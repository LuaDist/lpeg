/*
   PEG rules:

   e1 | e2 -> choice L1; e1; commit L2; L1: e2; L2:
   e*      -> L2: choice L1; e; commit L2; L1:
   or e*      -> choice L1; L2: e; partialcommit L2; L1:
   e?      -> choice L1; e; commit L1; L1:
   !e      -> choice L1; e; commit L2; L2: fail; L1:
   or !e     -> choice L1; e; failtwice; L1:
   &e      -> choice L1; choice L2; e; L2: commit L3; L3: fail; L1:
   or &e     -> choice L1; e; backcommit L2; L1: fail; L2:
*/


#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <wctype.h>

#include "lua.h"
#include "lauxlib.h"


/* maximum rules in a grammar */
#define MAXRULES	100

/* maximum backtrack levels */
#define MAXBACK		100

/* maximum call levels */
#define MAXRET		100

/* maximum captures */
#define MAXCAPTURES	1000

/* maximum level of capture nesting */
#define MAXNEST		40



typedef unsigned char byte;


#define CHARSETSIZE		((UCHAR_MAX/CHAR_BIT) + 1)


typedef byte Charset[CHARSETSIZE];


typedef const char *(*PattFunc) (void *ud, const char *s);


/* kinds of captures */
#define Cclose		0
#define Cposition	1
#define Copen		2
#define CTopen		3	/* table capture */


typedef enum Opcode {
  IRet=0, IChoice, IAny, IChar, ICharset, IJmp, ICall, IOpenCall, IFunc,
  ICommit, IPartialCommit, IBackCommit, IFailTwice, IFail,
  ICapture, IEnd
} Opcode;


typedef union Instruction {
  struct Inst {
    byte code;
    byte size;
    short offset;
  } i;
  PattFunc f;
  byte buff[1];
  char s[1];
} Instruction;


/* maximum size (in elements) for a pattern */
#define MAXPATTSIZE	((int)(SHRT_MAX/sizeof(Instruction)))

/* size (in elements) for an instruction plus extra l bytes */
#define instsize(l)	(((l) - 1)/sizeof(Instruction) + 2)


/* size (in elements) for a ICharset instruction */
#define CHARSETINSTSIZE		instsize(CHARSETSIZE)



#define loopset(b)	{ int i; for (i = 0; i < CHARSETSIZE; i++) b; }


#define testchar(st,c)	(((int)(st)[((c) >> 3)] & (1 << ((c) & 7))))
#define setchar(st,c)	((st)[(c) >> 3] |= (1 << ((c) & 7)))



/*
** {======================================================
** Printing patterns
** =======================================================
*/


static void printcharset (Charset st) {
  int i;
  printf("[");
  for (i = 0; i <= UCHAR_MAX; i++) {
    int first = i;
    while (testchar(st, i) && i <= UCHAR_MAX) i++;
    if (i - 1 == first)
      printf("(%02x)", first);
    else if (i - 1 > first)
      printf("(%02x-%02x)", first, i - 1);
  }
  printf("]");
}

static void printinst (Instruction *op, Instruction *p) {
  const char *const names[] = {
    "ret", "choice", "any", "char", "charset", "jmp",
    "call", "open_call", "func",
    "commit", "partial_commit", "back_commit", "failtwice", "fail",
    "capture", "end"
  };
  printf("%02d: %s (%d) ", p - op, names[p->i.code], p->i.size);
  switch ((Opcode)p->i.code) {
    case IChar: {
      printf("'%c'", p->i.offset);
      break;
    }
    case ICapture: {
      const char *const modes[] = {"close", "position", "open", "table open"};
      printf("%s", modes[p->i.offset]);
      if (p->i.offset != Cclose && (p + 1)->s[0] != '\0')
        printf(" (%s)", (p + 1)->s);
      break;
    }
    case ICharset: {
      printcharset((p+1)->buff);
      break;
    }
    case IOpenCall: {
      printf("-> %d", p->i.offset);
      break;
    }
    case IJmp: case ICall: case IChoice: case ICommit:
    case IPartialCommit: case IBackCommit: {
      printf("-> %d", p + p->i.offset - op);
      break;
    }
    default: break;
  }
  printf("\n");
}


static void printpatt (Instruction *p) {
  Instruction *op = p;
  for (;;) {
    printinst(op, p);
    if (p->i.code == IEnd) break;
    assert(p->i.size > 0);
    p += p->i.size;
  }
}

/* }====================================================== */




/*
** {======================================================
** Virtual Machine
** =======================================================
*/

typedef struct Capture {
  union {
    Instruction *p;  /* corresponding instruction */
    const char *s;  /* open position (when pushing strings) */
  } u1;
  union {
    const char *s;  /* position */
    struct Capture *cap;  /* closing pair (when pushing strings) */
  } u2;
} Capture;


typedef struct Backtrack {
  const char *s;
  Instruction *p;
  int retlevel;
  int caplevel;
} Backtrack;


static const char *match (lua_State *L, const char *s, Instruction *op,
                          Capture *capture) {
  Backtrack back[MAXBACK];
  Instruction *ret[MAXRET];
  int backtop = 0;  /* point to first empty slot in back */
  int rettop = 0;  /* point to first empty slot in ret */
  int captop = 0;  /* point to first empty slot in captures */
  Instruction *p = op;
  for (;;) {
#if defined(DEBUG)
      printf("s: |%s| b: %d r: %d c: %d  ", s, backtop, rettop, captop);
      printinst(op, p);
#endif
    switch ((Opcode)p->i.code) {
      case IRet: {
        assert(rettop > 0);
        p = ret[--rettop];
        continue;
      }
      case IAny: {
        if (*s == '\0') goto fail;
        s++;
        p++;
        continue;
      }
      case IChar: {
        if ((unsigned char)*s != p->i.offset)
          goto fail;
        s++;
        p++;
        continue;
      }
      case ICharset: {
        int c = (unsigned char)*s;
        if (!testchar((p+1)->buff, c))
          goto fail;
        s++;
        p += CHARSETINSTSIZE;
        continue;
      }
      case IJmp: {
        p += p->i.offset;
        continue;
      }
      case IChoice: {
        if (backtop >= MAXBACK) {
          luaL_error(L, "too many pending choices");
          return NULL;
        }
        back[backtop].p = p + p->i.offset;
        back[backtop].s = s;
        back[backtop].caplevel = captop;
        back[backtop++].retlevel = rettop;
        p++;
        continue;
      }
      case IFunc: {
        const char *r = (p+1)->f((p+2)->buff, s);
        if (r == NULL)
          goto fail;
        s = r;
        p += p->i.size;
        continue;
      }
      case ICall: {
        assert((p + 1)->i.code != IRet);  /* no tail call */
        if (rettop >= MAXRET) {
          luaL_error(L, "too many pending calls");
          return NULL;
        }
        ret[rettop++] = p + p->i.size;
        p += p->i.offset;
        continue;
      }
      case ICommit: {
        backtop--;
        p += p->i.offset;
        continue;
      }
      case IPartialCommit: {
        assert(backtop > 0 && back[backtop - 1].retlevel == rettop);
        back[backtop - 1].s = s;
        back[backtop - 1].caplevel = captop;
        p += p->i.offset;
        continue;
      }
      case IBackCommit: {
        assert(backtop > 0);
        back[backtop - 1].p = p + p->i.offset;  /* "fail" to this address */
        goto fail;
      }
      case IFailTwice:
        assert(backtop > 0);
        backtop--;
        /* go through */
      fail:  /* pattern failed: try to backtrack */
      case IFail: {
#if defined(DEBUG)
          printf("FAILED (%s) b: %d %d\n", s, backtop, rettop);
#endif
        if (backtop == 0)
          return NULL;  /* no more backtracking */
        backtop--;
        rettop = back[backtop].retlevel;
        captop = back[backtop].caplevel;
        s = back[backtop].s;
        p = back[backtop].p;
        continue;
      }
      case ICapture: {
        if (captop >= MAXCAPTURES) {
          luaL_error(L, "too many captures");
          return NULL;
        }
        capture[captop].u1.p = p;
        capture[captop].u2.s = s;
        captop++;
        p += p->i.size;
        continue;
      }
      case IEnd: {
        assert(rettop == 0 && backtop == 0);
        capture[captop].u2.s = NULL;
        return s;
      }
      case IOpenCall:
      default: assert(0);
    }
  }
}

/* }====================================================== */



/*
** {======================================================
** Building Patterns
** =======================================================
*/


#define checkpattern(L, idx) ((Instruction *)luaL_checkudata(L, idx, "pattern"))

#define addpatt(p1, p2, sz)	memcpy((p1), p2, (sz) * sizeof(Instruction))


static void setinst (Instruction *i, Opcode op, int offset) {
  i->i.code = op;
  i->i.size = 1;
  i->i.offset = offset;
}


static void strtocharset (const char *s, Charset p) {
  loopset(p[i] = 0);
  for (; *s; s++)
    setchar(p, (unsigned char)(*s));
}


static Instruction *newpatt (lua_State *L, size_t n) {
  Instruction *p;
  if (n >= MAXPATTSIZE - 1)
    luaL_error(L, "pattern too big");
  p = lua_newuserdata(L, (n + 1) * sizeof(Instruction));
  luaL_getmetatable(L, "pattern");
  lua_setmetatable(L, -2);
  setinst(p + n, IEnd, 0);
  return p;
}


static int tocharset (Instruction *p, Charset c) {
  loopset(c[i] = 0);
  if (p[0].i.code == IEnd || p[p[0].i.size].i.code != IEnd)
    return 0;  /* pattern does not have exactly 1 instruction */
  else switch (p[0].i.code) {
    case ICharset: {
      loopset(c[i] = p[1].buff[i]);
      return 1;
    }
    case IAny: {
      loopset(c[i] = 0xff);
      c[0] = 0xfe;  /* reset '\0' */
      return 1;
    }
    case IChar: {
      setchar(c, p[0].i.offset);
      return 1;
    }
    default: return 0;
  }
}


static byte *newcharset (lua_State *L) {
  Instruction *p = newpatt(L, CHARSETINSTSIZE);
  p[0].i.code = ICharset;
  p[0].i.size = CHARSETINSTSIZE;
  return p[1].buff;
}


static int set_l (lua_State *L) {
  const char *s = luaL_checkstring(L, 1);
  byte *p = newcharset(L);
  strtocharset(s, p);
  return 1;
}


static int range_l (lua_State *L) {
  int c;
  const char *f = luaL_checkstring(L, 1);
  const char *t = luaL_checkstring(L, 2);
  byte *p = newcharset(L);
  luaL_argcheck(L, strlen(f) == 1, 1, "string must have a single character");
  luaL_argcheck(L, strlen(t) == 1, 2, "string must have a single character");
  loopset(p[i] = 0);
  for (c = (byte)*f; c <= (byte)*t; c++)
    setchar(p, c);
  return 1;
}


static int nter_l (lua_State *L) {
  int i = luaL_checkinteger(L, 1);
  Instruction *p = newpatt(L, 1);
  luaL_argcheck(L, i >= 1, 1, "invalid rule reference");
  setinst(p, IOpenCall, i);
  return 1;
}



static Instruction *getfield (lua_State *L, int *size) {
  Instruction *p = (Instruction *)lua_touserdata(L, -1);
  *size = lua_objlen(L, -1) / sizeof(Instruction);
  if (p != NULL) {  /* value is a userdata? */
    if (lua_getmetatable(L, -1)) {  /* does it have a metatable? */
      lua_getfield(L, LUA_REGISTRYINDEX, "pattern");
      if (lua_rawequal(L, -1, -2)) {  /* does it have the correct mt? */
        lua_pop(L, 2);  /* remove both metatables */
        return p;
      } 
    }
  } 
  luaL_error(L, "invalid field in grammar");
  return NULL;  /* to avoid warnings */
}


static Instruction *fix_l (lua_State *L, int t) {
  Instruction *p;
  int pos[MAXRULES + 1];
  int i, totalsize;
  const int n = lua_objlen(L, t);
  luaL_argcheck(L, n <= MAXRULES, t, "grammar has too many rules");
  luaL_argcheck(L, n > 0, t, "empty grammar");
  luaL_checkstack(L, n, "grammar has too many rules");
  /* collect patterns and compute sizes */
  totalsize = 2;  /* initial call and jmp */
  for (i = 0; i < n; i++) {
    int l;
    lua_rawgeti(L, t, i + 1);
    getfield(L, &l);
    if (totalsize >= MAXPATTSIZE - l)
      luaL_error(L, "grammar too large");
    pos[i] = totalsize;
    totalsize += l;
  }
  pos[n] = totalsize;
  /* create new pattern */
  p = newpatt(L, totalsize);
  setinst(p, ICall, 2);
  setinst(p + 1, IJmp, totalsize - 1);
  for (i = 0; i < n; i++) {
    Instruction *p1 = (Instruction *)lua_touserdata(L, -(n + 1 - i));
    addpatt(p + pos[i], p1, (pos[i + 1] - 1) - pos[i]);
    setinst(p + pos[i + 1] - 1, IRet, 0);
  }
  /* correct calls */
  for (i = 0; i < totalsize; i += p[i].i.size) {
    if (p[i].i.code == IOpenCall) {
      int r = p[i].i.offset;
      if (r > n)
        luaL_error(L, "reference to non-existent non-terminal %d", r);
      p[i].i.code = (p[i + 1].i.code == IRet) ? IJmp : ICall;
      p[i].i.offset = pos[r - 1] - i;
    }
    assert(p[i].i.code != ICall || (p[i + 1].i.code != IRet &&
                                    p[i + 1].i.code != IEnd));
  }
  lua_replace(L, t);  /* put new pattern in old's position */
  lua_pop(L, n);  /* remove rules */
  return p;
}


static Instruction *getpatt (lua_State *L, int idx, int *size) {
  Instruction *p;
  switch (lua_type(L, idx)) {
    case LUA_TSTRING: {
      unsigned int i;
      const char *s = lua_tostring(L, idx);
      size_t len = strlen(s);
      p = newpatt(L, len);
      for (i = 0; i < len; i++) {
        setinst(p + i, IChar, (unsigned char)s[i]);
      }
      lua_replace(L, idx);
      break;
    }
    case LUA_TNUMBER: {
      const int n = lua_tointeger(L, idx);
      if (n >= 0) {
        int i;
        p = newpatt(L, n);
        for (i = 0; i < n; i++)
          setinst(p + i, IAny, 0);
      }
      else {
        int i;
        p = newpatt(L, -n + 2);
        setinst(p, IChoice, -n + 2);
        for (i = 0; i < -n; i++)
          setinst(p + 1 + i, IAny, 0);
        setinst(p + 1 + -n, IFailTwice, -n + 2);
      }
      lua_replace(L, idx);
      break;
    }
    case LUA_TTABLE: {
      p = fix_l(L, idx);
      break;
    }
    default: {
      p = checkpattern(L, idx);
      break;
    }
  }
  if (size) *size = lua_objlen(L, idx)/sizeof(Instruction) - 1;
  return p;
}


static int literal_l (lua_State *L) {
  lua_settop(L, 1);
  getpatt(L, 1, NULL);
  return 1;
}


static int concat_l (lua_State *L) {
  /* p1; p2; */
  int l1, l2;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p2 = getpatt(L, 2, &l2);
  Instruction *p = newpatt(L, l1 + l2);
  addpatt(p, p1, l1);
  addpatt(p + l1, p2, l2);
  return 1;
}


static int diff_l (lua_State *L) {
  int l1, l2;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p2 = getpatt(L, 2, &l2);
  Charset st1, st2;
  if (tocharset(p1, st1) && tocharset(p2, st2)) {
    byte *s = newcharset(L);
    loopset(s[i] = st1[i] & ~st2[i]);
  }
  else {
    /* !e2 . e1 */
    /* !e -> choice L1; e; failtwice; L1: ... */
    Instruction *p = newpatt(L, 1 + l2 + 1 + l1);
    setinst(p, IChoice, 1 + l2 + 1);
    addpatt(p + 1, p2, l2);
    setinst(p + 1 + l2, IFailTwice, 0);
    addpatt(p + 1 + l2 + 1, p1, l1);
  }
  return 1;
}


static int unm_l (lua_State *L) {
  lua_pushliteral(L, "");
  lua_insert(L, 1);
  return diff_l(L);
}


static int pattand_l (lua_State *L) {
  /* &e -> choice L1; e; backcommit L2; L1: fail; L2: ... */
  int l1;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p = newpatt(L, 1 + l1 + 2);
  setinst(p, IChoice, 1 + l1 + 1);
  addpatt(p + 1, p1, l1);
  setinst(p + 1 + l1, IBackCommit, 2);
  setinst(p + 1 + l1 + 1, IFail, 0);
  return 1;
}


static int union_l (lua_State *L) {
  int l1, l2;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p2 = getpatt(L, 2, &l2);
  Charset st1, st2;
  if (tocharset(p1, st1) && tocharset(p2, st2)) {
    byte *s = newcharset(L);
    loopset(s[i] = st1[i] | st2[i]);
  }
  else {
    /* choice L1; e1; commit L2; L1: e2; L2: ... */
    Instruction *p = newpatt(L, 1 + l1 + 1 + l2);
    setinst(p, IChoice, 1 + l1 + 1);
    addpatt(p + 1, p1, l1);
    setinst(p + 1 + l1, ICommit, 1 + l2);
    addpatt(p + 1 + l1 + 1, p2, l2);
  }
  return 1;
}


static int star_l (lua_State *L) {
  /* e; ...; e; choice L1; L2: e; partialcommit L2; L1: ... */
  /* choice L1; e; partialcommit L2; L2: ... e; L1: commit L3; L3: ... */
  int l1, i;
  Instruction *p1 = getpatt(L, 1, &l1);
  int n = luaL_checkint(L, 2);
  if (n >= 0) {
    Instruction *p = newpatt(L, (n + 1)*l1 + 2);
    for (i = 0; i < n; i++)
      addpatt(p + (i * l1), p1, l1);
    p += n * l1;
    setinst(p, IChoice, 1 + l1 + 1);
    addpatt(p + 1, p1, l1);
    setinst(p + 1 + l1, IPartialCommit, -l1);
  }
  else {
    Instruction *p = newpatt(L, -n*(l1 + 1) + 1);
    setinst(p++, IChoice, 1 + -n*(l1 + 1));
    for (i = 0; i < -n; i++) {
      addpatt(p, p1, l1);
      p += l1;
      setinst(p++, IPartialCommit, 1);
    }
    setinst(p - 1, ICommit, 1);
  }
  return 1;
}


static Instruction *newcap (lua_State *L, int nameidx, int extrasize) {
  const char *name = luaL_optstring(L, nameidx, "");
  int size = instsize(strlen(name) + 1);
  Instruction *p = newpatt(L, size + extrasize);
  p->i.code = ICapture;
  p->i.size = size;
  strcpy((p + 1)->s, name);
  return p;
}


static int capture_aux (lua_State *L, int kind) {
  int l1;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p = newcap(L, 2, l1 + 1);
  p->i.offset = kind;
  p += p->i.size;
  addpatt(p, p1, l1);
  setinst(p + l1, ICapture, Cclose);
  return 1;
}


static int capture_l (lua_State *L) { return capture_aux(L, Copen); }
static int tcapture_l (lua_State *L) { return capture_aux(L, CTopen); }


static int position_l (lua_State *L) {
  Instruction *p = newcap(L, 1, 0);
  p->i.offset = Cposition;
  return 1;
}

/* }====================================================== */



/*
** {======================================================
** User-Defined Patterns
** =======================================================
*/

static void newpattfunc (lua_State *L, PattFunc f, void *ud, size_t l) {
  int n = instsize(l) + 1;
  Instruction *p = newpatt(L, n);
  p[0].i.code = IFunc;
  p[0].i.size = n;
  p[1].f = f;
  memcpy(p[2].buff, ud, l);
}


static const char *utf_a (void *ud, const char *s) {
  wctype_t tp = *(wctype_t *)ud;
  wint_t c;
  if ((*s & 0x80) == 0x00)
    c = *s++;
  else if ((*s & 0xC0) == 0x80 || (*(s+1) & 0xC0) != 0x80)
    return NULL;
  else if ((*s & 0xE0) == 0xC0) {
    c = (*s & 0x1F << 6) | (*(s + 1) & 0x3F);
    s += 2;
  }
  else if ((*(s+2) & 0xC0) != 0x80)
    return NULL;
  else if ((*s & 0xF0) == 0xE0) {
    c = (((*s & 0x0F << 6) | (*(s + 1) & 0x3F)) << 6) | (*(s + 2) & 0x3F);
    s += 3;
  }
  else if ((*(s+3) & 0xC0) != 0x80)
    return NULL;
  else if ((*s & 0xF8) == 0xF0) {
    c = (((((*s & 0x07 << 6) | (*(s + 1) & 0x3F)) << 6) |
                              (*(s + 2) & 0x3F)) << 6) | (*(s + 3) & 0x3F);
    s += 4;
  }
  else return NULL;
  if (!iswctype(c, tp))
    return NULL;
  else
    return s;
}


static int utf8_l (lua_State *L) {
  const char *s = luaL_checkstring(L, 1);
  wctype_t tp = wctype(s);
  luaL_argcheck(L, tp != 0, 1, "invalid property name");
  newpattfunc(L, utf_a, &tp, sizeof(tp));
  return 1;
}

/* }====================================================== */



static int printpat_l (lua_State *L) {
  Instruction *p = getpatt(L, 1, NULL);
  printpatt(p);
  return 0;
}


#define capname(it)	(((it) + 1)->s)


static Capture *pushcapture (lua_State *L, const char *s, Capture *cap) {
  switch (cap->u1.p->i.offset) {
    case Cposition: {
      lua_pushinteger(L, cap->u2.s - s + 1);
      return cap;
    }
    case Copen: {
      Capture *close = cap->u2.cap;
      lua_pushlstring(L, close->u1.s, close->u2.s - close->u1.s);
      close->u1.p = NULL;
      return cap;
    }
    case CTopen: {
      int n = 1;
      Capture *close = cap->u2.cap;
      Capture *c;
      luaL_checkstack(L, 1, "capture's nest too deep");
      lua_newtable(L);
      for (c = cap + 1; c < close; c++) {
        Instruction *it = c->u1.p;
        if (it == NULL) continue;  /* nested close */
        else {
          c = pushcapture(L, s, c);
          if (*capname(it) != '\0')
            lua_setfield(L, -2, capname(it));
          else
            lua_rawseti(L, -2, n++);
        }
      }
      return c;
    }
    default: assert(0); return NULL;
  }
}


static int getcaptures (lua_State *L, const char *s, Capture *capture) {
  Capture *stack[MAXNEST];
  Capture *cap;
  int n = 0;
  /* match open/close pairs */
  for (cap = capture; cap->u2.s != NULL; cap++) {
    assert(cap->u1.p->i.code == ICapture);
    switch (cap->u1.p->i.offset) {
      case Copen:  case CTopen: {
        if (n >= MAXNEST) luaL_error(L, "too deep capture nesting");
        stack[n++] = cap;
        break;
      }
      case Cclose: {
        Capture *open = stack[--n];
        cap->u1.s = open->u2.s;  /* save open position */
        open->u2.cap = cap;
        break;
      }
      case Cposition: break;
      default: assert(0);
    }
  }
  /* push results */
  n = 0;
  for (cap = capture; cap->u2.s != NULL; cap++) {
    Instruction *it = cap->u1.p;
    if (it == NULL) continue;  /* close capture */
    luaL_checkstack(L, 4, "too many captures");
    if (*capname(it) != '\0') {  /* does have a name? */
      lua_pushstring(L, capname(it));
      n++;
    }
    cap = pushcapture(L, s, cap);
    n++;
  }
  return n;
}


static int matchl (lua_State *L) {
  Capture capture[MAXCAPTURES];
  int n;
  const char *s = luaL_checkstring(L, 1);
  Instruction *p = getpatt(L, 2, NULL);
  const char *r = match(L, s, p, capture);
  if (r == NULL) {
    lua_pushboolean(L, 0);
    return 1;
  }
  n = getcaptures(L, s, capture);
  if (n == 0) {  /* no captures? */
    lua_pushinteger(L, r - s + 1);
    n = 1;
  }
  return n;
}



static struct luaL_reg pattreg[] = {
  {"match", matchl},
  {"print", printpat_l},
  {"C", capture_l},
  {"I", position_l},
  {"P", literal_l},
  {"R", range_l},
  {"S", set_l},
  {"T", tcapture_l},
  {"V", nter_l},
  {"utf8", utf8_l},
  {NULL, NULL}
};


static struct luaL_reg metapattreg[] = {
  {"__add", union_l},
  {"__pow", star_l},
  {"__sub", diff_l},
  {"__mul", concat_l},
  {"__unm", unm_l},
  {"__len", pattand_l},
  {NULL, NULL}
};


int luaopen_lpeg (lua_State *L);
int luaopen_lpeg (lua_State *L) {
  luaL_newmetatable(L, "pattern");
  luaL_register(L, NULL, metapattreg);
  luaL_register(L, "lpeg", pattreg);
  lua_pushliteral(L, "__index");
  lua_pushvalue(L, -2);
  lua_settable(L, -4);
  return 1;
}

