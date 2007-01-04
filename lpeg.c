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

/* initial size for capture's list */
#define IMAXCAPTURES	600

/* maximum level of capture nesting */
#define MAXNEST		100


/* index, on Lua stack, for capture list */
#define CAPLISTIDX	3



typedef unsigned char byte;


#define CHARSETSIZE		((UCHAR_MAX/CHAR_BIT) + 1)


typedef byte Charset[CHARSETSIZE];


typedef const char *(*PattFunc) (void *ud, const char *s, const char *e);


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
    byte aux;
    short offset;
  } i;
  PattFunc f;
  byte buff[1];
} Instruction;


/* maximum size (in elements) for a pattern */
#define MAXPATTSIZE	((int)(SHRT_MAX/sizeof(Instruction)))

/* size (in elements) for an instruction plus extra l bytes */
#define instsize(l)	(((l) - 1)/sizeof(Instruction) + 2)


/* size (in elements) for a ICharset instruction */
#define CHARSETINSTSIZE		instsize(CHARSETSIZE)



#define loopset(v,b)	{ int v; for (v = 0; v < CHARSETSIZE; v++) b; }


#define testchar(st,c)	(((int)(st)[((c) >> 3)] & (1 << ((c) & 7))))
#define setchar(st,c)	((st)[(c) >> 3] |= (1 << ((c) & 7)))



static int sizei (Instruction *i) {
  switch(i->i.code) {
    case ICharset: return CHARSETINSTSIZE;
    case IFunc: return i->i.offset;
    default: return 1;
  }
}


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
  printf("%02d: %s ", p - op, names[p->i.code]);
  switch ((Opcode)p->i.code) {
    case IChar: {
      printf("'%c'", p->i.offset);
      break;
    }
    case ICapture: {
      const char *const modes[] = {"close", "position", "open", "table open"};
      printf("%s", modes[p->i.aux]);
      printf(" (%d)", p->i.offset);
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
    p += sizei(p);
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


static Capture *doublecap (lua_State *L, Capture *cap, int captop) {
  Capture *newc;
  if (captop >= INT_MAX/((int)sizeof(Capture) * 2))
    luaL_error(L, "too many captures");
  newc = (Capture *)lua_newuserdata(L, captop * 2 * sizeof(Capture));
  lua_replace(L, CAPLISTIDX);
  memcpy(newc, cap, captop * sizeof(Capture));
  return newc;
}


static const char *match (lua_State *L, const char *s, const char *e,
                          Instruction *op, Capture *capture) {
  Backtrack back[MAXBACK];
  Instruction *ret[MAXRET];
  int capsize = IMAXCAPTURES;
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
        if (s >= e) goto fail;
        s++;
        p++;
        continue;
      }
      case IChar: {
        if (s >= e || (byte)*s != (byte)p->i.offset)
          goto fail;
        s++;
        p++;
        continue;
      }
      case ICharset: {
        int c = (unsigned char)*s;
        if (s >= e || !testchar((p+1)->buff, c))
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
        const char *r = (p+1)->f((p+2)->buff, s, e);
        if (r == NULL)
          goto fail;
        s = r;
        p += p->i.offset;
        continue;
      }
      case ICall: {
        assert((p + 1)->i.code != IRet);  /* no tail call */
        if (rettop >= MAXRET) {
          luaL_error(L, "too many pending calls");
          return NULL;
        }
        ret[rettop++] = p + 1;
        p += p->i.offset;
        continue;
      }
      case ICommit: {
        assert(backtop > 0);
        backtop--;
        if (s <= back[backtop].s && p->i.offset <= 0) {
          luaL_error(L, "loop over empty pattern");
          return NULL;
        }
        p += p->i.offset;
        continue;
      }
      case IPartialCommit: {
        assert(backtop > 0 && back[backtop - 1].retlevel == rettop);
        if (s == back[backtop - 1].s && p->i.offset <= 0) {
          luaL_error(L, "infinite loop in pattern");
          return NULL;
        }
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
        if (captop >= capsize) {
          capture = doublecap(L, capture, captop);
          capsize = 2 * captop;
        }
        capture[captop].u1.p = p;
        capture[captop].u2.s = s;
        captop++;
        p++;
        continue;
      }
      case IEnd: {
        assert(rettop == 0 && backtop == 0);
        capture[captop].u2.s = NULL;
        return s;
      }
      case IOpenCall:
      default: assert(0); return NULL;
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


static int jointable (lua_State *L, int p1) {
  int n, n1, i;
  lua_getfenv(L, p1);
  lua_getfenv(L, -2);
  n1 = lua_objlen(L, -2);  /* number of elements in p1's env */
  n = lua_objlen(L, -1);  /* number of elements in p's env */
  for (i = 1; i <= n1; i++) {
    lua_rawgeti(L, -2, i);
    lua_rawseti(L, -2, n + i);
  }
  lua_pop(L, 2);
  return n;
}


#define copypatt(p1,p2,sz)	memcpy(p1, p2, (sz) * sizeof(Instruction));


static int addpatt (lua_State *L, Instruction *p, int p1idx) {
  Instruction *p1 = (Instruction *)lua_touserdata(L, p1idx);
  int sz = lua_objlen(L, p1idx)/sizeof(Instruction) - 1;
  int corr = jointable(L, p1idx);
  copypatt(p, p1, sz);
  if (corr != 0) {
    Instruction *px;
    for (px = p; px < p + sz; px += sizei(px)) {
      if (px->i.code == ICapture && px->i.offset != 0)
        px->i.offset += corr;
    }
  }
  return sz;
}


static void setinst (Instruction *i, Opcode op, int offset) {
  i->i.code = op;
  i->i.offset = offset;
}


static Instruction *newpatt (lua_State *L, size_t n) {
  Instruction *p;
  if (n >= MAXPATTSIZE - 1)
    luaL_error(L, "pattern too big");
  p = lua_newuserdata(L, (n + 1) * sizeof(Instruction));
  luaL_getmetatable(L, "pattern");
  lua_setmetatable(L, -2);
  setinst(p + n, IEnd, 0);
  lua_newtable(L);
  lua_setfenv(L, -2);  /* 'env' is a new table */
  return p;
}


static int tocharset (Instruction *p, Charset c) {
  loopset(i, c[i] = 0);
  if (p->i.code == IEnd || (p + sizei(p))->i.code != IEnd)
    return 0;  /* pattern does not have exactly 1 instruction */
  else switch (p[0].i.code) {
    case ICharset: {
      loopset(i, c[i] = p[1].buff[i]);
      return 1;
    }
    case IAny: {
      loopset(i, c[i] = 0xff);
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
  loopset(i, p[1].buff[i] = 0);
  return p[1].buff;
}


static int set_l (lua_State *L) {
  size_t l;
  const char *s = luaL_checklstring(L, 1, &l);
  byte *p = newcharset(L);
  while (l--) {
    setchar(p, (unsigned char)(*s));
    s++;
  }
  return 1;
}


static int range_l (lua_State *L) {
  int c;
  size_t fl, tl;
  const char *f = luaL_checklstring(L, 1, &fl);
  const char *t = luaL_checklstring(L, 2, &tl);
  byte *p = newcharset(L);
  luaL_argcheck(L, fl == 1, 1, "string must have a single character");
  luaL_argcheck(L, tl == 1, 2, "string must have a single character");
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
  setinst(p++, ICall, 2);
  setinst(p++, IJmp, totalsize - 1);
  for (i = 0; i < n; i++) {
    p += addpatt(L, p, -(n + 1 -i));
    setinst(p++, IRet, 0);
  }
  /* correct calls */
  p -= totalsize;  /* back to first position */
  for (i = 0; i < totalsize; i += sizei(p + i)) {
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
      size_t i, len;
      const char *s = lua_tolstring(L, idx, &len);
      p = newpatt(L, len);
      for (i = 0; i < len; i++)
        setinst(p + i, IChar, (unsigned char)s[i]);
      lua_replace(L, idx);
      break;
    }
    case LUA_TNUMBER: {
      int n = lua_tointeger(L, idx);
      if (n >= 0) {
        Instruction *p1 = p = newpatt(L, n);
        while (n--)
          setinst(p1++, IAny, 0);
      }
      else {
        int i;
        Instruction *p1 = p = newpatt(L, -n + 2);
        setinst(p1++, IChoice, -n + 2);
        for (i = 0; i < -n; i++)
          setinst(p1++, IAny, 0);
        setinst(p1, IFailTwice, -n + 2);
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


static int getpattl (lua_State *L, int idx) {
  int size;
  getpatt(L, idx, &size);
  return size;
}


static int literal_l (lua_State *L) {
  lua_settop(L, 1);
  getpatt(L, 1, NULL);
  return 1;
}


static int concat_l (lua_State *L) {
  /* p1; p2; */
  int l1 = getpattl(L, 1);
  int l2 = getpattl(L, 2);
  Instruction *p = newpatt(L, l1 + l2);
  p += addpatt(L, p, 1);
  addpatt(L, p, 2);
  return 1;
}


static int diff_l (lua_State *L) {
  int l1, l2;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p2 = getpatt(L, 2, &l2);
  Charset st1, st2;
  if (tocharset(p1, st1) && tocharset(p2, st2)) {
    byte *s = newcharset(L);
    loopset(i, s[i] = st1[i] & ~st2[i]);
  }
  else {
    /* !e2 . e1 */
    /* !e -> choice L1; e; failtwice; L1: ... */
    Instruction *p = newpatt(L, 1 + l2 + 1 + l1);
    setinst(p++, IChoice, 1 + l2 + 1);
    p += addpatt(L, p, 2);
    setinst(p++, IFailTwice, 0);
    addpatt(L, p, 1);
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
  int l1 = getpattl(L, 1);
  Instruction *p = newpatt(L, 1 + l1 + 2);
  setinst(p++, IChoice, 1 + l1 + 1);
  p += addpatt(L, p, 1);
  setinst(p++, IBackCommit, 2);
  setinst(p, IFail, 0);
  return 1;
}


static int union_l (lua_State *L) {
  int l1, l2;
  Instruction *p1 = getpatt(L, 1, &l1);
  Instruction *p2 = getpatt(L, 2, &l2);
  Charset st1, st2;
  if (tocharset(p1, st1) && tocharset(p2, st2)) {
    byte *s = newcharset(L);
    loopset(i, s[i] = st1[i] | st2[i]);
  }
  else {
    /* choice L1; e1; commit L2; L1: e2; L2: ... */
    Instruction *p = newpatt(L, 1 + l1 + 1 + l2);
    int comm;
    while (p1[0].i.code == IChoice &&
          p1[comm = p1[0].i.offset - 1].i.code == ICommit &&
          p1[comm].i.offset + comm == l1) {
      copypatt(p, p1, comm); p += comm;
      setinst(p++, ICommit, (l1 - comm) + 2 + l2);
      p1 += comm + 1;
      l1 -= comm + 1;
    }
    jointable(L, 1);
    setinst(p++, IChoice, 1 + l1 + 1);
    copypatt(p, p1, l1); p += l1;
    setinst(p++, ICommit, 1 + l2);
    addpatt(L, p, 2);
  }
  return 1;
}


static int star_l (lua_State *L) {
  /* e; ...; e; choice L1; L2: e; partialcommit L2; L1: ... */
  /* choice L1; e; partialcommit L2; L2: ... e; L1: commit L3; L3: ... */
  int i;
  int l1 = getpattl(L, 1);
  int n = luaL_checkint(L, 2);
  if (n >= 0) {
    Instruction *p = newpatt(L, (n + 1)*l1 + 2);
    for (i = 0; i < n; i++) {
      p += addpatt(L, p, 1);
    }
    setinst(p++, IChoice, 1 + l1 + 1);
    p += addpatt(L, p, 1);
    setinst(p, IPartialCommit, -l1);
  }
  else {
    Instruction *p = newpatt(L, -n*(l1 + 1) + 1);
    setinst(p++, IChoice, 1 + -n*(l1 + 1));
    for (i = 0; i < -n; i++) {
      p += addpatt(L, p, 1);
      setinst(p++, IPartialCommit, 1);
    }
    setinst(p - 1, ICommit, 1);  /* correct last commit */
  }
  return 1;
}


static Instruction *newcap (lua_State *L, int labelidx, int extrasize) {
  int ref = (lua_isnoneornil(L, labelidx)) ? 0 : 1;
  Instruction *p = newpatt(L, 1 + extrasize);
  p->i.code = ICapture;
  p->i.offset = ref;
  if (ref) {
    lua_getfenv(L, -1);
    lua_pushvalue(L, labelidx);
    lua_rawseti(L, -2, 1);
    lua_pop(L, 1);
  }
  return p;
}


static int capture_aux (lua_State *L, int kind) {
  int l1 = getpattl(L, 1);
  Instruction *p = newcap(L, 2, l1 + 1);
  p->i.aux = kind;
  p++;
  p += addpatt(L, p, 1);
  setinst(p, ICapture, 0);
  p->i.aux = Cclose;
  return 1;
}


static int capture_l (lua_State *L) { return capture_aux(L, Copen); }
static int tcapture_l (lua_State *L) { return capture_aux(L, CTopen); }


static int position_l (lua_State *L) {
  Instruction *p = newcap(L, 1, 0);
  p->i.aux = Cposition;
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
  p[0].i.offset = n;
  p[1].f = f;
  memcpy(p[2].buff, ud, l);
}


static const char *utf_a (void *ud, const char *s, const char *e) {
  wctype_t tp = *(wctype_t *)ud;
  wint_t c;
  if (*(unsigned char *)s < 0x80)
    c = *s++;
  else if (*(unsigned char *)s < 0xC0 || (*(s+1) & 0xC0) != 0x80)
    return NULL;
  else if (*(unsigned char *)s < 0xE0) {
    c = (*s & 0x1F << 6) | (*(s + 1) & 0x3F);
    s += 2;
  }
  else if ((*(s+2) & 0xC0) != 0x80)
    return NULL;
  else if (*(unsigned char *)s < 0xF0) {
    c = (((*s & 0x0F << 6) | (*(s + 1) & 0x3F)) << 6) | (*(s + 2) & 0x3F);
    s += 3;
  }
  else if ((*(s+3) & 0xC0) != 0x80)
    return NULL;
  else if (*(unsigned char *)s < 0xF8) {
    c = (((((*s & 0x07 << 6) | (*(s + 1) & 0x3F)) << 6) |
                              (*(s + 2) & 0x3F)) << 6) | (*(s + 3) & 0x3F);
    s += 4;
  }
  else return NULL;
  if (s > e || (tp != 0 && !iswctype(c, tp)))
    return NULL;
  else
    return s;
}


static int utf8_l (lua_State *L) {
  const char *s = luaL_optstring(L, 1, NULL);
  wctype_t tp;
  if (s == NULL)
    tp = 0;
  else {
    tp = wctype(s);
    luaL_argcheck(L, tp != 0, 1, "invalid property name");
  }
  newpattfunc(L, utf_a, &tp, sizeof(tp));
  return 1;
}

/* }====================================================== */



static int printpat_l (lua_State *L) {
  Instruction *p = getpatt(L, 1, NULL);
  int n, i;
  lua_getfenv(L, 1);
  n = lua_objlen(L, -1);
  printf("[");
  for (i = 1; i <= n; i++) {
    printf("%d = ", i);
    lua_rawgeti(L, -1, i);
    if (lua_isstring(L, -1))
      printf("%s  ", lua_tostring(L, -1));
    else
      printf("%s  ", lua_typename(L, lua_type(L, -1)));
    lua_pop(L, 1);
  }
  printf("]\n");
  printpatt(p);
  return 0;
}


static Capture *pushcapture (lua_State *L, const char *s, Capture *cap) {
  switch (cap->u1.p->i.aux) {
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
          if (it->i.offset == 0)
            lua_pushinteger(L, n++);
          else
            lua_rawgeti(L, CAPLISTIDX + 1, it->i.offset);
          c = pushcapture(L, s, c);
          lua_settable(L, -3);
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
    switch (cap->u1.p->i.aux) {
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
    if (it->i.offset != 0) {  /* does have a label? */
      lua_rawgeti(L, CAPLISTIDX + 1, it->i.offset);
      n++;
    }
    cap = pushcapture(L, s, cap);
    n++;
  }
  return n;
}


static int matchl (lua_State *L) {
  Capture capture[IMAXCAPTURES];
  const char *r;
  int n;
  size_t l;
  const char *s = luaL_checklstring(L, 1, &l);
  Instruction *p = getpatt(L, 2, NULL);
  lua_Integer i = luaL_optinteger(L, 3, 1);
  i = (i > 0) ?
        ((i <= (lua_Integer)l) ? i - 1 : (lua_Integer)l) :
        (((lua_Integer)l + i >= 0) ? (lua_Integer)l + i : 0);
  lua_settop(L, CAPLISTIDX - 1);
  lua_pushlightuserdata(L, capture);
  r = match(L, s + i, s + l, p, capture);
  if (r == NULL) {
    lua_pushboolean(L, 0);
    return 1;
  }
  lua_getfenv(L, 2);
  n = getcaptures(L, s, (Capture *)lua_touserdata(L, CAPLISTIDX));
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

