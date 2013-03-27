/*
** $Id: lpcode.c,v 1.10 2013/03/27 15:49:17 roberto Exp $
** Copyright 2007, Lua.org & PUC-Rio  (see 'lpeg.html' for license)
*/

#include "lua.h"
#include "lauxlib.h"

#include "lptypes.h"
#include "lpcode.h"


/* signals a "no-instruction */
#define NOINST		-1


static const Charset fullset =
  {0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF,
   0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF};

/*
** {======================================================
** Analysis and some optimizations
** =======================================================
*/

/*
** Check whether a charset is empty (IFail), singleton (IChar),
** full (IAny), or none of those (ISet).
*/
static int charsettype (const Charset cs, int *c) {
  int count = 0;
  int i;
  int candidate = -1;  /* candidate position for a char */
  for (i = 0; i < CHARSETSIZE; i++) {
    int b = cs[i];
    if (b == 0) {
      if (count > 1) return ISet;  /* else set is still empty */
    }
    else if (b == 0xFF) {
      if (count < (i * BITSPERCHAR))
        return ISet;
      else count += BITSPERCHAR;  /* set is still full */
    }
    else if ((b & (b - 1)) == 0) {  /* byte has only one bit? */
      if (count > 0)
        return ISet;  /* set is neither full nor empty */
      else {  /* set has only one char till now; track it */
        count++;
        candidate = i;
      }
    }
    else return ISet;  /* byte is neither empty, full, nor singleton */
  }
  switch (count) {
    case 0: return IFail;  /* empty set */
    case 1: {  /* singleton; find character bit inside byte */
      int b = cs[candidate];
      *c = candidate * BITSPERCHAR;
      if ((b & 0xF0) != 0) { *c += 4; b >>= 4; }
      if ((b & 0x0C) != 0) { *c += 2; b >>= 2; }
      if ((b & 0x02) != 0) { *c += 1; }
      return IChar;
    }
    case (CHARSETSIZE * BITSPERCHAR): return IAny;  /* full set */
    default: assert(0); return 0;  /* should have returned by now */
  }
}

/*
** A few basic operations on Charsets
*/
static void cs_complement (Charset cs) {
  loopset(i, cs[i] = ~cs[i]);
}


static int cs_equal (const Charset cs1, const Charset cs2) {
  loopset(i, if (cs1[i] != cs2[i]) return 0);
  return 1;
}


/*
** computes whether sets st1 and st2 are disjoint
*/
static int cs_disjoint (const Charset st1, const Charset st2) {
  loopset(i, if ((st1[i] & st2[i]) != 0) return 0;)
  return 1;
}


/*
** Convert a 'char' pattern (TSet, TChar, TAny) to a charset
*/
int tocharset (TTree *tree, byte *cs) {
  switch (tree->tag) {
    case TSet: {  /* copy set */
      loopset(i, cs[i] = treebuffer(tree)[i]);
      return 1;
    }
    case TChar: {  /* only one char */
      loopset(i, cs[i] = 0);  /* erase all chars */
      setchar(cs, tree->u.n);  /* add that one */
      return 1;
    }
    case TAny: {
      loopset(i, cs[i] = 0xFF);  /* add all to the set */
      return 1;
    }
    default: return 0;
  }
}


/*
** checks whether a pattern has captures
*/
int hascaptures (TTree *tree) {
 tailcall:
  switch (tree->tag) {
    case TCapture: case TRunTime:
      return 1;
    default: {
      switch (numsiblings[tree->tag]) {
        case 0: return 0;
        case 1:  /* return hascaptures(sib1(tree)); */
          tree = sib1(tree); goto tailcall;
        case 2:
          if (hascaptures(sib1(tree))) return 1;
          /* else return hascaptures(sib2(tree)); */
          tree = sib2(tree); goto tailcall;
        default: assert(0); return 0;
      }
    }
  }
}


/*
** Checks how a pattern behaves regarding the empty string,
** in one of two different ways:
** A pattern is *nullable* if it can match without consuming any character;
** A pattern is *nofail* if it never fails for any string
** (including the empty string).
** The difference is only for predicates; for patterns without
** predicates, the two properties are equivalent.
** (With predicates, &'a' is nullable but not nofail. Of course,
** nofail => nullable.)
** These functions are all convervative in the following way:
** p is nullable => nullable(p)
** nofail(p) => p cannot fail
** (The function assumes that TOpenCall and TRunTime are not nullable:
** TOpenCall must be checked again when the grammar is fixed;
** TRunTime is an arbitrary choice.)
*/
int checkaux (TTree *tree, int pred) {
 tailcall:
  switch (tree->tag) {
    case TChar: case TSet: case TAny:
    case TFalse: case TOpenCall: case TRunTime:
      return 0;  /* not nullable */
    case TRep: case TTrue:
      return 1;  /* no fail */
    case TNot: case TBehind:
      /* can match empty, but may fail */
      if (pred == PEnofail) return 0;
      else return 1;  /* PEnullable */
    case TAnd:
      /* can match empty; fail iff body does */
      if (pred == PEnullable) return 1;
      /* else return checkaux(sib1(tree), pred); */
      tree = sib1(tree); goto tailcall;
    case TSeq:
      if (!checkaux(sib1(tree), pred)) return 0;
      /* else return checkaux(sib2(tree), pred); */
      tree = sib2(tree); goto tailcall;
    case TChoice:
      if (checkaux(sib2(tree), pred)) return 1;
      /* else return checkaux(sib1(tree), pred); */
      tree = sib1(tree); goto tailcall;
    case TCapture: case TGrammar: case TRule:
      /* return checkaux(sib1(tree), pred); */
      tree = sib1(tree); goto tailcall;
    case TCall:  /* return checkaux(sib2(tree), pred); */
      tree = sib2(tree); goto tailcall;
    default: assert(0); return 0;
  };
}


/*
** number of characters to match a pattern (or -1 if variable)
** ('count' avoids infinite loops for grammars)
*/
int fixedlenx (TTree *tree, int count, int len) {
 tailcall:
  switch (tree->tag) {
    case TChar: case TSet: case TAny:
      return len + 1;
    case TFalse: case TTrue: case TNot: case TAnd: case TBehind:
      return len;
    case TRep: case TRunTime: case TOpenCall:
      return -1;
    case TCapture: case TRule: case TGrammar:
      /* return fixedlenx(sib1(tree), count); */
      tree = sib1(tree); goto tailcall;
    case TCall:
      if (count++ >= MAXRULES)
        return -1;  /* may be a loop */
      /* else return fixedlenx(sib2(tree), count); */
      tree = sib2(tree); goto tailcall;
    case TSeq: {
      len = fixedlenx(sib1(tree), count, len);
      if (len < 0) return -1;
      /* else return fixedlenx(sib2(tree), count, len); */
      tree = sib2(tree); goto tailcall;
    }
    case TChoice: {
      int n1, n2;
      n1 = fixedlenx(sib1(tree), count, len);
      if (n1 < 0) return -1;
      n2 = fixedlenx(sib2(tree), count, len);
      if (n1 == n2) return n1;
      else return -1;
    }
    default: assert(0); return 0;
  };
}


/*
** Computes the 'first set' of a pattern.
** The result is a conservative aproximation:
**   match p ax -> x' for some x ==> a in first(p).
**   match p '' -> ''            ==> returns 1.
** The set 'follow' is the first set of what follows the
** pattern (full set if nothing follows it)
*/
static int getfirst (TTree *tree, const Charset follow, Charset firstset) {
 tailcall:
  switch (tree->tag) {
    case TChar: case TSet: case TAny: {
      tocharset(tree, firstset);
      return 0;
    }
    case TTrue: {
      loopset(i, firstset[i] = follow[i]);
      return 1;
    }
    case TFalse: {
      loopset(i, firstset[i] = 0);
      return 0;
    }
    case TChoice: {
      Charset csaux;
      int e1 = getfirst(sib1(tree), follow, firstset);
      int e2 = getfirst(sib2(tree), follow, csaux);
      loopset(i, firstset[i] |= csaux[i]);
      return e1 | e2;
    }
    case TSeq: {
      if (!nullable(sib1(tree))) {
        /* return getfirst(sib1(tree), follow, firstset); */
        tree = sib1(tree); goto tailcall;
      }
      else {  /* FIRST(p1 p2, fl) = FIRST(p1, FIRST(p2, fl)) */
        Charset csaux;
        int e2 = getfirst(sib2(tree), follow, csaux);
        int e1 = getfirst(sib1(tree), csaux, firstset);
        return e1 & e2;
      }
    }
    case TRep: {
      getfirst(sib1(tree), follow, firstset);
      loopset(i, firstset[i] |= follow[i]);
      return 1;  /* accept the empty string */
    }
    case TCapture: case TGrammar: case TRule: {
      /* return getfirst(sib1(tree), follow, firstset); */
      tree = sib1(tree); goto tailcall;
    }
    case TRunTime: {  /* function invalidates any follow info. */
      /* return getfirst(sib1(tree), fullset, firstset); */
      tree = sib1(tree); follow = fullset; goto tailcall;
    }
    case TCall: {
      /* return getfirst(sib2(tree), follow, firstset); */
      tree = sib2(tree); goto tailcall;
    }
    case TAnd: {
      int e = getfirst(sib1(tree), follow, firstset);
      loopset(i, firstset[i] &= follow[i]);
      return e;
    }
    case TNot: {
      if (tocharset(sib1(tree), firstset)) {
        cs_complement(firstset);
        return 1;
      }
      /* else go through */
    }
    case TBehind: {  /* instruction gives no new information */
      loopset(i, firstset[i] = follow[i]);  /* uses follow */
      return 1;  /* can accept the empty string */
    }
    default: assert(0); return 0;
  }
}


/*
** If it returns true, then pattern can fail only depending on the next
** character of the subject
*/
static int headfail (TTree *tree) {
 tailcall:
  switch (tree->tag) {
    case TChar: case TSet: case TAny: case TFalse:
      return 1;
    case TTrue: case TRep: case TRunTime: case TNot:
    case TBehind:
      return 0;
    case TCapture: case TGrammar: case TRule: case TAnd:
      tree = sib1(tree); goto tailcall;  /* return headfail(sib1(tree)); */
    case TCall:
      tree = sib2(tree); goto tailcall;  /* return headfail(sib2(tree)); */
    case TSeq:
      if (!nofail(sib2(tree))) return 0;
      /* else return headfail(sib1(tree)); */
      tree = sib1(tree); goto tailcall;
    case TChoice:
      if (!headfail(sib1(tree))) return 0;
      /* else return headfail(sib2(tree)); */
      tree = sib2(tree); goto tailcall;
    default: assert(0); return 0;
  }
}


/*
** Check whether the code generation for the given tree can benefit
** from a follow set (to avoid computing the follow set when it is
** not needed)
*/
static int needfollow (TTree *tree) {
 tailcall:
  switch (tree->tag) {
    case TChar: case TSet: case TAny:
    case TFalse: case TTrue: case TAnd: case TNot:
    case TRunTime: case TGrammar: case TCall: case TBehind:
      return 0;
    case TChoice: case TRep:
      return 1;
    case TCapture:
      tree = sib1(tree); goto tailcall;
    case TSeq:
      tree = sib2(tree); goto tailcall;
    default: assert(0); return 0;
  } 
}

/* }====================================================== */



/*
** {======================================================
** Code generation
** =======================================================
*/

/*
** state for the compiler
*/
typedef struct CompileState {
  Pattern *p;  /* pattern being compiled */
  int ncode;  /* next position in p->code to be filled */
  lua_State *L;
} CompileState;


/*
** code generation is recursive; 'opt' indicates that the code is
** being generated under a 'IChoice' operator jumping to its end.
** 'tt' points to a previous test protecting this code. 'fl' is
** the follow set of the pattern.
*/
static void codegen (CompileState *compst, TTree *tree, int opt, int tt,
                     const Charset fl);


void reallocprog (lua_State *L, Pattern *p, int nsize) {
  void *ud;
  lua_Alloc f = lua_getallocf(L, &ud);
  void *newblock = f(ud, p->code, p->codesize * sizeof(Instruction),
                                  nsize * sizeof(Instruction));
  if (newblock == NULL && nsize > 0)
    luaL_error(L, "not enough memory");
  p->code = (Instruction *)newblock;
  p->codesize = nsize;
}


static int nextinstruction (CompileState *compst) {
  int size = compst->p->codesize;
  if (compst->ncode >= size) {
    if (size < (MAXPATTSIZE / 2))
      reallocprog(compst->L, compst->p, size * 2);
    else if (size < MAXPATTSIZE)
      reallocprog(compst->L, compst->p, MAXPATTSIZE);
    else luaL_error(compst->L, "pattern too large");
  }
  return compst->ncode++;
}


#define getinstr(cs,i)		((cs)->p->code[i])


static int addinstruction (CompileState *compst, Opcode op, int aux) {
  int i = nextinstruction(compst);
  getinstr(compst, i).i.code = op;
  getinstr(compst, i).i.aux = aux;
  return i;
}


static void setoffset (CompileState *compst, int instruction, int offset) {
  getinstr(compst, instruction).i.offset = offset;
}


/*
** Add a capture instruction:
** 'op' is the capture instruction; 'cap' the capture kind;
** 'key' the key into ktable; 'aux' is optional offset
**
*/
static int addinstcap (CompileState *compst, int op, int cap, int key,
                       int aux) {
  int i = addinstruction(compst, op, joinkindoff(cap, aux));
  setoffset(compst, i, key);
  return i;
}


#define gethere(compst) 	((compst)->ncode)

#define target(code,i)		((i) + code[i].i.offset)


static void jumptothere (CompileState *compst, int instruction, int target) {
  if (instruction >= 0)
    setoffset(compst, instruction, target - instruction);
}


static void jumptohere (CompileState *compst, int instruction) {
  jumptothere(compst, instruction, gethere(compst));
}


/*
** Code an IChar instruction, or IAny if there is an equivalent
** test dominating it
*/
static void codechar (CompileState *compst, int c, int tt) {
  if (tt >= 0 && getinstr(compst, tt).i.code == ITestChar &&
                 getinstr(compst, tt).i.aux == c)
    addinstruction(compst, IAny, 0);
  else
    addinstruction(compst, IChar, c);
}


/*
** Code an ISet instruction
*/
static int coderealcharset (CompileState *compst, byte *cs) {
  int p = addinstruction(compst, ISet, 0);
  int i;
  for (i = 0; i < (int)CHARSETINSTSIZE - 1; i++)
    nextinstruction(compst);  /* space for buffer */
  /* fill buffer with charset */
  loopset(j, getinstr(compst, p + 1).buff[j] = cs[j]);
  return p;
}


/*
** code a char set, optimizing unit sets for IChar, "complete"
** sets for IAny, and empty sets for IFail; also use an IAny
** when instruction is dominated by an equivalent test.
*/
static void codecharset (CompileState *compst, byte *cs, int tt) {
  int c = 0;  /* (=) to avoid warnings */
  int op = charsettype(cs, &c);
  switch (op) {
    case IChar: codechar(compst, c, tt); break;
    case ISet: {  /* non-trivial set? */
      if (tt >= 0 && getinstr(compst, tt).i.code == ITestSet &&
          cs_equal(cs, getinstr(compst, tt + 1).buff))
        addinstruction(compst, IAny, 0);
      else
        coderealcharset(compst, cs);
      break;
    }
    default: addinstruction(compst, op, c); break;
  }
}


/*
** code a test set, optimizing unit sets for ITestChar, "complete"
** sets for ITestAny, and empty sets for IJmp (always fails).
** 'e' is true iff test should accept the empty string. (Test
** instructions in the current VM never accept the empty string.)
*/
static int codetestset (CompileState *compst, byte *cs, int e) {
  if (e) return NOINST;  /* no test */
  else {
    Instruction *inst;
    int pos = gethere(compst);
    codecharset(compst, cs, NOINST);
    inst = &getinstr(compst, pos);
    switch (inst->i.code) {
      case IFail: inst->i.code = IJmp; break;  /* always jump */
      case IAny: inst->i.code = ITestAny; break;
      case IChar: inst->i.code = ITestChar; break;
      case ISet: inst->i.code = ITestSet; break;
      default: assert(0);
    }
    return pos;
  }
}


/*
** Find the final destination of a sequence of jumps
*/
static int finaltarget (Instruction *code, int i) {
  while (code[i].i.code == IJmp)
    i = target(code, i);
  return i;
}


/*
** final label (after traversing any jumps)
*/
static int finallabel (Instruction *code, int i) {
  return finaltarget(code, target(code, i));
}


/*
** <behind(p)> == behind n; <p>   (where n = fixedlen(p))
*/
static void codebehind (CompileState *compst, TTree *tree) {
  if (tree->u.n > 0)
    addinstruction(compst, IBehind, tree->u.n);
  codegen(compst, sib1(tree), 0, NOINST, fullset);
}


/*
** Choice; optimizations:
** - when p1 is headfail
** - when first(p1) and first(p2) are disjoint; than
** a character not in first(p1) cannot go to p1, and a character
** in first(p1) cannot go to p2 (at it is not in first(p2)).
** (The optimization is not valid if p1 accepts the empty string,
** as then there is no character at all...)
** - when p2 is empty and opt is true; a IPartialCommit can resuse
** the Choice already active in the stack.
*/
static void codechoice (CompileState *compst, TTree *p1, TTree *p2, int opt,
                        const Charset fl) {
  int emptyp2 = (p2->tag == TTrue);
  Charset st1, st2;
  int e1 = getfirst(p1, fullset, st1);
  if (headfail(p1) ||
      (!e1 && (getfirst(p2, fl, st2), cs_disjoint(st1, st2)))) {
    /* <p1 / p2> == test (fail(p1)) -> L1 ; p1 ; jmp L2; L1: p2; L2: */
    int test = codetestset(compst, st1, 0);
    int jmp = NOINST;
    codegen(compst, p1, 0, test, fl);
    if (!emptyp2)
      jmp = addinstruction(compst, IJmp, 0); 
    jumptohere(compst, test);
    codegen(compst, p2, opt, NOINST, fl);
    jumptohere(compst, jmp);
  }
  else if (opt && emptyp2) {
    /* p1? == IPartialCommit; p1 */
    jumptohere(compst, addinstruction(compst, IPartialCommit, 0));
    codegen(compst, p1, 1, NOINST, fullset);
  }
  else {
    /* <p1 / p2> == 
        test(fail(p1)) -> L1; choice L1; <p1>; commit L2; L1: <p2>; L2: */
    int pcommit;
    int test = codetestset(compst, st1, e1);
    int pchoice = addinstruction(compst, IChoice, 0);
    codegen(compst, p1, emptyp2, test, fullset);
    pcommit = addinstruction(compst, ICommit, 0);
    jumptohere(compst, pchoice);
    jumptohere(compst, test);
    codegen(compst, p2, opt, NOINST, fl);
    jumptohere(compst, pcommit);
  }
}


/*
** And predicate
** optimization: fixedlen(p) = n ==> <&p> == <p>; behind n
** (valid only when 'p' has no captures)
*/
static void codeand (CompileState *compst, TTree *tree, int tt) {
  int n = fixedlen(tree);
  if (n >= 0 && n <= MAXBEHIND && !hascaptures(tree)) {
    codegen(compst, tree, 0, tt, fullset);
    if (n > 0)
      addinstruction(compst, IBehind, n);
  }
  else {  /* default: Choice L1; p1; BackCommit L2; L1: Fail; L2: */
    int pcommit;
    int pchoice = addinstruction(compst, IChoice, 0);
    codegen(compst, tree, 0, tt, fullset);
    pcommit = addinstruction(compst, IBackCommit, 0);
    jumptohere(compst, pchoice);
    addinstruction(compst, IFail, 0);
    jumptohere(compst, pcommit);
  }
}


/*
** Captures: if pattern has fixed (and not too big) length, use
** a single IFullCapture instruction after the match; otherwise,
** enclose the pattern with OpenCapture - CloseCapture.
*/
static void codecapture (CompileState *compst, TTree *tree, int tt,
                         const Charset fl) {
  int len = fixedlen(sib1(tree));
  if (len >= 0 && len <= MAXOFF && !hascaptures(sib1(tree))) {
    codegen(compst, sib1(tree), 0, tt, fl);
    addinstcap(compst, IFullCapture, tree->cap, tree->key, len);
  }
  else {
    addinstcap(compst, IOpenCapture, tree->cap, tree->key, 0);
    codegen(compst, sib1(tree), 0, tt, fl);
    addinstcap(compst, ICloseCapture, Cclose, 0, 0);
  }
}


static void coderuntime (CompileState *compst, TTree *tree, int tt) {
  addinstcap(compst, IOpenCapture, Cgroup, tree->key, 0);
  codegen(compst, sib1(tree), 0, tt, fullset);
  addinstcap(compst, ICloseRunTime, Cclose, 0, 0);
}


/*
** Repetion; optimizations:
** When pattern is a charset, can use special instruction ISpan.
** When pattern is head fail, or if it starts with characters that
** are disjoint from what follows the repetions, a simple test
** is enough (a fail inside the repetition would backtrack to fail
** again in the following pattern, so there is no need for a choice).
** When 'opt' is true, the repetion can reuse the Choice already
** active in the stack.
*/
static void coderep (CompileState *compst, TTree *tree, int opt,
                     const Charset fl) {
  Charset st;
  if (tocharset(tree, st)) {
    int op = coderealcharset(compst, st);
    getinstr(compst, op).i.code = ISpan;
  }
  else {
    int e1 = getfirst(tree, fullset, st);
    if (headfail(tree) || (!e1 && cs_disjoint(st, fl))) {
      /* L1: test (fail(p1)) -> L2; <p>; jmp L1; L2: */
      int jmp;
      int test = codetestset(compst, st, 0);
      codegen(compst, tree, opt, test, fullset);
      jmp = addinstruction(compst, IJmp, 0);
      jumptohere(compst, test);
      jumptothere(compst, jmp, test);
    }
    else {
      /* test(fail(p1)) -> L2; choice L2; L1: <p>; partialcommit L1; L2: */
      /* or (if 'opt'): partialcommit L1; L1: <p>; partialcommit L1; */
      int commit, l2;
      int test = codetestset(compst, st, e1);
      int pchoice = NOINST;
      if (opt)
        jumptohere(compst, addinstruction(compst, IPartialCommit, 0));
      else
        pchoice = addinstruction(compst, IChoice, 0);
      l2 = gethere(compst);
      codegen(compst, tree, 0, NOINST, fullset);
      commit = addinstruction(compst, IPartialCommit, 0);
      jumptothere(compst, commit, l2);
      jumptohere(compst, pchoice);
      jumptohere(compst, test);
    }
  }
}


/*
** Not predicate; optimizations:
** In any case, if first test fails, 'not' succeeds, so it can jump to
** the end. If pattern is headfail, that is all (it cannot fail
** in other parts); this case includes 'not' of simple sets. Otherwise,
** use the default code (a choice plus a failtwice).
*/
static void codenot (CompileState *compst, TTree *tree) {
  Charset st;
  int e = getfirst(tree, fullset, st);
  int test = codetestset(compst, st, e);
  if (headfail(tree))  /* test (fail(p1)) -> L1; fail; L1:  */
    addinstruction(compst, IFail, 0);
  else {
    /* test(fail(p))-> L1; choice L1; <p>; failtwice; L1:  */
    int pchoice = addinstruction(compst, IChoice, 0);
    codegen(compst, tree, 0, NOINST, fullset);
    addinstruction(compst, IFailTwice, 0);
    jumptohere(compst, pchoice);
  }
  jumptohere(compst, test);
}


/*
** change open calls to calls, using list 'positions' to find
** correct offsets; also optimize tail calls
*/
static void correctcalls (CompileState *compst, int *positions,
                          int from, int to) {
  int i;
  Instruction *code = compst->p->code;
  for (i = from; i < to; i++) {
    if (code[i].i.code == IOpenCall) {
      int n = code[i].i.offset;  /* rule number */
      int rule = positions[n];  /* rule position */
      assert(rule == from || code[rule - 1].i.code == IRet);
      if (code[finaltarget(code, i + 1)].i.code == IRet)  /* call; ret ? */
        code[i].i.code = IJmp;  /* tail call */
      else
        code[i].i.code = ICall;
      jumptothere(compst, i, rule);  /* call jumps to respective rule */
    }
  }
}


/*
** Code for a grammar:
** call L1; jmp L2; L1: rule 1; ret; rule 2; ret; ...; L2:
*/
static void codegrammar (CompileState *compst, TTree *grammar) {
  int positions[MAXRULES];
  int rulenumber = 0;
  TTree *rule;
  int firstcall = addinstruction(compst, ICall, 0);  /* call initial rule */
  int jumptoend = addinstruction(compst, IJmp, 0);  /* jump to the end */
  jumptohere(compst, firstcall);  /* here starts the initial rule */
  for (rule = sib1(grammar); rule->tag == TRule; rule = sib2(rule)) {
    positions[rulenumber++] = gethere(compst);  /* save rule position */
    codegen(compst, sib1(rule), 0, NOINST, fullset);  /* code rule */
    addinstruction(compst, IRet, 0);
  }
  assert(rule->tag == TTrue);
  jumptohere(compst, jumptoend);
  correctcalls(compst, positions, firstcall + 2, gethere(compst));
}


static void codecall (CompileState *compst, TTree *call) {
  int c = addinstruction(compst, IOpenCall, 0);  /* to be corrected later */
  assert(sib2(call)->tag == TRule);
  setoffset(compst, c, sib2(call)->cap);  /* offset = rule number */
}


static void codeseq (CompileState *compst, TTree *p1, TTree *p2,
                     int opt, int tt, const Charset fl) {
  if (needfollow(p1)) {
    Charset fl1;
    getfirst(p2, fl, fl1);  /* p1 follow is p2 first */
    codegen(compst, p1, 0, tt, fl1);
  }
  else  /* use 'fullset' as follow */
    codegen(compst, p1, 0, tt, fullset);
  if (fixedlen(p1) != 0)  /* can p1 consume anything? */
    tt = NOINST;  /* invalidate test */
  codegen(compst, p2, opt, tt, fl);
}


/*
** Main code-generation function: dispatch to auxiliar functions
** according to kind of tree
*/
static void codegen (CompileState *compst, TTree *tree, int opt, int tt,
                     const Charset fl) {
  switch (tree->tag) {
    case TChar: codechar(compst, tree->u.n, tt); break;
    case TAny: addinstruction(compst, IAny, 0); break;
    case TSet: codecharset(compst, treebuffer(tree), tt); break;
    case TTrue: break;
    case TFalse: addinstruction(compst, IFail, 0); break;
    case TSeq: codeseq(compst, sib1(tree), sib2(tree), opt, tt, fl); break;
    case TChoice: codechoice(compst, sib1(tree), sib2(tree), opt, fl); break;
    case TRep: coderep(compst, sib1(tree), opt, fl); break;
    case TBehind: codebehind(compst, tree); break;
    case TNot: codenot(compst, sib1(tree)); break;
    case TAnd: codeand(compst, sib1(tree), tt); break;
    case TCapture: codecapture(compst, tree, tt, fl); break;
    case TRunTime: coderuntime(compst, tree, tt); break;
    case TGrammar: codegrammar(compst, tree); break;
    case TCall: codecall(compst, tree); break;
    default: assert(0);
  }
}


/*
** Optimize jumps and other jump-like instructions.
** * Update labels of instructions with labels to their final
** destinations (e.g., choice L1; ... L1: jmp L2: becomes
** choice L2)
** * Jumps to other instructions that do jumps become those
** instructions (e.g., jump to return becomes a return; jump
** to commit becomes a commit)
*/
static void peephole (CompileState *compst) {
  Instruction *code = compst->p->code;
  int i;
  for (i = 0; i < compst->ncode; i++) {
    switch (code[i].i.code) {
      case IChoice: case ICall: case ICommit: case IPartialCommit:
      case IBackCommit: case ITestChar: case ITestSet:
      case ITestAny: {  /* instructions with labels */
        jumptothere(compst, i, finallabel(code, i));  /* optimize label */
        break;
      }
      case IJmp: {
        int ft = finaltarget(code, i);
        switch (code[ft].i.code) {  /* jumping to what? */
          case IRet: case IFail: case IFailTwice:
          case IEnd: {  /* instructions with unconditional implicit jumps */
            code[i] = code[ft];  /* jump becomes that instruction */
            break;
          }
          case ICommit: case IPartialCommit:
          case IBackCommit: {  /* inst. with unconditional explicit jumps */
            int fft = finallabel(code, ft);
            code[i] = code[ft];  /* jump becomes that instruction... */
            jumptothere(compst, i, fft);  /* but must correct its offset */
            i--;  /* reoptimize its label */
            break;
          }
          default: {
            jumptothere(compst, i, ft);  /* optimize label */
            break;
          }
        }
        break;
      }
      default: break;
    }
  }
}


/*
** Compile a pattern
*/
Instruction *compile (lua_State *L, Pattern *p) {
  CompileState compst;
  compst.p = p;  compst.ncode = 0;  compst.L = L;
  reallocprog(L, p, 2);  /* minimum initial size */
  codegen(&compst, p->tree, 0, NOINST, fullset);
  addinstruction(&compst, IEnd, 0);
  reallocprog(L, p, compst.ncode);  /* set final size */
  peephole(&compst);
  return p->code;
}


/* }====================================================== */

