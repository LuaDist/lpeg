/*
** $Id: lpcode.h,v 1.2 2013/03/27 15:48:56 roberto Exp $
*/

#if !defined(lpcode_h)
#define lpcode_h

#include "lua.h"

#include "lptypes.h"
#include "lptree.h"
#include "lpvm.h"

int tocharset (TTree *tree, byte *cs);
int checkaux (TTree *tree, int pred);
int fixedlenx (TTree *tree, int count, int len);
int hascaptures (TTree *tree);
int lp_gc (lua_State *L);
Instruction *compile (lua_State *L, Pattern *p);
void reallocprog (lua_State *L, Pattern *p, int nsize);


#define PEnullable      0
#define PEnofail        2

#define nofail(t)	checkaux(t, PEnofail)
#define nullable(t)	checkaux(t, PEnullable)

#define fixedlen(t)     fixedlenx(t, 0, 0)



#endif
