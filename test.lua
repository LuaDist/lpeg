#!/usr/local/bin/lua5.1

local m = require"lpeg"

print"General tests for LPeg library"

assert(m.match("aaaa", 3))
assert(m.match("aaaa", 4))
assert(not m.match("aaaa", 5))
assert(not m.match("aaaa", -3))
assert(not m.match("aaaa", -4))
assert(m.match("aaaa", -5))

assert(m.match("alo", "a") == 2)
assert(m.match("alo", "al") == 3)
assert(not m.match("alo", "alu"))

digit = m.S"01234567" + "8" + "9"
upper = m.S"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lower = m.R("a", "z")
letter = upper + lower
alpha = letter + digit

word = alpha^1 * (1 - alpha)^0

assert(m.match("alo alo", word^0 * -1))
assert(m.match("alo alo", word^1 * -1))
assert(m.match("alo alo", word^2 * -1))
assert(not m.match("alo alo", word^3 * -1))

assert(not m.match("alo alo", word^-1 * -1))
assert(m.match("alo alo", word^-2 * -1))
assert(m.match("alo alo", word^-3 * -1))

eos = m.P(-1)

assert(m.match("1298a1", digit^0 * letter * digit * eos))
assert(not m.match("1257a1", digit^0 * letter * eos))

b = {
  [1] = "(" * (((1 - m.S"()") + #m.P"(" * m.V(1))^0) * ")"
}

assert(m.match("(al())()", b))
assert(not m.match("(al())()", b * eos))
assert(m.match("((al())()(é))", b * eos))
assert(not m.match("(al()()", b))

assert(not m.match("foreach", letter^1 - "for"))
assert(m.match("foreach", letter^1 - ("for" * eos)))
assert(not m.match("for", letter^1 - ("for" * eos)))

function basiclookfor (p)
  return m.P {
    [1] = p + (1 * m.V(1))
  }
end

function caplookfor (p)
  return basiclookfor(m.C(p))
end

assert(m.match("   4achou123...", caplookfor(letter^1)) == "achou")
a = {m.match(" two words, one more  ", caplookfor(letter^1)^0)}
assert(a[1] == "two" and a[2] == "words" and a[3] == "one" and a[4] == "more")

assert(m.match("  (  (a)", basiclookfor((#m.P(b) * 1) * m.I())) == 7)

assert(m.match("  éção46", caplookfor(m.utf8("digit")^1)) == "46")

a = {m.match("123", m.C(digit^1, "d") + m.C(letter^1, "l"))}
assert(a[1] == "d" and a[2] == "123")

a = {m.match("abcd", m.C(digit^1, "d") + m.C(letter^1, "l"))}
assert(a[1] == "l" and a[2] == "abcd")

a = {m.match("abcd", m.I"begin" * letter^1 * m.I"end")}
assert(a[1] == "begin" and a[2] == 1 and a[3] == "end" and a[4] == 5)

-- test for alternation optimization
assert(m.match("abcd", m.P"ab" + "cd" + m.P"e"^1 + "x") == 3)
assert(m.match("eeex", m.P"ab" + "cd" + m.P"e"^1 + "x") == 4)
assert(m.match("eeex", m.P"ab" + "cd" + m.P"e"^1 + "x") == 4)
assert(m.match("cd", m.P"ab" + "cd" + m.P"e"^1 + "x") == 3)
assert(m.match("x", m.P"ab" + "cd" + m.P"e"^1 + "x") == 2)
assert(m.match("zee", m.P"ab" + "cd" + m.P"e"^1 + "x" + "") == 1)
print"+"

-- test for table captures
t = m.match("alo", m.T(letter^1))
assert(not next(t))

n, t = m.match("alo", m.T(letter^1, "t"))
assert(not next(t) and n == "t")

n, t = m.match("alo", m.T(m.C(letter)^1, "t"))
assert(n == "t" and table.concat(t) == "alo")

t = m.match("alo", m.T(m.C(m.C(letter)^1)))
assert(table.concat(t, ";") == "alo;a;l;o")

t = m.match("alo", m.T(m.C(m.C(letter)^1, "n")))
assert(table.concat(t, ";") == "a;l;o" and t.n == "alo")

t = m.match("alo", m.T(m.T((m.I() * letter * m.I())^1, "n")))
assert(table.concat(t.n, ";") == "1;2;2;3;3;4")


g = {
  [1] = m.V(2) * m.V(3) * m.V(4);
  [2] = m.C('a', 'x');
  [3] = m.C('b', 'y');
  [4] = m.C(1) * m.V(4) + m.I("end")
}

t = m.match("aabcd", m.T(g), 2)
assert(t.x == 'a' and t.y == 'b' and t[1] == 'c' and t[2] == 'd' and
       t[3] == nil and t['end'] == 6)


-- test for non-pattern as arguments to pattern functions

p = { ('a' * m.V(1))^-1 } * m.P'b' * { 'a' * m.V(2); m.V(1)^-1 }
assert(m.match("aaabaac", p) == 7)


-- test for errors
assert(not pcall(m.match, "a", { m.V(1) * 'a' }))
assert(not pcall(m.match, string.rep("a", 10000), m.C('a')^0))


t = m.match(string.rep("a", 10000), m.T(m.C('a')^0))
assert(#t == 10000 and t[1] == 'a' and t[#t] == 'a')

print('+')


local V = lpeg.V

local Space = lpeg.S(" \n\t")^0
local Number = lpeg.C(lpeg.R("0", "9")^1) * Space
local FactorOp = lpeg.C(lpeg.S("+-")) * Space
local TermOp = lpeg.C(lpeg.S("*/")) * Space
local Open = "(" * Space
local Close = ")" * Space

local Exp, Term, Factor = 1, 2, 3
G = lpeg.P{
  [Exp] = lpeg.T(V(Factor) * (FactorOp * V(Factor))^0);
  [Factor] = lpeg.T(V(Term) * (TermOp * V(Term))^0);
  [Term] = Number + Open * V(Exp) * Close;
}

G = Space * G * -1

function eval (x)
  if type(x) == "string" then
    return tonumber(x)
  else
    local op1 = eval(x[1])
    for i = 2, #x, 2 do
      local op = x[i]
      local op2 = eval(x[i + 1])
      if (op == "+") then op1 = op1 + op2
      elseif (op == "-") then op1 = op1 - op2
      elseif (op == "*") then op1 = op1 * op2
      elseif (op == "/") then op1 = op1 / op2
      end
    end
    return op1
  end
end

function evalExp (s)
  local t = lpeg.match(s, G)
  if not t then error("syntax error", 2) end
  return eval(t)
end

for _, s in ipairs{" 3 + 5*9 / (1+1) ", "3+4/2", "3+3+3-2*2+3*9/1-  8"} do
  assert(evalExp(s) == loadstring("return "..s)())
end


-- tests for \0
assert(m.match("\0\1\0", m.R("\0", "\1")^1) == 4)
assert(m.match("\0\1\0a", m.S("\0\1ab")^1) == 5)
assert(m.match("\0\1\0a", m.P(1)^3) == 5)
assert(not m.match("\0\1\0a", -4))
assert(m.match("\0\1\0a", "\0\1\0a") == 5)


-- tests for optional start position
assert(m.match("abc", "a", 1))
assert(m.match("abc", "b", 2))
assert(m.match("abc", "c", 3))
assert(not m.match("abc", 1, 4))
assert(m.match("abc", "a", -3))
assert(m.match("abc", "b", -2))
assert(m.match("abc", "c", -1))
assert(m.match("abc", "abc", -4))   -- truncate to position 1

assert(m.match("abc", "", 10))   -- empty string is everywhere!
assert(m.match("", "", 10))
assert(not m.match("", 1, 1))
assert(not m.match("", 1, -1))
assert(not m.match("", 1, 0))


-- tests for arbitrary label values
local v1, v2, v3  = {}, print, "hello"
t = m.match("abc", m.T(m.C(1, v1) * m.C(1, v2) * m.C(1)))
assert(t[v1] == 'a' and t[v2] == 'b' and t[1] == 'c')
a, b, c, d, e, f = m.match("abc", m.C(1, v1) * m.C(1, v2) * m.C(1))
assert(a == v1 and b == "a" and c == v2 and d == "b" and e == "c" and f == nil)
assert(t[v1] == 'a' and t[v2] == 'b' and t[1] == 'c')
t = m.match("abc", m.T(m.C('b', v1) + m.C(2, v2) * m.C(1)))
assert(t[v2] == 'ab' and t[1] == 'c')


-- infinite loops
assert(not pcall(m.match, "a", m.P""^0))
assert(not pcall(m.match, "a", (-m.P"ab")^0))
assert(m.match("a", m.P""^-3) == 1)

-- basic tests for utf8
-- break a UTF8 string into characters

c = "君が Ελληνικά"

u = m.T((m.I() * m.utf8())^0)

t = (m.match(c, u))
assert(#t == 11 and t[4] - t[1] == string.len("君が ") and
                    t[5] - t[4] == string.len("Ε"))





print"OK"

