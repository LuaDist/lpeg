#!/usr/local/bin/lua5.1

local m = require"lpeg"

assert(m.match("aaaa", 3))
assert(m.match("aaaa", 4))
assert(not m.match("aaaa", 5))
assert(not m.match("aaaa", -3))
assert(not m.match("aaaa", -4))
assert(m.match("aaaa", -5))


digit = m.S"0123456789"
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

assert(m.match("1222a1", digit^0 * letter * digit * eos))
assert(not m.match("1222a1", digit^0 * letter * eos))

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


-- test for non-pattern as arguments to pattern functions

p = { ('a' * m.V(1))^-1 } * m.P'b' * { 'a' * m.V(2); m.V(1)^-1 }
assert(m.match("aaabaac", p) == 7)


-- test for errors
assert(not pcall(m.match, "a", { m.V(1) * 'a' }))
assert(not pcall(m.match, string.rep("a", 10000), m.C('a')^0))

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

print"OK"

