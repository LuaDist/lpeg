#!/usr/local/bin/lua5.1

local m = require"lpeg"

local function checkeq (x, y)
  if type(x) ~= "table" then assert(x == y)
  else
    assert(#x == #y)
    for i = 1, #x do
      checkeq(x[i], y[i])
    end
  end
end



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
checkeq(a, {"two", "words", "one", "more"})

assert(m.match("  (  (a)", basiclookfor((#m.P(b) * 1) * m.Cp())) == 7)

assert(m.match("  éção46", caplookfor(m.utf8("digit")^1)) == "46")

a = {m.match("123", m.C(digit^1, "d") + m.C(letter^1, "l"))}
checkeq(a, {"d", "123"})

a = {m.match("abcd", m.C(digit^1, "d") + m.C(letter^1, "l"))}
checkeq(a, {"l", "abcd"})

a = {m.match("abcd", m.Cp"begin" * letter^1 * m.Cp"end")}
checkeq(a, {"begin", 1, "end", 5})

-- test for alternation optimization
assert(m.match("abcd", m.P"ab" + "cd" + m.P"e"^1 + "x") == 3)
assert(m.match("eeex", m.P"ab" + "cd" + m.P"e"^1 + "x") == 4)
assert(m.match("eeex", m.P"ab" + "cd" + m.P"e"^1 + "x") == 4)
assert(m.match("cd", m.P"ab" + "cd" + m.P"e"^1 + "x") == 3)
assert(m.match("x", m.P"ab" + "cd" + m.P"e"^1 + "x") == 2)
assert(m.match("zee", m.P"ab" + "cd" + m.P"e"^1 + "x" + "") == 1)
print"+"

-- test for table captures
t = m.match("alo", m.Ct(letter^1))
assert(not next(t))

n, t = m.match("alo", m.Ct(letter^1, "t"))
assert(not next(t) and n == "t")

n, t = m.match("alo", m.Ct(m.C(letter)^1, "t"))
assert(n == "t" and table.concat(t) == "alo")

t = m.match("alo", m.Ct(m.C(m.C(letter)^1)))
assert(table.concat(t, ";") == "alo;a;l;o")

t = m.match("alo", m.Ct(m.C(m.C(letter)^1, "n")))
assert(table.concat(t, ";") == "a;l;o" and t.n == "alo")

t = m.match("alo", m.Ct(m.Ct((m.Cp() * letter * m.Cp())^1, "n")))
assert(table.concat(t.n, ";") == "1;2;2;3;3;4")

t = m.match("alo", m.Ct(m.C(m.C(1) * 1 * m.C(1))))
checkeq(t, {"alo", "a", "o"})


g = {
  [1] = m.V(2) * m.V(3) * m.V(4);
  [2] = m.C('a', 'x');
  [3] = m.C('b', 'y');
  [4] = m.C(1) * m.V(4) + m.Cp("end")
}

t = m.match("aabcd", m.Ct(g), 2)
assert(t.x == 'a' and t.y == 'b' and t[1] == 'c' and t[2] == 'd' and
       t[3] == nil and t['end'] == 6)


-- test for non-pattern as arguments to pattern functions

p = { ('a' * m.V(1))^-1 } * m.P'b' * { 'a' * m.V(2); m.V(1)^-1 }
assert(m.match("aaabaac", p) == 7)


-- test for errors
assert(not pcall(m.match, "a", { m.V(1) * 'a' }))
assert(not pcall(m.match, string.rep("a", 10000), m.C('a')^0))
assert(not pcall(m.match, "", m.V(1)))   -- open grammar

t = m.match(string.rep("a", 10000), m.Ct(m.C('a')^0))
assert(#t == 10000 and t[1] == 'a' and t[#t] == 'a')

print('+')


local V = m.V

local Space = m.S(" \n\t")^0
local Number = m.C(m.R("0", "9")^1) * Space
local FactorOp = m.C(m.S("+-")) * Space
local TermOp = m.C(m.S("*/")) * Space
local Open = "(" * Space
local Close = ")" * Space


local function f_factor (v1, op, v2, d)
  assert(d == nil)
  if op == "+" then return v1 + v2
  else return v1 - v2
  end
end


local function f_term (v1, op, v2, d)
  assert(d == nil)
  if op == "*" then return v1 * v2
  else return v1 / v2
  end
end

local Exp, Term, Factor = 1, 2, 3
G = m.P{
  [Exp] = m.Ca(V(Factor) * (FactorOp * V(Factor) / f_factor)^0);
  [Factor] = m.Ca(V(Term) * (TermOp * V(Term) / f_term)^0);
  [Term] = Number / tonumber  +  Open * V(Exp) * Close;
}

G = Space * G * -1

for _, s in ipairs{" 3 + 5*9 / (1+1) ", "3+4/2", "3+3-3- 9*2+3*9/1-  8"} do
  assert(m.match(s, G) == loadstring("return "..s)())
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
t = m.match("abc", m.Ct(m.C(1, v1) * m.C(1, v2) * m.C(1)))
assert(t[v1] == 'a' and t[v2] == 'b' and t[1] == 'c')
a, b, c, d, e, f = m.match("abc", m.C(1, v1) * m.C(1, v2) * m.C(1))
assert(a == v1 and b == "a" and c == v2 and d == "b" and e == "c" and f == nil)
assert(t[v1] == 'a' and t[v2] == 'b' and t[1] == 'c')
t = m.match("abc", m.Ct(m.C('b', v1) + m.C(2, v2) * m.C(1)))
assert(t[v2] == 'ab' and t[1] == 'c')


-- infinite loops
assert(not pcall(m.match, "a", m.P""^0))
assert(not pcall(m.match, "a", (-m.P"ab")^0))
assert(m.match("a", m.P""^-3) == 1)


-- basic tests for utf8
-- break a UTF8 string into characters

c = "君が Ελληνικά"

u = m.Ct((m.Cp() * m.utf8())^0)

t = (m.match(c, u))
assert(#t == 11 and t[4] - t[1] == string.len("君が ") and
                    t[5] - t[4] == string.len("Ε"))

print("+")


-- tests for Lua functions

t = {}
s = ""
p = m.F(function (s1, i) assert(s == s1); t[#t + 1] = i end)
s = "hi, this is a test"
assert(m.match(s, ((p - -1) + 2)^0) == string.len(s) + 1)
assert(#t == string.len(s)/2 and t[1] == 1 and t[2] == 3)

assert(not m.match(s, p))


t = {}
p = m.F(function (s1, i) assert(s == s1); t[#t + 1] = i; return i end)
s = "hi, this is a test"
assert(m.match(s, (1 * p)^0) == string.len(s) + 1)
assert(#t == string.len(s) and t[1] == 2 and t[2] == 3)

t = {}
p = m.F(function (s1, i) assert(s == s1); t[#t + 1] = i; return i + 1 end)
s = "hi, this is a test"
assert(m.match(s, p^0) == string.len(s) + 1)
assert(#t == string.len(s) + 1 and t[1] == 1 and t[2] == 2)

p = m.F(function (s1, i) return m.match(s1, m.P"a"^0, i) end)
assert(m.match("aaaa", p) == 5)
assert(m.match("baaa", p) == 1)

assert(not m.match(s, m.F(function () return 2^20 end)))
assert(not m.match(s, m.F(function () return 0 end)))
assert(not m.match(s, m.P(1)^0 * m.F(function (_, i) return i - 1 end)))
assert(m.match(s, m.P(1)^0 * m.F(function (_, i) return i end)) ==
       string.len(s) + 1)
for i = 1, string.len(s) + 1 do
  assert(m.match(s, m.F(function (_, _) return i end)) == i)
end


-- tests for Function Replacements
f = function (a, ...) if a ~= "x" then return {a, ...} end end

t = m.match("abc", m.C(1)^0/f)
checkeq(t, {"a", "b", "c"})

t = m.match("abc", m.C(1)^0/f/f)
checkeq(t, {{"a", "b", "c"}})

t = m.match("abc", m.P(1)^0/f/f)   -- no capture
checkeq(t, {{"abc"}})

t = m.match("abc", (m.P(1)^0/f * m.Cp())/f)
checkeq(t, {{"abc"}, 4})

t = m.match("abc", (m.C(1)^0/f * m.Cp())/f)
checkeq(t, {{"a", "b", "c"}, 4})

t = m.match("xbc", (m.C(1)^0/f * m.Cp())/f)
checkeq(t, {4})

t = m.match("abc", m.C(m.C(1)^0)/f)
checkeq(t, {"abc", "a", "b", "c"})

assert(m.match("abc", m.C(m.C(1)^0)/{abc = 10}) == 10)
assert(m.match("abc", m.C(1)^0/{a = 10}) == 10)
assert(m.match("abc", m.S("ba")^0/{ab = 40}) == 40)
t = m.match("abc", m.Ct((m.S("ba")/{a = 40})^0))
checkeq(t, {40})

assert(m.match("abcdde", m.Cs((m.C(1)/{a=".", d=".."})^0)) == ".bc....e")
assert(m.match("abcdde", m.Cs((m.C(1)/{f="."})^0)) == "abcdde")
assert(m.match("abcdde", m.Cs((m.C(1))^0)) == "abcdde")
assert(not pcall(m.match, "abcdde", m.Cs(m.C(m.C(1)^0))))

assert(m.match("abcd", m.Cs((m.P(1) / "%0")^0)) == "abcd")
assert(m.match("abcd", m.Cs((m.P(1) / "%0.%0")^0)) == "a.ab.bc.cd.d")
assert(m.match("abcad", m.Cs((m.P("a") / "%0.%0" + 1)^0)) == "a.abca.ad")
assert(m.match("a", m.C("a") / "%1%%%0") == "a%a")

assert(not pcall(m.match, "abc", m.P(1)/"%1"))   -- out of range
assert(not pcall(m.match, "abc", m.P(1)/"%9"))   -- out of range
assert(not pcall(m.match, "abc", m.Cp()/"%1"))   -- invalid nesting

function f (x) return x + 1 end
assert(m.match("alo alo", m.Ca(m.Cc(0) * (m.P(1) / f)^0)) == 7)

assert(m.match("", m.Cc(print)) == print)

s = string.rep("12345678901234567890", 20)
assert(m.match(s, m.C(1)^0 / "%9-%1-%0-%3") == "9-1-" .. s .. "-3")

print"OK"

