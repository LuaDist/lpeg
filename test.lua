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


mt = getmetatable(m.P(1))


local allchar = {}
for i=0,255 do allchar[i + 1] = i end
allchar = string.char(unpack(allchar))
assert(#allchar == 256)

local function cs2str (c)
  return m.match(m.Cs((c + m.P(1)/"")^0), allchar)
end

local function eqcharset (c1, c2)
  assert(cs2str(c1) == cs2str(c2))
end


print"General tests for LPeg library"

assert(m.match(3, "aaaa"))
assert(m.match(4, "aaaa"))
assert(not m.match(5, "aaaa"))
assert(m.match(-3, "aa"))
assert(not m.match(-3, "aaa"))
assert(not m.match(-3, "aaaa"))
assert(not m.match(-4, "aaaa"))
assert(m.P(-5):match"aaaa")

assert(m.match("a", "alo") == 2)
assert(m.match("al", "alo") == 3)
assert(not m.match("alu", "alo"))
assert(m.match(true, "") == 1)

digit = m.S"0123456789"
upper = m.S"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
lower = m.S"abcdefghijklmnopqrstuvwxyz"
letter = m.S"" + upper + lower
alpha = letter + digit + m.R()

eqcharset(m.S"", m.P(false))
eqcharset(upper, m.R("AZ"))
eqcharset(lower, m.R("az"))
eqcharset(upper + lower, m.R("AZ", "az"))
eqcharset(upper + lower, m.R("AZ", "cz", "aa", "bb", "90"))
eqcharset(digit, m.S"01234567" + "8" + "9")
eqcharset(upper, letter - lower)
eqcharset(m.S(""), m.R())
assert(cs2str(m.S("")) == "")

word = alpha^1 * (1 - alpha)^0

assert((word^0 * -1):match"alo alo")
assert(m.match(word^1 * -1, "alo alo"))
assert(m.match(word^2 * -1, "alo alo"))
assert(not m.match(word^3 * -1, "alo alo"))

assert(not m.match(word^-1 * -1, "alo alo"))
assert(m.match(word^-2 * -1, "alo alo"))
assert(m.match(word^-3 * -1, "alo alo"))

eos = m.P(-1)

assert(m.match(digit^0 * letter * digit * eos, "1298a1"))
assert(not m.match(digit^0 * letter * eos, "1257a1"))

b = {
  [1] = "(" * (((1 - m.S"()") + #m.P"(" * m.V(1))^0) * ")"
}

assert(m.match(b, "(al())()"))
assert(not m.match(b * eos, "(al())()"))
assert(m.match(b * eos, "((al())()(é))"))
assert(not m.match(b, "(al()()"))

assert(not m.match(letter^1 - "for", "foreach"))
assert(m.match(letter^1 - ("for" * eos), "foreach"))
assert(not m.match(letter^1 - ("for" * eos), "for"))

function basiclookfor (p)
  return m.P {
    [1] = p + (1 * m.V(1))
  }
end

function caplookfor (p)
  return basiclookfor(p:C())
end

assert(m.match(caplookfor(letter^1), "   4achou123...") == "achou")
a = {m.match(caplookfor(letter^1)^0, " two words, one more  ")}
checkeq(a, {"two", "words", "one", "more"})

assert(m.match( basiclookfor((#m.P(b) * 1) * m.Cp()), "  (  (a)") == 7)

assert(m.match(caplookfor(m.utf8("digit")^1), "  éção46") == "46")

a = {m.match(m.C(digit^1 * m.Cc"d") + m.C(letter^1 * m.Cc"l"), "123")}
checkeq(a, {"123", "d"})

a = {m.match(m.C(digit^1 * m.Cc"d") + m.C(letter^1 * m.Cc"l"), "abcd")}
checkeq(a, {"abcd", "l"})

a = {m.match(m.Cp() * letter^1 * m.Cp(), "abcd")}
checkeq(a, {1, 5})


t = {m.match({[1] = m.C(m.C(1) * m.V(1) + -1)}, "abc")}
checkeq(t, {"abc", "a", "bc", "b", "c", "c", ""})


-- test for small capture boundary
for i = 250,260 do
  assert(#m.match(m.C(i), string.rep('a', i)) == i)
  assert(#m.match(m.C(m.C(i)), string.rep('a', i)) == i)
end


-- test for alternation optimization
assert(m.match(m.P"a"^1 + "ab" + m.P"x"^0, "ab") == 2)
assert(m.match((m.P"a"^1 + "ab" + m.P"x"^0 * 1)^0, "ab") == 3)
assert(m.match(m.P"ab" + "cd" + "" + "cy" + "ak", "98") == 1)
assert(m.match(m.P"ab" + "cd" + "ax" + "cy", "ax") == 3)
assert(m.match((m.P"ab" + "cd" + "ax" + "cy")^0, "ax") == 3)
assert(m.match(m.P(1) * "x" + m.S"" * "xu" + "ay", "ay"))
assert(m.match(m.P"abc" + "cde" + "aka", "aka"))
assert(m.match(m.S"abc" * "x" + "cde" + "aka", "ax"))
assert(m.match(m.S"abc" * "x" + "cde" + "aka", "aka"))
assert(m.match(m.S"abc" * "x" + "cde" + "aka", "cde"))
assert(m.match(m.S"abc" * "x" + "ide" + m.S"ab" * "ka", "aka"))
assert(m.match(m.P(1) * "x" + "cde" + m.S"ab" * "ka", "aka"))
assert(m.match(m.P(1) * "x" + "cde" + m.P(1) * "ka", "aka"))
assert(m.match(m.P(1) * "x" + "cde" + m.P(1) * "ka", "cde"))
assert(m.match(m.P"eb" + "cd" + m.P"e"^0 + "x", "ee") == 3)
assert(m.match(m.P"ab" + "cd" + m.P"e"^0 + "x", "abcd") == 3)
assert(m.match(m.P"ab" + "cd" + m.P"e"^0 + "x", "eeex") == 4)
assert(m.match(m.P"ab" + "cd" + m.P"e"^0 + "x", "cd") == 3)
assert(m.match(m.P"ab" + "cd" + m.P"e"^0 + "x", "x") == 1)
assert(m.match(m.P"ab" + "cd" + m.P"e"^0 + "x" + "", "zee") == 1)
assert(m.match(m.P"ab" + "cd" + m.P"e"^1 + "x", "abcd") == 3)
assert(m.match(m.P"ab" + "cd" + m.P"e"^1 + "x", "eeex") == 4)
assert(m.match(m.P"ab" + "cd" + m.P"e"^1 + "x", "cd") == 3)
assert(m.match(m.P"ab" + "cd" + m.P"e"^1 + "x", "x") == 2)
assert(m.match(m.P"ab" + "cd" + m.P"e"^1 + "x" + "", "zee") == 1)

pi = "3.14159 26535 89793 23846 26433 83279 50288 41971 69399 37510"
assert(m.match(m.Cs((m.P"1" / "a" + m.P"5" / "b" + m.P"9" / "c" + 1)^0), pi) ==
  m.match(m.Cs((m.P(1) / {["1"] = "a", ["5"] = "b", ["9"] = "c"})^0), pi))
print"+"


-- test for table captures
t = m.match(m.Ct(letter^1), "alo")
checkeq(t, {})

t, n = m.match(m.Ct(m.C(letter)^1) * m.Cc"t", "alo")
assert(n == "t" and table.concat(t) == "alo")

t = m.match(m.Ct(m.C(m.C(letter)^1)), "alo")
assert(table.concat(t, ";") == "alo;a;l;o")

t = m.match(m.Ct(m.C(m.C(letter)^1)), "alo")
assert(table.concat(t, ";") == "alo;a;l;o")

t = m.match(m.Ct(m.Ct((m.Cp() * letter * m.Cp())^1)), "alo")
assert(table.concat(t[1], ";") == "1;2;2;3;3;4")

t = m.match(m.Ct(m.C(m.C(1) * 1 * m.C(1))), "alo")
checkeq(t, {"alo", "a", "o"})



-- test for non-pattern as arguments to pattern functions

p = { ('a' * m.V(1))^-1 } * m.P'b' * { 'a' * m.V(2); m.V(1)^-1 }
assert(m.match(p, "aaabaac") == 7)


-- test for errors
assert(not pcall(m.match, "a", { m.V(1) * 'a' }))
assert(not pcall(m.match, string.rep("a", 10000), m.C('a')^0))
assert(not pcall(m.match, "", m.V(1)))   -- open grammar

t = m.match(m.Ct(m.C('a')^0), string.rep("a", 10000))
assert(#t == 10000 and t[1] == 'a' and t[#t] == 'a')

print('+')


local V = m.V

local Space = m.S(" \n\t")^0
local Number = m.C(m.R("09")^1) * Space
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
  assert(m.match(G, s) == loadstring("return "..s)())
end


-- test for grammars (errors deep in calling non-terminals)
g = m.P{
  [1] = m.V(2) + "a",
  [2] = "a" * m.V(3) * "x",
  [3] = "b" * m.V(3) + "c"
}

assert(m.match(g, "abbbcx") == 7)
assert(m.match(g, "abbbbx") == 2)


-- tests for \0
assert(m.match(m.R("\0\1")^1, "\0\1\0") == 4)
assert(m.match(m.S("\0\1ab")^1, "\0\1\0a") == 5)
assert(m.match(m.P(1)^3, "\0\1\0a") == 5)
assert(not m.match(-4, "\0\1\0a"))
assert(m.match("\0\1\0a", "\0\1\0a") == 5)


-- tests for predicates
assert(not m.match(-m.P("a") * 2, "alo"))
assert(m.match(- -m.P("a") * 2, "alo") == 3)
assert(m.match(#m.P("a") * 2, "alo") == 3)
assert(m.match(##m.P("a") * 2, "alo") == 3)
assert(not m.match(##m.P("c") * 2, "alo"))
assert(m.match(m.Cs((##m.P("a") * 1 + m.P(1)/".")^0), "aloal") == "a..a.")
assert(m.match(m.Cs((#((#m.P"a")/"") * 1 + m.P(1)/".")^0), "aloal") == "a..a.")
assert(m.match(m.Cs((- -m.P("a") * 1 + m.P(1)/".")^0), "aloal") == "a..a.")
assert(m.match(m.Cs((-((-m.P"a")/"") * 1 + m.P(1)/".")^0), "aloal") == "a..a.")


-- tests for optional start position
assert(m.match("a", "abc", 1))
assert(m.match("b", "abc", 2))
assert(m.match("c", "abc", 3))
assert(not m.match(1, "abc", 4))
assert(m.match("a", "abc", -3))
assert(m.match("b", "abc", -2))
assert(m.match("c", "abc", -1))
assert(m.match("abc", "abc", -4))   -- truncate to position 1

assert(m.match("", "abc", 10))   -- empty string is everywhere!
assert(m.match("", "", 10))
assert(not m.match(1, "", 1))
assert(not m.match(1, "", -1))
assert(not m.match(1, "", 0))


-- basic tests for utf8
-- break a UTF8 string into characters

c = "君が Ελληνικά"

u = m.Ct((m.Cp() * m.utf8())^0)

t = (m.match(u, c))
assert(#t == 11 and t[4] - t[1] == string.len("君が ") and
                    t[5] - t[4] == string.len("Ε"))

print("+")


-- tests for Lua functions

t = {}
s = ""
p = function (s1, i) assert(s == s1); t[#t + 1] = i end
s = "hi, this is a test"
assert(m.match(((p - m.P(-1)) + 2)^0, s) == string.len(s) + 1)
assert(#t == string.len(s)/2 and t[1] == 1 and t[2] == 3)

assert(not m.match(p, s))

p = mt.__add(function (s, i) return i end, function (s, i) return null end)
assert(m.match(p, "alo"))

p = mt.__mul(function (s, i) return i end, function (s, i) return null end)
assert(not m.match(p, "alo"))


t = {}
p = function (s1, i) assert(s == s1); t[#t + 1] = i; return i end
s = "hi, this is a test"
assert(m.match((m.P(1) * p)^0, s) == string.len(s) + 1)
assert(#t == string.len(s) and t[1] == 2 and t[2] == 3)

t = {}
p = m.P(function (s1, i) assert(s == s1); t[#t + 1] = i; return i + 1 end)
s = "hi, this is a test"
assert(m.match(p^0, s) == string.len(s) + 1)
assert(#t == string.len(s) + 1 and t[1] == 1 and t[2] == 2)

p = function (s1, i) return m.match(m.P"a"^0, s1, i) end
assert(m.match(p, "aaaa") == 5)
assert(m.match(p, "baaa") == 1)

assert(not m.match(function () return 2^20 end, s))
assert(not m.match(m.P(function () return 0 end), s))
assert(not m.match(m.P(1)^0 * function (_, i) return i - 1 end, s))
assert(m.match(m.P(1)^0 * function (_, i) return i end, s) ==
       string.len(s) + 1)
for i = 1, string.len(s) + 1 do
  assert(m.match(function (_, _) return i end, s) == i)
end


-- tests for Function Replacements
f = function (a, ...) if a ~= "x" then return {a, ...} end end

t = m.match(m.C(1)^0/f, "abc")
checkeq(t, {"a", "b", "c"})

t = m.match(m.C(1)^0/f/f, "abc")
checkeq(t, {{"a", "b", "c"}})

t = m.match(m.P(1)^0/f/f, "abc")   -- no capture
checkeq(t, {{"abc"}})

t = m.match((m.P(1)^0/f * m.Cp())/f, "abc")
checkeq(t, {{"abc"}, 4})

t = m.match((m.C(1)^0/f * m.Cp())/f, "abc")
checkeq(t, {{"a", "b", "c"}, 4})

t = m.match((m.C(1)^0/f * m.Cp())/f, "xbc")
checkeq(t, {4})

t = m.match(m.C(m.C(1)^0)/f, "abc")
checkeq(t, {"abc", "a", "b", "c"})


t = {m.match((m.C(1) / function (x) return x, x.."x" end)^0, "abc")}
checkeq(t, {"a", "ax", "b", "bx", "c", "cx"})

t = m.match(m.Ct((m.C(1) / function (x,y) return y, x end * m.Cc(1))^0), "abc")
checkeq(t, {nil, "a", 1, nil, "b", 1, nil, "c", 1})

-- tests for Query Replacements

assert(m.match(m.C(m.C(1)^0)/{abc = 10}, "abc") == 10)
assert(m.match(m.C(1)^0/{a = 10}, "abc") == 10)
assert(m.match(m.S("ba")^0/{ab = 40}, "abc") == 40)
t = m.match(m.Ct((m.S("ba")/{a = 40})^0), "abc")
checkeq(t, {40})

assert(m.match(m.Cs((m.C(1)/{a=".", d=".."})^0), "abcdde") == ".bc....e")
assert(m.match(m.Cs((m.C(1)/{f="."})^0), "abcdde") == "abcdde")
assert(m.match(m.Cs((m.C(1)/{d="."})^0), "abcdde") == "abc..e")
assert(m.match(m.Cs((m.C(1)/{e="."})^0), "abcdde") == "abcdd.")
assert(m.match(m.Cs((m.C(1)/{e=".", f="+"})^0), "eefef") == "..+.+")
assert(m.match(m.Cs((m.C(1))^0), "abcdde") == "abcdde")
assert(m.match(m.Cs(m.C(m.C(1)^0)), "abcdde") == "abcdde")
assert(m.match(1 * m.Cs(m.P(1)^0), "abcdde") == "bcdde")
assert(m.match(m.Cs((m.C('0')/'x' + 1)^0), "abcdde") == "abcdde")
assert(m.match(m.Cs((m.C('0')/'x' + 1)^0), "0ab0b0") == "xabxbx")
assert(m.match(m.Cs((m.C('0')/'x' + m.P(1)/{b=3})^0), "b0a0b") == "3xax3")
assert(m.match(m.P(1)/'%0%0'/{aa = -3} * 'x', 'ax') == -3)
assert(m.match(m.C(1)/'%0%1'/{aa = 'z'}/{z = -3} * 'x', 'ax') == -3)

assert(m.match(m.Cs(m.Cc(0) * (m.P(1)/"")), "4321") == "0")

assert(m.match(m.Cs((m.P(1) / "%0")^0), "abcd") == "abcd")
assert(m.match(m.Cs((m.P(1) / "%0.%0")^0), "abcd") == "a.ab.bc.cd.d")
assert(m.match(m.Cs((m.P("a") / "%0.%0" + 1)^0), "abcad") == "a.abca.ad")
assert(m.match(m.C("a") / "%1%%%0", "a") == "a%a")
assert(m.match(m.Cs((m.P(1) / ".xx")^0), "abcd") == ".xx.xx.xx.xx")

assert(not pcall(m.match, "abc", m.P(1)/"%1"))   -- out of range
assert(not pcall(m.match, "abc", m.P(1)/"%9"))   -- out of range
assert(not pcall(m.match, "abc", m.Cp()/"%1"))   -- invalid nesting

function f (x) return x + 1 end
assert(m.match(m.Ca(m.Cc(0) * (m.P(1) / f)^0), "alo alo") == 7)

assert(m.match(m.Cc(print), "") == print)

s = string.rep("12345678901234567890", 20)
assert(m.match(m.C(1)^0 / "%9-%1-%0-%3", s) == "9-1-" .. s .. "-3")

print"+"


-- tests for loop checker

local function haveloop (p)
  assert(not pcall(function (p) return p^0 end, m.P(p)))
end

haveloop(m.P("x")^-4)
assert(m.match(((m.P(0) + 1) * m.S"al")^0, "alo") == 3)
assert(m.match((("x" + #m.P(1))^-4 * m.S"al")^0, "alo") == 3)
haveloop("")
haveloop(m.P("x")^0)
haveloop(m.P("x")^-1)
haveloop(m.P("x") + 1 + 2 + m.P("a")^-1)
haveloop(-m.P("ab"))
haveloop(- -m.P("ab"))
haveloop(# #(m.P("ab") + "xy"))
haveloop(- #m.P("ab")^0)
haveloop(# -m.P("ab")^1)
haveloop(#m.V(3))
haveloop(m.V(3) + m.V(1) + m.P('a')^-1)
haveloop({[1] = m.V(2) * m.V(3), [2] = m.V(3), [3] = m.P(0)})
assert(m.match(m.P{[1] = m.V(2) * m.V(3), [2] = m.V(3), [3] = m.P(1)}^0, "abc")
       == 3)
assert(m.match(m.P""^-3, "a") == 1)

local function find (p, s)
  return m.match(basiclookfor(p), s)
end

local function badgrammar (g, exp)
  local err, msg = pcall(m.P, g)
  assert(not err)
  if exp then assert(find(exp, msg)) end
end

badgrammar({[1] = m.V(1)}, "rule 1")
badgrammar({[1] = m.V(2)}, "non-terminal 2")   -- invalid non-terminal
badgrammar({[1] = #m.P("a") * m.V(1)}, "rule 1")
badgrammar({[1] = -m.P("a") * m.V(1)}, "rule 1")
badgrammar({[1] = -1 * m.V(1)}, "rule 1")
badgrammar({[1] = 1 * m.V(2), [2] = m.V(2)}, "rule 2")
badgrammar({[1] = m.P(0), [2] = 1 * m.V(1)^0}, "loop in rule 2")


print"OK"

