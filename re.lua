local m = require"lpeg"
local _G = _G
local mt = getmetatable(m.P(0))

module "re"

local Char = ("%" * m.C(1)) / "%1" + m.C(1)
local S = m.S(" \t")^0

local Literal = "'" * m.Cs((Char - "'")^0) / m.P * "'" +
                '"' * m.Cs((Char - '"')^0) / m.P * '"'

local Interval = m.Cs(Char * (m.P"-"/"") * Char) / m.R

local Class = "[" *
           m.Ca(m.Cc(m.S"") * ((Interval + Char) / mt.__add - "]")^0) *
              "]"


local Exp, Seq, Prefix, Sufix, Primary = 1, 2, 3, 4, 5
local g = m.P{
  [Exp] = m.Ca(m.V(Seq) * ("/" * S * m.V(Seq) / mt.__add)^0);
  [Seq] = m.Ca(m.Cc(m.P"") * (m.V(Prefix) / mt.__mul)^0);
  [Prefix] = "&" * S * m.V(Sufix) / mt.__len
           + "!" * S * m.V(Sufix) / mt.__unm
           + m.V(Sufix);
  [Sufix] = m.Ca(m.V(Primary) *
            ( m.P"+" * m.Cc(1) / mt.__pow    -- primary^1
            + m.P"*" * m.Cc(0) / mt.__pow    -- primary^0
            + m.P"?" * m.Cc(-1) / mt.__pow   -- primary^-1
            + ""
            ) ) * S;
  [Primary] =
            ( "(" * S * m.V(Exp) * ")"
            + m.P"{}" / m.Cp
            + "{" * S * m.V(Exp) * "}" / m.C
            + Literal
            + Class
            + m.P"." * m.Cc(1) / m.P     -- m.P(1)
            ) * S;
}

g = S * g * -1


local mem = {}
_G.setmetatable(mem, {__mode = "v"})

function compile (p)
  local cp = mem[p]
  if not cp then
    cp = g:match(p)
    if not cp then _G.error("incorrect pattern", 3) end
    mem[p] = cp
  end
  return cp
end

function match (s, p)
  return compile(p):match(s)
end

function test ()   -- basic tests
  local assert = _G.assert
  assert(match("a", ".") == 2)
  assert(match("a", "") == 1)
  assert(match("", "!.") == 1)
  assert(not match("a", " ! . "))
  assert(match("abcde", "  ( . . ) * ") == 5)
  assert(match("abbcde", " [a-c] +") == 5)
  assert(match("abbc--", " [%a-%c] +") == 5)
  assert(match("abbc--", " [a%-%c] +") == 2)
  assert(match("abbc--", " [a%-%cb] + ") == 7)
  assert(not match("abbcde", " [b-z] + "))
  assert(match("abb\"de", '"abb%"de"') == 7)
  assert(match("abceeef", "'ac'? 'ab'* 'c' {'e'*} / 'abceeef' ") == "eee")
  assert(match("abceeef", "'ac'? 'ab'* 'c' { 'f'+ } / 'abceeef' ") == 8)
  local t = {match("abceefe", "((&'e' {})? .)*")}
  assert(t[1] == 4 and t[2] == 5 and t[3] == 7 and t[4] == nil)
  _G.print"OK"
end

test()
