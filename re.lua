local m = require"lpeg"
local _G = _G
local concat = table.concat

module "re"

local function union (a,b) return a+b end
local function concat (a,b) return a*b end

local Char = ("%" * m.C(1)) / "%1" + m.C(1)
local S = m.S(" \t")^0

local Literal = "'" * m.Cs((Char - "'")^0) / m.P * "'" +
                '"' * m.Cs((Char - '"')^0) / m.P * '"'

local Interval = (Char * "-" * Char) / m.R

local Class = "[" *
           m.Ca(m.Cc(m.S"") * ((Interval + Char) / union - "]")^0) *
              "]"


local Exp, Seq, Prefix, Sufix, Primary = 1, 2, 3, 4, 5
local g = m.P{
  [Exp] = m.Ca(m.V(Seq) * ("/" * S * m.V(Seq) / union)^0);
  [Seq] = m.Ca(m.Cc(m.P"") * (m.V(Prefix) / concat)^0);
  [Prefix] = "&" * S * m.V(Sufix) / function (p) return #p end
           + "!" * S * m.V(Sufix) / function (p) return -p end
           + m.V(Sufix);
  [Sufix] = m.Ca(m.V(Primary) *
            ( m.P"+" / function (p) return p^1 end
            + m.P"*" / function (p) return p^0 end
            + m.P"?" / function (p) return p^-1 end
            + "" )) * S;
  [Primary] = ("(" * S * m.V(Exp) * ")"
            + m.P"{}" / function () return m.Cp() end
            + "{" * S * m.V(Exp) * "}" / m.C
            + Literal
            + Class
            + m.P"." / function () return m.P(1) end) * S;
}

g = S * g * -1


local mem = {}
_G.setmetatable(mem, {__mode = "v"})

function compile (p)
  local cp = mem[p]
  if not cp then
    cp = m.match(p, g)
    if not cp then _G.error("incorrect pattern", 3) end
    mem[p] = cp
  end
  return cp
end

function match (s, p)
  return m.match(s, compile(p))
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
