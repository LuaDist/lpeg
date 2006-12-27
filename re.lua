local m = require"lpeg"
local _G = _G
local concat = table.concat

module "re"


local EOS = -1

local Char = "%" * m.C(1) + m.C(1)
local S = m.S(" \t")^0

local Special = m.S"\"\'./()[]{}"

local Literal = "'" * (Char - "'")^0 * "'" +
                '"' * (Char - '"')^0 * '"'

local Interval = m.T(Char * "-" * Char)
local Class = "[" * ((Interval + Char) - "]")^0 * "]"

local OPEN = "(" * S
local CLOSE = ")" * S

local g = {
  [1] = m.T(m.V(2)) * ("/" * S * m.T(m.V(2)))^0,  -- Expression
  [2] = m.T(m.V(3))^0,  -- Sequence
  [3] = m.C(m.S"&!" + "", "pre") * S * m.T(m.V(4), "suf"),  -- Prefix
  [4] = m.T(m.V(5), "pri") * m.C(m.S"*+?" + "", "pos") * S,  -- Suffix
  [5] =   (OPEN * m.T(m.V(1), "E") * CLOSE +    -- Primary
          m.T(Literal + (Char - Special), "L") +
          m.T(Class, "C") +
          m.C(".", "A")) * S,
}

g = S * m.T(g) * EOS

local expression

local prim = {}


function prim.L (t)
  return m.P(concat(t))
end

function prim.C (t)
  local s = m.S""
  local neg = false
  local start = 1
  if t[1] == "^" then start = 2; neg = true end
  for i = start, #t do
    local e = t[i]
    if _G.type(e) == "string" then
      s = s + m.S(e)
    else
      s = s + m.R(e[1], e[2])
    end
  end
  if neg then s = 1 - s end
  return s
end

prim.E = function (x) return expression(x) end
prim.A = function () return m.P(1) end

local function primary (t)
  local k, v = _G.next(t)
  return prim[k](v)
end


local function suffix (t)
  local p = primary(t.pri)
  if t.pos == "*" then p = p^0
  elseif t.pos == "+" then p = p^1
  elseif t.pos == "?" then p = p + ""
  end
  return p
end

local function prefix (t)
  local p = suffix(t.suf)
  if t.pre == "&" then p = #p
  elseif t.pre == "!" then p = -p
  end
  return p
end

local function sequence (t)
  local p = m.P""
  for i = 1, #t do
    p = p * prefix(t[i])
  end
  return p
end

local function expression (t)
  local p = sequence(t[1])
  for i = 2, #t do
    p = p + sequence(t[i])
  end
  return p
end

local mem = {}
_G.setmetatable(mem, {__mode = "v"})

function match (s, p)
  local cp = mem[p]
  if not cp then
    local t = m.match(p, g)
    if not t then _G.error("incorrect pattern", 2) end
    cp = expression(t)
    mem[p] = cp
  end
  return m.match(s, cp)
end

_G.print(match("alo 894", "'b' / [a-%z]* ' ' [1-789]+"))
