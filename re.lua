local m = require"lpeg"
local _G = _G
local print = _G.print
local mt = getmetatable(m.P(0))

local I = m.P(function (s,i) print(i, s:sub(1, i-1)); return i end)

module "re"

local function complement (p) return 1 - p end

local function optapply (f, v) return v and f(v) or f end


local S = (m.S(" \t\n") + "#" * (1 - m.S"\n")^0)^0

local Char = ("%" * m.C(1)) / "%1" + m.C(1)

local Literal = "'" * m.Cs((Char - "'")^0) / m.P * "'" +
                '"' * m.Cs((Char - '"')^0) / m.P * '"'

local Range = m.Cs(Char * (m.P"-"/"") * Char) / m.R

local Class =
    "["
  * ("^" * m.Cc(complement))^-1   -- optional complement symbol
  * m.Ca(m.Cc(m.S"") * ((Range + Char) / mt.__add - "]")^0) / optapply
  * "]"

local Identifier = m.R("AZ", "az", "__") * m.R("AZ", "az", "__", "09")^0


local exp = m.P{ "Exp",
  Exp = m.Ca(m.V"Seq" * ("/" * S * m.V"Seq" / mt.__add)^0);
  Seq = m.Ca(m.Cc(m.P"") * (m.V"Prefix" / mt.__mul)^0);
  Prefix = "&" * S * m.V"Sufix" / mt.__len
         + "!" * S * m.V"Sufix" / mt.__unm
         + m.V"Sufix";
  Sufix = m.Ca(m.V"Primary" *
          ( m.P"+" * m.Cc(1) / mt.__pow    -- primary^1
            + m.P"*" * m.Cc(0) / mt.__pow    -- primary^0
            + m.P"?" * m.Cc(-1) / mt.__pow   -- primary^-1
            + ""
            ) ) * S;
  Primary = ( "(" * S * m.V"Exp" * ")"
            + m.P"{}" / m.Cp
            + "{" * S * m.V"Exp" * "}" / m.C
            + Literal
            + Class
            + m.P"." * m.Cc(m.P(1))
            + Identifier * -(S * '<-') / m.V
            ) * S;
}


local definition = m.C(Identifier) * S * '<-' * S * exp

local grammar = m.Ca(
     definition / function (n, r) return {n; [n] = r} end
   * (definition / _G.rawset)^0
)

grammar = S * grammar / m.P * -1

local pattern = S * (grammar + exp) / m.P * -1
                                   


local mem = {}
_G.setmetatable(mem, {__mode = "v"})

function compile (p)
  local cp = mem[p]
  if not cp then
    cp = pattern:match(p)
    if not cp then _G.error("incorrect pattern", 3) end
    mem[p] = cp
  end
  return cp
end

function match (s, p)
  return compile(p):match(s)
end

