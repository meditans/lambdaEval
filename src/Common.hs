module Common where

import Lib
import Prelude hiding ((^), const, id)

unit = make_var "unit"

const = x ^ y ^ x
id = z ^ z

couple = (a ^ b ^ x ^ (x # a # b))
pi1 = (a ^ a # (x ^ y ^ x))
pi2 = (a ^ a # (x ^ y ^ y))

inl = (a ^ x ^ y ^ x # a)
inr = (a ^ x ^ y ^ y # a)

-- caseSplit viene di solito indicato con [...]
caseSplit = (f ^ g ^ a ^ a # f # g)
-- funPlus viene di solito indicato con f + g
funPlus = (f ^ g ^ a ^ x ^ y ^ a # (a ^ x # (f # a)) # (a ^ y # (g # a)))

-- split viene di solito indicato con <...>
split = (f ^ g ^ a ^ x ^ x # (f # a) # (g # a))
-- funTimes viene di solito indicato con f x g
funTimes = (f ^ g ^ a ^ a # (i ^ j ^ x ^ x # (f # i) # (g # j)))

comp = f ^ g ^ x ^ f # (g # x)
comp3 = f ^ g ^ h ^ x ^ f # (g # (h # x))

