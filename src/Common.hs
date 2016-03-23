module Common where

import Lib
import Prelude hiding ((^), const)

unit = make_var "unit"

const = x ^ y ^ x

couple = (a ^ b ^ x ^ (x # a # b))
pi1 = (a ^ a # (x ^ y ^ x))
pi2 = (a ^ a # (x ^ y ^ y))

inl = (a ^ x ^ y ^ x # a)
inr = (a ^ x ^ y ^ y # a)

caseSplit = (f ^ g ^ a ^ a # f # g)
funPlus = (f ^ g ^ a ^ x ^ y ^ a # (a ^ x # (f # a)) # (a ^ y # (g # a)))

split = (f ^ g ^ a ^ x ^ x # (f # a) # (g # a))
funTimes = (f ^ g ^ a ^ a # (i ^ j ^ x ^ x # (f # i) # (g # j)))

comp = f ^ g ^ x ^ f # (g # x)
comp3 = f ^ g ^ h ^ x ^ f # (g # (h # x))
