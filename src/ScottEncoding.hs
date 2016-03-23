module ScottEncoding where

import Prelude hiding ((^), const, sum)

import Lib
import Common

i0 = z ^ s ^ z
i1 = eval $ suc # i0
i2 = eval $ suc # i1
i3 = eval $ suc # i2
i4 = eval $ suc # i3
i5 = eval $ suc # i4
i6 = eval $ suc # i5

is = i0 : map (\t -> eval $ suc # t) is
ii n = is !! n

suc = n ^ z ^ s ^ s # n

natCase = (z ^ z)

inn = caseSplit # (const # i0) # suc
out = n ^ n # (inl # unit) # inr

-- natRec = fix # (f ^ n ^ z ^ s ^ natCase # n # z # (r ^ s # (f # r # s # z)))

fix = f ^ (x ^ f # (x # x)) # (x ^ f # (x # x))

fNat = f ^ funPlus # (i ^ i) # f

phi = caseSplit # (const # i0) # (comp # suc # suc)

cata = p ^ (fix # (f ^ comp3 # p # (fNat # f) # out))

sum = n ^ m ^ (cata # (caseSplit # (const # n) # suc)) # m

prod = n ^ m ^ (cata # (caseSplit # (const # i0) # (sum # n))) # m

-- Cosa succederebbe se provassi comunque a definire il predecessore come catamorfismo?
predCata = cata # (fNat # inn)
