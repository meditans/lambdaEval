module ParaEncoding where

import Lib
import Common
import Prelude hiding ((^))

-- * Derivation of the paramorphic encoding

-- The point of these encodings is that you representing the data by the behavior
-- that you otherwise would've had to define instead of defining both:

-- - a first order representation
-- - a way of converting that to computational behavior

-- You just represent the data as the behavior you would've gotten via the
-- conversion. So, in Haskell, the behavior would be:

-- #+BEGIN_EXAMPLE
-- paraNat :: Nat -> r -> (Nat -> r -> r) -> r
-- paraNat Zero    z s = z
-- paraNat (Suc n) z s = s n (paraNat n)
-- #+END_EXAMPLE

-- So, keeping in mind that the data is the behavior, we end defining:
-- #+BEGIN_EXAMPLE
-- zero   = paraNat Zero    = \z s -> z
-- suc n  = paraNat (Suc n) = \z s -> s n (n z s)
-- #+END_EXAMPLE

-- Now we can also define

-- #+BEGIN_EXAMPLE
-- pred n = paraNat n Zero (\n' _ -> n')
-- #+END_EXAMPLE

-- Let's also notice that in these encodings, the "higher order function", like
-- ~paraNat~ in this case, is essentially (modulo order) the identity function,
-- because we encoded the computational informations in the representation of the
-- number.

-- ** Zero
zero = z ^ s ^ z
suc  = n ^ z ^ s ^ (s # n # (n # z # s))

one   = eval $ suc # zero
two   = eval $ suc # one
three = eval $ suc # two
four  = eval $ suc # three

frst = a ^ b ^ a

-- * Unrelated
-- paraList :: [a] -> r -> (a -> [a] -> r -> r) -> r
-- paraList [] n c = n
-- paraList (x:xs) n c = c x xs (paraList n c xs)
