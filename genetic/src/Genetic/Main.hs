import Utils.Misc
import Utils.Distance
import Genetic.Atom
import Genetic.Individ
import Genetic.Population

import System.Random

target  :: Individ
target    = map Atom "Hello, world!"

fitness :: Individ -> Int
fitness   = distance target

-- Interleave elements of individs.
-- It reduces length of output individ
-- because of `evens' and `odds' usage.
cross   :: Individ -> Individ -> Individ
cross l r = alternate (odds l) (odds r)

-- Since `cross' can only reduce length of individ
-- we have to balance it with mutations which increase
-- length of individ.
mutate  :: RandomGen g => g -> Individ -> (Individ,g)
mutate    = undefined

main :: IO ()
main = do
    return ()
