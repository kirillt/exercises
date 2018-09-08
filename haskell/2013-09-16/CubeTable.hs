cubeTable :: Integer -> [(Integer, Integer)]
cubeTable n = [ (i,i^3) | i <- [1..n] ]
