type Point = (Integer, Integer)

isosc :: Point -> Point -> Point -> Bool
isosc a b c = dist a b == dist b c ||
              dist b c == dist c a ||
              dist c a == dist a b
    where
        dist (x1,x2) (y1,y2) = (x1-x2)^2 + (y1-y2)^2
