levels :: Tree[a] -> [[a]] 
levels (Nd a bs) = a : foldr (zipWith' (++) []) [](map levels bs) 

zipWith' f xs [] = xs 
zipWith' f [] xs = xs 
zipWith' f  (x:xs)  (y:ys) = f x y : zipWith'f xs ys


levels' (Nd a bs) = [a] : foldr (zipWith' (++)) [] (map levels' bs) 

