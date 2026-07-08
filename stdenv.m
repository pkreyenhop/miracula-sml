foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs
