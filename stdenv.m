foldl f z []     = z
foldl f z (x:xs) = foldl f (f z x) xs

converse f a b = f b a

reverse = foldl (converse(:)) []


