import Test.QuickCheck

eqi [] [] = True
eqi (x : xs) (y : ys) = (x == y) && eqi xs ys
eqi _ _ = False

zeros = 0 : zeros
ones = 1 : ones
ones' = map succ zeros


prop_eq :: [Integer] -> [Integer] -> Property
prop_eq xs ys =
  eqi xs ys ==> (xs == ys)


prop_d :: [Int] -> Int -> Property
prop_d xs n =
  not (null xs) && n >= 0 ==>
  take n (cycle xs) == take n (cycle $ xs ++ xs)

main = quickCheck prop_d

prop_o :: Int -> Property
prop_o n =
  n >= 0 ==> take n ones == take n zeros
