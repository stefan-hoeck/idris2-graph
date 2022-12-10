module Main

import Data.BitMap
import Profile

%default total

pairs : Key -> List (Key,String)
pairs k = map (\i => (i, show i)) [1 .. k]

full : Key -> BitMap String
full = fromList . pairs


bench : Benchmark Void
bench = Group "intmap_ops" [
    Group "fromList" [
        Single "1"     (basic BitMap.fromList $ pairs 1)
      , Single "10"    (basic BitMap.fromList $ pairs 10)
      , Single "100"   (basic BitMap.fromList $ pairs 100)
      , Single "1000"  (basic BitMap.fromList $ pairs 1000)
      , Single "10000" (basic BitMap.fromList $ pairs 10000)
      ]
  , Group "lookup" [
        Single "1"     (basic (lookup 333) $ full 1)
      , Single "10"    (basic (lookup 333) $ full 10)
      , Single "100"   (basic (lookup 333) $ full 100)
      , Single "1000"  (basic (lookup 333) $ full 1000)
      , Single "10000" (basic (lookup 333) $ full 10000)
      ]
  , Group "insert" [
        Single "1"     (basic (insert 333 "") $ full 1)
      , Single "10"    (basic (insert 333 "") $ full 10)
      , Single "100"   (basic (insert 333 "") $ full 100)
      , Single "1000"  (basic (insert 333 "") $ full 1000)
      , Single "10000" (basic (insert 333 "") $ full 10000)
      ]
  , Group "delete" [
        Single "1"     (basic (delete 333) $ full 1)
      , Single "10"    (basic (delete 333) $ full 10)
      , Single "100"   (basic (delete 333) $ full 100)
      , Single "1000"  (basic (delete 333) $ full 1000)
      , Single "10000" (basic (delete 333) $ full 10000)
      ]
  ]

main : IO ()
main = runDefault (const True) Table show bench
