module Test.BitMap

import Control.Monad.Identity
import Data.List
import Data.SortedMap as SM
import Data.BitMap as IM
import Hedgehog

--------------------------------------------------------------------------------
--          Generators
--------------------------------------------------------------------------------

anyKey : Gen Key
anyKey = bits64 (linear 0 0xffff_ffff_ffff_ffff)

smallKey : Gen Key
smallKey = bits64 (linear 0 0xf)

largeKey : Gen Key
largeKey = bits64 (linear 0xffff_ffff 0xffff_ffff_ffff)

pair : Gen (Key, Char)
pair = [| MkPair anyKey alpha |]

smallPair : Gen (Key, Char)
smallPair = [| MkPair smallKey alpha |]

largePair : Gen (Key, Char)
largePair = [| MkPair largeKey alpha |]

pairs : Gen $ List (Key, Char)
pairs = list (linear 0 30) pair

smallPairs : Gen $ List (Key, Char)
smallPairs = list (linear 0 30) smallPair

largePairs : Gen $ List (Key, Char)
largePairs = list (linear 0 30) largePair

bitMap : Gen $ BitMap Char
bitMap = fromList <$> pairs

smallIntMap : Gen $ BitMap Char
smallIntMap = fromList <$> smallPairs

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

empty_lookup : Property
empty_lookup = property $ do
  k <- forAll anyKey
  IM.lookup k (empty {v = Char}) === Nothing

singleton_lookup : Property
singleton_lookup = property $ do
  (k,v) <- forAll pair
  IM.lookup k (singleton k v) === Just v

insert_lookup : Property
insert_lookup = property $ do
  ((k,v),m) <- forAll [| MkPair pair bitMap |]
  lookup k (insert k v m) === Just v

insertWith_lookup : Property
insertWith_lookup = property $ do
  ((k,v),m) <- forAll [| MkPair smallPair smallIntMap |]
  lookup k (insertWith (\_,v2 => v2) k v m) ===
  (lookup k m <|> Just v)

update_lookup : Property
update_lookup = property $ do
  (k,m) <- forAll [| MkPair smallKey smallIntMap |]
  lookup k (update k toUpper m) === (toUpper <$> lookup k m)

decomp_lookup_old : Property
decomp_lookup_old = property $ do
  m <- forAll bitMap
  case decomp m of
    NoMatch      => True === True
    Match k v m2 => lookup k m === Just v

decomp_lookup_new : Property
decomp_lookup_new = property $ do
  m <- forAll bitMap
  case decomp m of
    NoMatch      => True === True
    Match k v m2 => lookup k m2 === Nothing

decomp_insert : Property
decomp_insert = property $ do
  m <- forAll bitMap
  case decomp m of
    NoMatch      => True === True
    Match k v m2 => m === insert k v m2

delete_lookup : Property
delete_lookup = property $ do
  (k,m) <- forAll [| MkPair smallKey smallIntMap |]
  lookup k (delete k m) === Nothing

map_id : Property
map_id = property $ do
  m <- forAll bitMap
  m === map id m

traverse_id : Property
traverse_id = property $ do
  m <- forAll bitMap
  Id m === traverse Id m

--------------------------------------------------------------------------------
--          props
--------------------------------------------------------------------------------

export
props : Group
props = MkGroup "BitMap Properties"
          [ ("empty_lookup", empty_lookup)
          , ("singleton_lookup", singleton_lookup)
          , ("insert_lookup", insert_lookup)
          , ("insertWith_lookup", insertWith_lookup)
          , ("update_lookup", update_lookup)
          , ("delete_lookup", delete_lookup)
          , ("decomp_lookup_old", decomp_lookup_old)
          , ("decomp_lookup_new", decomp_lookup_new)
          , ("decomp_insert", decomp_insert)
          , ("map_id", map_id)
          , ("traverse_id", traverse_id)
          ]

