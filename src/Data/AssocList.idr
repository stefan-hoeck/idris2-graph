module Data.AssocList

import Data.DPair
import Data.Prim.Bits32
import Data.Maybe.Upper

%default total

public export
0 Key : Type
Key = Bits32

public export
0 (<): Maybe Key -> Maybe Key -> Type
(<) = Upper (<)

public export
0 (<=): Maybe Key -> Maybe Key -> Type
(<=) = ReflexiveClosure (<)

||| A provably sorted assoc list with `Bits64` as the key type.
|||
||| This is mainly useful for short sequences of key / value pairs.
||| It comes with O(n) runtime complexity for `insert`, `update`,
||| `lookup` and `delete`, but also with fast O(n) complexity for
||| `union` and `intersection`.
public export
data AL : (ix : Maybe Key) -> Type -> Type where
  Nil : AL Nothing a
  (::) :  {0 ix : _}
       -> (p     : (Key,a))
       -> (ps    : AL ix a)
       -> (0 prf : Just (fst p) < ix)
       => AL (Just $ fst p) a

public export
Functor (AL ix) where
  map f []       = []
  map f ((k,v) :: t) = (k,f v) :: map f t

public export
foldlKV_ : (acc -> (Key,el) -> acc) -> acc -> AL m el -> acc
foldlKV_ f x (p :: ps) = foldlKV_ f (f x p) ps
foldlKV_ _ x []        = x

public export
traverseKV_ : Applicative f => ((Key,a) -> f b) -> AL m a -> f (AL m b)
traverseKV_ g []             = pure []
traverseKV_ g (p :: ps) =
  [| (\vb,ps' => (fst p,vb) :: ps') (g p) (traverseKV_ g ps) |]


public export
Foldable (AL ix) where
  foldr c n [] = n
  foldr c n (x::xs) = c (snd x) (foldr c n xs)

  foldl f q [] = q
  foldl f q (x::xs) = foldl f (f q $ snd x) xs

  null [] = True
  null (_::_) = False

  foldMap f = foldl (\acc, elem => acc <+> f elem) neutral

public export
Traversable (AL ix) where
  traverse f [] = pure []
  traverse f (p :: ps) =
    (\v,qs => (fst p,v) :: qs) <$> f (snd p) <*> traverse f ps

||| Lookup a key in an assoc list.
public export
lookup_ : (k : Key) -> AL ix a -> Maybe a
lookup_ k (p :: ps) = case comp k (fst p) of
  LT _ _ _ => Nothing
  EQ _ _ _ => Just $ snd p
  GT _ _ _ => lookup_ k ps
lookup_ _ []        = Nothing

public export
nonEmpty_ : AL m a -> Bool
nonEmpty_ (p :: ps) = True
nonEmpty_ []        = False

public export
isEmpty_ : AL m a -> Bool
isEmpty_ (p :: ps) = False
isEmpty_ []        = True

||| Extracts the key / value pairs from the assoc list.
public export
pairs_ : AL ix a -> List (Key,a)
pairs_ (p :: ps) = p :: pairs_ ps
pairs_ []        = []

||| Extracts the keys from the assoc list.
public export
keys_ : AL ix a -> List Key
keys_ (p :: ps) = fst p :: keys_ ps
keys_ []        = []

||| Extracts the values from the assoc list.
public export
values_ : AL ix a -> List a
values_ (p :: ps) = snd p :: values_ ps
values_ []        = []

public export
length_ : AL ix a -> Nat
length_ (p :: ps) = S $ length_ ps
length_ []        = 0

||| Heterogeneous equality check.
public export
heq : Eq a => AL m a -> AL n a -> Bool
heq (p :: ps) (q :: qs) = p == q && heq ps qs
heq [] [] = True
heq _ _   = False

public export %inline
Eq a => Eq (AL m a) where
  (==) = heq

export %inline
Show a => Show (AL m a) where
  showPrec p m = showPrec p (pairs_ m)

--------------------------------------------------------------------------------
--          Insert
--------------------------------------------------------------------------------

||| Inserting a new key / value pair leads to a new assoc list where the
||| key at the head is either equal to the new key or the one previously
||| at the head.
|||
||| @ k  New key that was inserted
||| @ mk Key index of the original assoc list
public export
record InsertRes (k : Key) (mk : Maybe Key) (a : Type) where
  constructor IR
  pairs : AL (Just x) a
  0 prf : Either (x === k) (Just x === mk)

0 prependLemma :
     {x,y,k : Key}
  -> {mk : Maybe Key}
  -> Either (x === k) (Just x === mk)
  -> (0 ltyk : Just y < Just k)
  => (0 ltym : Just y < mk)
  => Just y < Just x
prependLemma (Left Refl) = ltyk
prependLemma (Right z)   = rewrite z in ltym

%inline
prepend :
     (p : (Key,a))
  -> InsertRes k mk a
  -> (0 lt : Just (fst p) < Just k)
  => (0 sm : Just (fst p) < mk)
  => InsertRes k (Just $ fst p) a
prepend p (IR ps prf1) =
  let 0 prf = prependLemma prf1
   in IR (p :: ps) (Right Refl)

||| Inserts a new key / value pair into an assoc list.
||| The result type reflects the possibilities with regard
||| to the head pair of the new assoc list.
|||
||| Note: If the given key `k` is already present in the assoc list,
||| its associated value will be replaced with `v`.
public export
insert_ : (k : Key) -> (v : a) -> AL ix a -> InsertRes k ix a
insert_ k v (p :: ps) = case comp k (fst p) of
  LT prf _ _ => IR ((k,v) :: p :: ps) (Left Refl)
  EQ _ prf _ => IR ((fst p, v) :: ps) (Right Refl)
  GT _ _ prf => prepend p $ insert_  k v ps
insert_ k v []        = IR [(k,v)] (Left Refl)

||| Like `insert` but in case `k` is already present in the assoc
||| list, the `v` will be cobine with the old value via function `f`.
public export
insertWith_ :  (f : a -> a -> a)
            -> (k : Key)
            -> (v : a)
            -> AL ix a
            -> InsertRes k ix a
insertWith_ f k v (p :: ps) = case comp k (fst p) of
  LT prf _ _ => IR ((k,v) :: p :: ps) (Left Refl)
  EQ _ prf _ => IR ((fst p, f v $ snd p) :: ps) (Right Refl)
  GT _ _ prf => prepend p $ insertWith_ f k v ps
insertWith_ _ k v []        = IR [(k,v)] (Left Refl)

--------------------------------------------------------------------------------
--          Delete
--------------------------------------------------------------------------------

||| Deleting an entry from an assoc list results in a new assoc list
||| the index of which is equal to or smaller than the one from
||| the original list.
|||
||| @ m1 : Key index of the original assoc list.
public export
record DeleteRes (m1 : Maybe Key) (a : Type) where
  constructor DR
  {0 mx : Maybe Key}
  pairs : AL mx a
  0 prf : m1 <= mx

export %inline
prependDR :  (p : (Key,a))
          -> DeleteRes m a
          -> (0 lt : Just (fst p) < m)
          => DeleteRes (Just $ fst p) a
prependDR p (DR ps lte) =
  let 0 lt = strictLeft lt lte
   in DR (p :: ps) Refl

||| Tries to remove the entry with the given key from the
||| assoc list. The key index of the result will be equal to
||| or greater than `m`.
export
delete_ : (k : Key) -> AL m a -> DeleteRes m a
delete_ k (p :: ps) = case comp k (fst p) of
  LT _ _ _ => DR (p :: ps) %search
  EQ _ _ _ => DR ps %search
  GT _ _ _ => prependDR p $ delete_ k ps
delete_ k []        = DR [] %search

||| Applies the given function to all values, keeping only the
||| `Just` results.
export
mapMaybe_ : (a -> Maybe b) -> AL m a -> DeleteRes m b
mapMaybe_ f (p :: ps) = case f (snd p) of
  Just v  => prependDR (fst p, v) $ mapMaybe_ f ps
  Nothing => let DR qs prf = mapMaybe_ f ps
              in DR qs (transitive %search prf)
mapMaybe_ f []        = DR [] %search

||| Applies the given function to all key / value pairs, keeping only the
||| `Just` results.
export
mapMaybeK_ : (Key -> a -> Maybe b) -> AL m a -> DeleteRes m b
mapMaybeK_ f ((n,va) :: ps) = case f n va of
  Just vb => prependDR (n,vb) $ mapMaybeK_ f ps
  Nothing => let DR qs prf = mapMaybeK_ f ps
              in DR qs (transitive %search prf)
mapMaybeK_ f []        = DR [] %search

--------------------------------------------------------------------------------
--          Update
--------------------------------------------------------------------------------

||| Updates the value at the given position by applying the given function.
export
update_ : (k : Key) -> (a -> a) -> AL m a -> AL m a
update_ k f (p :: ps) = case comp k (fst p) of
  LT _ _ _ => p :: ps
  EQ _ _ _ => (fst p, f $ snd p) :: ps
  GT _ _ _ => p :: update_ k f ps
update_ k f []        = []

||| Updates the value at the given position by applying the given effectful
||| computation.
export
updateA_ : Applicative f => (k : Key) -> (a -> f a) -> AL m a -> f (AL m a)
updateA_ k g (p :: ps) = case comp k (fst p) of
  LT _ _ _ => pure $ p :: ps
  EQ _ _ _ => map (\v => (fst p, v) :: ps) (g $ snd p)
  GT _ _ _ => (p ::) <$>  updateA_ k g ps
updateA_ k g []        = pure []

--------------------------------------------------------------------------------
--          Union
--------------------------------------------------------------------------------

||| Result of computing the union of two assoc lists with
||| key indices `m1` and `m2`. The result's key index is equal to either
||| `m1` or `m2`
public export
record UnionRes (m1,m2 : Maybe Key) (a : Type) where
  constructor UR
  {0 mx : Maybe Key}
  pairs : AL mx a
  0 prf : Either (m1 === mx) (m2 === mx)

0 trans_LT_EQ : {0 lt : _} -> Transitive a lt => lt x y -> y === z -> lt x z
trans_LT_EQ w Refl = w

public export %inline
prepLT :
     (p : (Key,a))
  -> UnionRes m1 (Just k2) a
  -> (0 prf1 : Just (fst p) < m1)
  => (0 prf2 : Just (fst p) < Just k2)
  => UnionRes (Just $ fst p) (Just k2) a
prepLT p (UR ps prf) =
  let 0 lt = either (trans_LT_EQ prf1) (trans_LT_EQ prf2) prf
   in UR (p :: ps) (Left Refl)

public export %inline
prepGT :
     (p : (Key,a))
   -> UnionRes (Just k1) m2 a
   -> (0 prf1 : Just (fst p) < m2)
   => (0 prf2 : Just (fst p) < Just k1)
   => UnionRes (Just k1) (Just $ fst p) a
prepGT p (UR ps prf) =
  let 0 lt = either (trans_LT_EQ prf2) (trans_LT_EQ prf1) prf
   in UR (p :: ps) (Right Refl)

public export %inline
prepEQ :
     {0 x : Maybe Key}
  -> (p : (Key,a))
  -> (0 eq  : fst p === k)
  -> UnionRes m1 m2 a
  -> (0 prf1 : Just (fst p) < m1)
  => (0 prf2 : Just k < m2)
  => UnionRes (Just $ fst p) x a
prepEQ p eq (UR ps prf) =
  let 0 fstp_lt_m2 = rewrite eq in prf2
      0 lt = either (trans_LT_EQ prf1) (trans_LT_EQ fstp_lt_m2) prf
   in UR (p :: ps) (Left Refl)

||| Computes the union of two assoc lists.
|||
||| In case of identical keys, the value of the second list
||| is dropped. Use `unionWith` for better control over handling
||| duplicate entries.
public export
union_ : AL m1 a -> AL m2 a -> UnionRes m1 m2 a
union_ (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT prf _   _   => prepLT p $ union_ ps (q :: qs)
  EQ _   prf _   => prepEQ p prf $ union_ ps qs
  GT _   _   prf => prepGT q $ union_ (p :: ps) qs
union_ y [] = UR y (Left Refl)
union_ [] y = UR y (Right Refl)

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`. Otherwise, values are converted with `g`.
public export
unionMap_ :
     (f : a -> a -> b)
  -> (g : a -> b)
  -> AL m1 a
  -> AL m2 a
  -> UnionRes m1 m2 b
unionMap_ f g (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT prf _   _   => prepLT (fst p, g $ snd p) $ unionMap_ f g ps (q :: qs)
  EQ _   prf _   => prepEQ (fst p, f (snd p) (snd q)) prf $ unionMap_ f g ps qs
  GT _   _   prf => prepGT (fst q, g $ snd q) $ unionMap_ f g (p :: ps) qs
unionMap_ _ g y [] = UR (map g y) (Left Refl)
unionMap_ _ g [] y = UR (map g y) (Right Refl)

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`.
public export
unionWith_ : (a -> a -> a) -> AL m1 a -> AL m2 a -> UnionRes m1 m2 a
unionWith_ f = unionMap_ f id

--------------------------------------------------------------------------------
--          Intersection
--------------------------------------------------------------------------------

||| The result of building the intersection of two assoc lists may
||| contain an arbitrary new key index, which is not smaller than
||| the head indices of the original lists.
public export
record IntersectRes (m1,m2 : Maybe Key) (a : Type) where
  constructor IS
  {0 mx : Maybe Key}
  pairs  : AL mx a
  0 prf1 : m1 <= mx
  0 prf2 : m2 <= mx

0 lteNothing : {m : Maybe Key} -> m <= Nothing
lteNothing {m = Nothing} = Refl
lteNothing {m = Just _}  = Rel %search

public export %inline
prependIS :
     {0 m1,m2 : Maybe Key}
  -> (p : (Key, a))
  -> (0 prf : fst p === k)
  -> IntersectRes m1 m2 a
  -> (0 lt  : Just (fst p) < m1)
  => IntersectRes (Just $ fst p) (Just k) a
prependIS p prf (IS ps prf1 prf2) =
  let 0 ltp = strictLeft lt prf1
   in IS (p :: ps) Refl (fromEq $ cong Just (sym prf))

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Only the values of
||| the first list are being kept.
public export
intersect_ : AL m1 a -> AL m2 a -> IntersectRes m1 m2 a
intersect_ (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT _ _ _   =>
    let IS res p1 p2 = intersect_ ps (q :: qs)
     in IS res (transitive %search p1) p2
  EQ _ y _ => prependIS p y $ intersect_ ps qs
  GT _ _ _ =>
    let IS res p1 p2 = intersect_ (p :: ps) qs
     in IS res p1 (transitive %search p2)
intersect_ y [] = IS [] lteNothing %search
intersect_ [] y = IS [] %search lteNothing

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Values of the two
||| lists are combine using function `f`.
public export
intersectWith_ : (a -> a -> b) -> AL m1 a -> AL m2 a -> IntersectRes m1 m2 b
intersectWith_ f (p :: ps) (q :: qs) = case comp (fst p) (fst q) of
  LT _ _ _ =>
    let IS res p1 p2 = intersectWith_ f ps (q :: qs)
     in IS res (transitive %search p1) p2
  EQ _ y _ => prependIS (fst p, f (snd p) (snd q)) y $ intersectWith_ f ps qs
  GT _ _ _ =>
    let IS res p1 p2 = intersectWith_ f (p :: ps) qs
     in IS res p1 (transitive %search p2)
intersectWith_ _ y [] = IS [] lteNothing %search
intersectWith_ _ [] y = IS [] %search lteNothing

--------------------------------------------------------------------------------
--          AssocList
--------------------------------------------------------------------------------

public export
record AssocList a where
  constructor MkAL
  {0 m : Maybe Key}
  repr : AL m a

public export %inline
Functor AssocList where
  map f (MkAL r) = MkAL $ map f r

public export %inline
foldlKV : (acc -> (Key,el) -> acc) -> acc -> AssocList el -> acc
foldlKV f ini (MkAL r) = foldlKV_ f ini r

public export
traverseKV : Applicative f => ((Key,a) -> f b) -> AssocList a -> f (AssocList b)
traverseKV f (MkAL r) = MkAL <$> traverseKV_ f r

public export %inline
Foldable AssocList where
  foldr c n (MkAL r) = foldr c n r
  foldl c n (MkAL r) = foldl c n r
  null (MkAL r) = null r
  foldMap f (MkAL r) = foldMap f r

public export %inline
Traversable AssocList where
  traverse f (MkAL r) = MkAL <$> traverse f r

||| Lookup a key in an assoc list.
public export %inline
lookup : (k : Key) -> AssocList a -> Maybe a
lookup k (MkAL r) = lookup_ k r

public export %inline
nonEmpty : AssocList a -> Bool
nonEmpty (MkAL r) = nonEmpty_ r

public export %inline
isEmpty : AssocList a -> Bool
isEmpty (MkAL r) = isEmpty_ r

||| Extracts the key / value pairs from the assoc list.
public export %inline
pairs : AssocList a -> List (Key,a)
pairs (MkAL r) = pairs_ r

||| Extracts the keys from the assoc list.
public export %inline
keys : AssocList a -> List Key
keys (MkAL r) = keys_ r

||| Extracts the values from the assoc list.
public export %inline
values : AssocList a -> List a
values (MkAL r) = values_ r

public export %inline
length : AssocList a -> Nat
length (MkAL r) = length_ r

public export %inline
Eq a => Eq (AssocList a) where
  MkAL r1 == MkAL r2 = heq r1 r2

export
Show a => Show (AssocList a) where
  showPrec p (MkAL r) = showCon p "MkAL" $ showArg r

||| Inserts a new key / value pair into an assoc list.
||| The result type reflects the possibilities with regard
||| to the head pair of the new assoc list.
|||
||| Note: If the given key `k` is already present in the assoc list,
||| its associated value will be replaced with `v`.
public export %inline
insert : (k : Key) -> (v : a) -> AssocList a -> AssocList a
insert k v (MkAL r) = MkAL $ pairs $ insert_ k v r

||| Like `insert` but in case `k` is already present in the assoc
||| list, the `v` will be cobine with the old value via function `f`.
public export %inline
insertWith :  (f : a -> a -> a)
           -> (k : Key)
           -> (v : a)
           -> AssocList a
           -> AssocList a
insertWith f k v (MkAL r) = MkAL $ pairs $ insertWith_ f k v r

public export
fromList : List (Key,a) -> AssocList a
fromList = foldl (\al,(k,v) => insert k v al) (MkAL [])

||| Tries to remove the entry with the given key from the
||| assoc list. The key index of the result will be equal to
||| or greater than `m`.
public export %inline
delete : (k : Key) -> AssocList a -> AssocList a
delete k (MkAL r) = MkAL $ pairs $ delete_ k r

||| Applies the given function to all values, keeping only the
||| `Just` results.
public export %inline
mapMaybe : (a -> Maybe b) -> AssocList a -> AssocList b
mapMaybe f (MkAL r) = MkAL $ pairs $ mapMaybe_ f r

||| Applies the given function to all key / value pairs, keeping only the
||| `Just` results.
public export %inline
mapMaybeK : (Key -> a -> Maybe b) -> AssocList a -> AssocList b
mapMaybeK f (MkAL r) = MkAL $ pairs $ mapMaybeK_ f r

||| Updates the value at the given position by applying the given function.
public export %inline
update : (k : Key) -> (a -> a) -> AssocList a -> AssocList a
update k f (MkAL r) = MkAL $ update_ k f r

||| Updates the value at the given position by applying the given effectful
||| computation.
public export %inline
updateA : Applicative f => Key -> (a -> f a) -> AssocList a -> f (AssocList a)
updateA k g (MkAL r) = MkAL <$> updateA_ k g r

||| Computes the union of two assoc lists.
|||
||| In case of identical keys, the value of the second list
||| is dropped. Use `unionWith` for better control over handling
||| duplicate entries.
public export %inline
union : AssocList a -> AssocList a -> AssocList a
union (MkAL r1) (MkAL r2) = MkAL $ pairs $ union_ r1 r2

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`. Otherwise, values are converted with `g`.
public export %inline
unionMap :
     (f : a -> a -> b)
  -> (g : a -> b)
  -> AssocList a
  -> AssocList a
  -> AssocList b
unionMap f g (MkAL r1) (MkAL r2) = MkAL $ pairs $ unionMap_ f g r1 r2

||| Like `union` but in case of identical keys appearing in
||| both lists, the associated values are combined using
||| function `f`.
public export %inline
unionWith : (a -> a -> a) -> AssocList a -> AssocList a -> AssocList a
unionWith f = unionMap f id

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Only the values of
||| the first list are being kept.
public export %inline
intersect : AssocList a -> AssocList a -> AssocList a
intersect (MkAL r1) (MkAL r2) = MkAL $ pairs $ intersect_ r1 r2

||| Computes the intersection of two assoc lists, keeping
||| only entries appearing in both lists. Values of the two
||| lists are combine using function `f`.
public export
intersectWith : (a -> a -> b) -> AssocList a -> AssocList a -> AssocList b
intersectWith f (MkAL r1) (MkAL r2) = MkAL $ pairs $ intersectWith_ f r1 r2
