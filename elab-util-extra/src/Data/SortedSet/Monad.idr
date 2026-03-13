module Data.SortedSet.Monad

import public Data.SortedSet
import public Data.SortedSet.Extra

%default total

public export %inline
insertM : Monad m => a -> SortedSet a -> m (SortedSet a)
insertM x s = pure $ insert x s

public export %inline
insertM' : Monad m => SortedSet a -> a -> m (SortedSet a)
insertM' s x = pure $ insert' s x

public export %inline
toListM : Monad m => SortedSet a -> m (List a)
toListM s = pure $ Prelude.toList s

public export %inline
fromListM : Monad m => Ord a => List a -> m (SortedSet a)
fromListM xs = pure $ fromList xs

public export
anyM : Monad m => (a -> m Bool) -> List a -> m Bool
anyM f [] = pure False
anyM f (x :: xs) = if !(f x) then pure True else anyM f xs

public export %inline
unionM : Monad m => SortedSet a -> SortedSet a -> m (SortedSet a)
unionM s1 s2 = pure $ s1 `union` s2

export %inline
(<+>) : Monad m => Ord a => SortedSet a -> SortedSet a -> m (SortedSet a)
(<+>) s1 s2 = pure $ s1 <+> s2
