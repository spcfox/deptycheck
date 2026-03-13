module Data.SortedMap.Monad

import public Data.SortedMap
import public Data.SortedMap.Extra

%default total

public export %inline
insertM : Monad m => k -> v -> SortedMap k v -> m (SortedMap k v)
insertM k v m = pure $ insert k v m

public export %inline
insertM' : Monad m => SortedMap k v -> (k, v) -> m (SortedMap k v)
insertM' m kv = pure $ insert' m kv

public export %inline
mergeLeftM : Monad m => SortedMap k v -> SortedMap k v -> m (SortedMap k v)
mergeLeftM m1 m2 = pure $ mergeLeft m1 m2

public export %inline
fromListM : Monad m => Ord k => List (k, v) -> m (SortedMap k v)
fromListM kvs = pure $ fromList kvs
