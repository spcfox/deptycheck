module Language.Reflection.Compat.Recursive

import Data.SortedMap
import Data.SortedSet

import public Language.Reflection.Compat.TypeInfo

import public Syntax.IHateParens.SortedSet

%default total

export
record RecursiveCons where
  constructor MkRecursiveCons
  recursiveCons : SortedSet Name

export
isRecursive : RecursiveCons => Con -> Bool
isRecursive @{recCons} = contains' recCons.recursiveCons . name

------------------------------------------
-- Tarjan's algorithm for finding SCCs ---
------------------------------------------

-- Based on implementation from Idris2 compiler
-- https://github.com/idris-lang/Idris2/blob/f1bde6d4b130b4e382226d5115e3ab71c6a11e80/src/Libraries/Data/Graph.idr

record TarjanVertex where
  constructor TV
  index   : Int
  lowlink : Int
  inStack : Bool

record TarjanState cuid where
  constructor TS
  vertices           : SortedMap cuid TarjanVertex
  stack              : List cuid
  nextIndex          : Int
  components         : List (List1 cuid)
  impossibleHappened : Bool  -- we should get at least some indication of broken assumptions

initial : Ord cuid => TarjanState cuid
initial = TS empty [] 0 [] False

tarjan : Monad m => Ord cuid => SortedMap cuid (SortedSet cuid) -> m $ List (List1 cuid)
tarjan {cuid} deps = loop initial (SortedMap.keys deps)
  where
    strongConnect : TarjanState cuid -> cuid -> m $ TarjanState cuid
    strongConnect ts v = do
        ts'' <- case SortedMap.lookup v deps of
              Nothing => pure ts'  -- no edges
              Just edgeSet => loop ts' (Prelude.toList edgeSet)
        case SortedMap.lookup v ts''.vertices of
         Nothing => pure $ { impossibleHappened := True } ts''
         Just vtv =>
           if vtv.index == vtv.lowlink
             then createComponent ts'' v []
             else pure ts''
      where
        createComponent : TarjanState cuid -> cuid -> List cuid -> m $ TarjanState cuid
        createComponent ts v acc =
          case ts.stack of
            [] => pure $ { impossibleHappened := True } ts
            w :: ws =>
              let ts' : TarjanState cuid = {
                      vertices $= updateExisting { inStack := False } w,
                      stack := ws
                    } ts
                in if w == v
                  then pure $ { components $= ((v ::: acc) ::) } ts'  -- that's it
                  else assert_total createComponent ts' v (w :: acc)

        loop : TarjanState cuid -> List cuid -> m $ TarjanState cuid
        loop ts [] = pure ts
        loop ts (w :: ws) = do
          ts <- case SortedMap.lookup w ts.vertices of
                   Nothing => do
                     ts' <- assert_total strongConnect ts w
                     case SortedMap.lookup w ts'.vertices of
                       Nothing => pure $ { impossibleHappened := True } ts'
                       Just wtv => pure $ { vertices $= updateExisting { lowlink $= min wtv.lowlink } v } ts'

                   Just wtv => case wtv.inStack of
                     False => pure ts  -- nothing to do
                     True => pure $ { vertices $= updateExisting { lowlink $= min wtv.index } v } ts
          loop ts ws

        ts' : TarjanState cuid
        ts' = {
            vertices  $= SortedMap.insert v (TV ts.nextIndex ts.nextIndex True),
            stack     $= (v ::),
            nextIndex $= (1+)
          } ts

    loop : TarjanState cuid -> List cuid -> m $ List (List1 cuid)
    loop ts [] =
      pure $ if ts.impossibleHappened
                then []
                else ts.components
    loop ts (v :: vs) =
      case SortedMap.lookup v ts.vertices of
        Just _ => loop ts vs  -- done, skip
        Nothing => loop !(strongConnect ts v) vs

----------------------------------------
--- Calculate recursive constructors ---
----------------------------------------

export
getRecursiveCons : Monad m => NamesInfoInTypes => m RecursiveCons
getRecursiveCons =
  MkRecursiveCons . fromList . concat . map forget . filter ((> 1) . List1.length) <$> tarjan getNamesInTypes
