module Language.Reflection.Compat.TypeInfo

import Data.SortedMap.Monad
import Data.SortedSet.Monad

import public Language.Reflection.Compat.Constr
import public Language.Reflection.Expr

import public Syntax.IHateParens.SortedSet

%default total

%hide SortedMap.insert
%hide SortedMap.insert'
%hide SortedMap.mergeLeft
%hide SortedMap.fromList
%hide SortedSet.insert
%hide SortedSet.insert'
%hide SortedSet.toList

--------------------------------------------------------
--- Acquiring special representations from type info ---
--------------------------------------------------------

||| Returns a type constructor as `Con` by given type
typeCon : TypeInfo -> Con
typeCon ti = MkCon ti.name ti.args type

||| Generate a declaration from TypeInfo
export
(.decl) : TypeInfo -> Decl
(.decl) ti =
  iData Public ti.name tySig [] conITys
  where
    tySig = piAll type ti.args
    conITys = (.iTy) <$> ti.cons

---------------------------
--- Analysing type info ---
---------------------------

-- Returns a list without duplications
export
allInvolvedTypes : Elaboration m => (minimalRig : Count) -> TypeInfo -> m $ List TypeInfo
allInvolvedTypes minimalRig ti = toList <$> go [ti] empty where
  go : (left : List TypeInfo) -> (curr : SortedMap Name TypeInfo) -> m $ SortedMap Name TypeInfo
  go left curr = do
    let (c::left) = filter (not . isJust . lookup' curr . name) left
      | [] => pure curr
    next <- insertM c.name c curr
    args <- atRig M0 $ join <$> for c.args typesOfArg
    cons <- join <$> for c.tyCons typesOfCon
    assert_total $ go (args ++ cons ++ left) next
    where
      atRig : Count -> m (List a) -> m (List a)
      atRig rig act = if rig >= minimalRig then act else pure []

      typesOfExpr : TTImp -> m $ List TypeInfo
      typesOfExpr expr = map (mapMaybe id) $ for (allVarNames expr) $ catch . getInfo'

      typesOfArg : Arg -> m $ List TypeInfo
      typesOfArg arg = atRig arg.count $ typesOfExpr arg.type

      typesOfCon : Con -> m $ List TypeInfo
      typesOfCon con = [| atRig M0 (typesOfExpr con.type) ++ (join <$> for con.args typesOfArg) |]

-- Fails if the given type info does not have all type args named
export
ensureTyArgsNamed : Elaboration m => (ty : TypeInfo) -> m $ AllTyArgsNamed ty
ensureTyArgsNamed ty = do
  let Yes prf = areAllTyArgsNamed ty
    | No _ => fail "Type info for type `\{ty.name}` contains unnamed arguments"
  pure prf

export
(.argNames) : (ti : TypeInfo) -> (0 tiN : AllTyArgsNamed ti) => List Name
(.argNames) ti = argNames ti.args @{tiN.tyArgsNamed}

--------------------------
--- Changing type info ---
--------------------------

normaliseCons : Elaboration m => TypeInfo -> m TypeInfo
normaliseCons ty = for ty.cons normaliseCon <&> \cons' => {cons := cons'} ty

---------------------------
--- Names info in types ---
---------------------------

export
record NamesInfoInTypes where
  constructor Names
  types : SortedMap Name TypeInfo
  cons  : SortedMap Name (TypeInfo, Con)
  namesInTypes : SortedMap TypeInfo $ SortedSet Name

lookupByType : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
lookupByType @{tyi} = lookup' tyi.types >=> lookup' tyi.namesInTypes

lookupByCon : NamesInfoInTypes => Name -> Maybe $ SortedSet Name
lookupByCon @{tyi} = concatMap @{Deep} lookupByType . Prelude.toList . concatMap allVarNames' . conSubexprs . snd <=< lookup' tyi.cons

typeByCon : NamesInfoInTypes => Con -> Maybe TypeInfo
typeByCon @{tyi} = map fst . lookup' tyi.cons . name

export
lookupType : NamesInfoInTypes => Name -> Maybe TypeInfo
lookupType @{tyi} = lookup' tyi.types

export
lookupCon : NamesInfoInTypes => Name -> Maybe Con
lookupCon @{tyi} n = snd <$> lookup n tyi.cons
                 <|> typeCon <$> lookup n tyi.types

export
knownTypes : NamesInfoInTypes => SortedMap Name TypeInfo
knownTypes @{tyi} = tyi.types

||| Returns either resolved expression, or a non-unique name and the set of alternatives.
-- We could use `Validated (SortedMap Name $ SortedSet Name) TTImp` as the result, if we depended on `contrib`.
-- NOTICE: this function does not resolve re-export aliases, say, it does not resolve `Prelude.Nil` to `Prelude.Basics.Nil`.
export
resolveNamesUniquely : NamesInfoInTypes => (freeNames : SortedSet Name) -> TTImp -> Either (Name, SortedSet Name) TTImp
resolveNamesUniquely @{tyi} freeNames = do
  let allConsideredNames = keySet tyi.types `union` keySet tyi.cons
  let reverseNamesMap = concatMap (uncurry SortedMap.singleton) $ allConsideredNames.asList >>= \n => allNameSuffixes n <&> (, SortedSet.singleton n)
  mapATTImp' $ \case
    v@(IVar fc n) => if contains n freeNames then id else do
                       let Just resolvedAlts = lookup n reverseNamesMap | Nothing => id
                       let [resolved] = Prelude.toList resolvedAlts
                         | _ => const $ Left (n, resolvedAlts)
                       const $ pure $ IVar fc resolved
    _ => id

export
[TypeInfoEqByName] Eq TypeInfo where
  (==) = (==) `on` name

export
[TypeInfoOrdByName] Ord TypeInfo using TypeInfoEqByName where
  compare = comparing name

empty : NamesInfoInTypes
empty = let _ = TypeInfoOrdByName in Names empty empty empty

(<+>) : Monad m => NamesInfoInTypes -> NamesInfoInTypes -> m NamesInfoInTypes
(<+>) (Names ts cs nit) (Names ts' cs' nit') =
  pure $ Names !(ts `mergeLeftM` ts') !(cs `mergeLeftM` cs') !(nit `mergeLeftM` nit')

export
hasNameInsideDeep : Monad m => NamesInfoInTypes => Name -> TTImp -> m Bool
hasNameInsideDeep nm = hasInside empty . allVarNames where

  hasInside : (visited : SortedSet Name) -> (toLook : List Name) -> m Bool
  hasInside visited []           = pure False
  hasInside visited (curr::rest) = if curr == nm then pure True else do
    let new : List Name = if contains curr visited then [] else maybe [] Prelude.toList $ lookupByType curr
    -- visited is limited and either growing or `new` is empty, thus `toLook` is strictly less
    visited' <- insertM curr visited
    assert_total $ hasInside visited' (new ++ rest)
    -- pure $ assert_total $ hasInside visited' (new ++ rest)

export
isRecursive : Monad m => NamesInfoInTypes => (con : Con) -> {default Nothing containingType : Maybe TypeInfo} -> m Bool
isRecursive con = case the (Maybe TypeInfo) $ containingType <|> typeByCon con of
  Just containingType => anyM (hasNameInsideDeep containingType.name) $ conSubexprs con
  Nothing             => pure False

-- returns `Nothing` if given name is not a constructor
export
isRecursiveConstructor : Monad m => (tyi : NamesInfoInTypes) => Name -> m $ Maybe Bool
isRecursiveConstructor n = for (lookup' tyi.cons n) $ \(ty, con) => isRecursive {containingType=Just ty} con

export
enrichNamesInfoInTypes : Elaboration m => List TypeInfo -> NamesInfoInTypes -> m NamesInfoInTypes
enrichNamesInfoInTypes []         tyi = pure tyi
enrichNamesInfoInTypes (ti::rest) tyi = do
  ti <- normaliseCons ti
  subes <- concatMap allVarNames' <$> subexprs ti
  new : List TypeInfo <- map join $ for !(toListM subes) $ \n =>
           if isNothing $ lookupByType n
             then map toList $ catch $ getInfo' n
             else pure []
  nextTyeps <- insertM ti.name ti tyi.types
  nextNamesInTypes <- insertM ti subes tyi.namesInTypes
  nextCons <- mergeLeftM !(fromListM $ ti.cons <&> \con => (con.name, ti, con)) tyi.cons
  assert_total $ enrichNamesInfoInTypes (new ++ rest) $ Names nextTyeps nextCons nextNamesInTypes
  where
    subexprs : TypeInfo -> m $ List TTImp
    subexprs ty = pure $ map type ty.args ++ (ty.cons >>= conSubexprs)

export
getNamesInfoInTypes : Elaboration m => TypeInfo -> m NamesInfoInTypes
getNamesInfoInTypes ty = enrichNamesInfoInTypes [ty] empty

export
getNamesInfoInTypes' : Elaboration m => TTImp -> m NamesInfoInTypes
getNamesInfoInTypes' expr = do
  let varsFirstOrder = allVarNames expr
  varsSecondOrder : SortedSet Name <- foldlM (<+>) SortedSet.empty !(for varsFirstOrder $ \n => do
                          ns <- getType n
                          vars <- foldlM (<+>) empty $ !(for ns $ \(n', ty) => insertM n' $ allVarNames' ty)
                          insertM n vars)
  tys <- map (mapMaybe id) $ for (Prelude.toList varsSecondOrder) $ catch . getInfo'
  infos <- Prelude.for tys getNamesInfoInTypes
  foldlM (<+>) empty infos
