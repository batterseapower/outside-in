{-# LANGUAGE ScopedTypeVariables, TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Applicative (Applicative(..))
import Control.Arrow (first, second, (***))
import Control.Monad

import Data.Char
import Data.Function
import Data.Traversable (Traversable(..))
import Data.List

import Debug.Trace
import GHC.Exts (IsString(..))

import Text.PrettyPrint.HughesPJClass hiding (first)

import Prelude hiding (interact)


{-
newtype Unique = Unique { unUnique :: Integer }
               deriving (Eq, Ord)

data UniqSupply = UniqSupply Unique UniqSupply UniqSupply

-- Simple but inefficient
uniqSupply :: UniqSupply
uniqSupply = go 0
  where go i = UniqSupply (Unique i) (go (2 * i)) (go (1 + (2 * i)))

uniqFromSupply :: UniqSupply -> Unique
uniqFromSupply (UniqSupply u _ _) = u

splitUniqSupply :: UniqSupply -> (UniqSupply, UniqSupply)
splitUniqSupply (UniqSupply _ l r) = (l, r)

deriveUnique :: Unique -> Unique
deriveUnique (Unique i) = Unique (i + 1)
-}


fmapFst :: (a -> c) -> (a, b) -> (c, b)
fmapFst f (a, b) = (f a, b)

spanReverse :: (a -> Bool) -> [a] -> ([a], [a])
spanReverse f xs = case span f (reverse xs) of (satisfy, rest) -> (reverse rest, reverse satisfy)

unionMapA :: (Applicative t, Ord k)
          => (v -> v -> t v)
          -> M.Map k v -> M.Map k v -> t (M.Map k v)
unionMapA f m1 m2 = flip traverse (M.unionWith (\(Right v1) (Right v2) -> Left (f v1 v2)) (fmap Right m1) (fmap Right m2)) $ \ei_tx_x -> case ei_tx_x of
    Left tx -> tx
    Right x -> pure x

extract :: (a -> Maybe b) -> [a] -> ([b], [a])
extract f = go [] []
  where go bs as' []     = (reverse bs, reverse as')
        go bs as' (a:as) = case f a of
          Nothing -> go bs     (a:as') as
          Just b  -> go (b:bs) as'     as

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
    pPrint kvs = char '{' <+> hcat (intersperse (text ", ") [pPrint k <+> text "->" <+> pPrint v | (k, v) <- M.toList kvs]) <+> char '}'


class (Pretty tv, Ord tv) => TyVarLike tv where
    derived :: tv -> tv

{-
instance TyVarLike Unique where
    derived = deriveUnique
-}

{-
data TyVar = TV { tyVarName :: String, tyVarUnique :: Int }

instance Eq TyVar where
    (==) = (==) `on` tyVarUnique

instance Ord TyVar where
    compare = compare `on` tyVarUnique

instance TyVarLike TyVar where
    derived tv = TV { tyVarName = tyVarName tv, tyVarUnique = derived (tyVarUnique tv) }
-}

newtype TyVar = TV { unTV :: String }
              deriving (Eq, Ord)

instance IsString TyVar where
    fromString = TV

instance TyVarLike TyVar where
    derived tv = TV $ case spanReverse isNumber (unTV tv) of
      (non_num, [])  -> non_num ++ "1"
      (non_num, num) -> non_num ++ show ((read num :: Integer) + 1)

instance Pretty TyVar where
    pPrint = text . unTV


-- NB: ensure that TcUnif < TcSkolem so that we can use the Ord instance during canonicalization
data TcTyVar = TcUnif   TyVar
             | TcSkolem TyVar
             deriving (Eq, Ord)

instance TyVarLike TcTyVar where
    derived (TcUnif   tv) = TcUnif   (derived tv)
    derived (TcSkolem tv) = TcSkolem (derived tv)

instance Pretty TcTyVar where
    pPrintPrec lvl prec (TcUnif tv)   = pPrintPrec lvl prec tv <> char '?'
    pPrintPrec lvl prec (TcSkolem tv) = pPrintPrec lvl prec tv


type TyCon = String
type TyFam = String

type Class = String

data Type tv = TyVar tv
             | TyConApp TyCon [Type tv]
             | TyFamApp TyFam [Type tv]
             | TyForAll tv (Type tv)

data Instance tv = I Class [Type tv]
                 deriving (Eq, Ord)

data Equality tv = (:~) (Type tv) (Type tv)
                 deriving (Eq, Ord)

data BaseConstraint tv = Equality (Equality tv)
                       | Instance (Instance tv)
                       deriving (Eq, Ord)

data TopLevelImplication tv = TLI [tv] [BaseConstraint tv] (Instance tv)
                            | TLE [tv] TyFam [Type tv] (Type tv)

data Implication tv = Imp [tv] [BaseConstraint tv] (Implications tv)
type Implications tv = ([Implication tv], [BaseConstraint tv])


instance Ord tv => Eq (Type tv) where
    ty1 == ty2 = ty1 `compare` ty2 == EQ

instance Ord tv => Ord (Type tv) where
    compare = alphaOrd (0, M.empty, M.empty)


topPrec, funPrec, argPrec :: Rational
topPrec = 0
funPrec = 1
argPrec = 2

pPrintPrecNAry :: (Pretty a) => PrettyLevel -> Rational -> String -> [a] -> Doc
pPrintPrecNAry lvl prec s xs = prettyParen (prec > 1 && not (null xs)) $ text s <+> hsep (map (pPrintPrec lvl argPrec) xs)

pPrintContext :: (Pretty a) => PrettyLevel -> [a] -> Doc
pPrintContext lvl required = parens (hcat (intersperse (text ", ") (map (pPrintPrec lvl topPrec) required))) <+> text "=>"

instance Pretty tv => Pretty (Type tv) where
    pPrintPrec lvl prec (TyVar tv)         = pPrintPrec lvl prec tv
    pPrintPrec lvl prec (TyConApp tc [ty]) | tc == "[]" = brackets (pPrintPrec lvl topPrec ty)
    pPrintPrec lvl prec (TyConApp tc tys)  = pPrintPrecNAry lvl prec tc tys
    pPrintPrec lvl prec (TyFamApp tc tys)  = pPrintPrecNAry lvl prec tc tys
    pPrintPrec lvl prec (TyForAll tv ty)   = prettyParen (prec > topPrec) $ text "forall" <+> pPrintPrec lvl topPrec tv <> char '.' <+> pPrintPrec lvl topPrec ty

instance Pretty tv => Pretty (Instance tv) where
    pPrintPrec lvl prec (I cls tys) = pPrintPrecNAry lvl prec cls tys

instance Pretty tv => Pretty (Equality tv) where
    pPrintPrec lvl prec (ty1 :~ ty2) = prettyParen (prec > funPrec) $ pPrintPrec lvl topPrec ty1 <+> char '~' <+> pPrintPrec lvl topPrec ty2

instance Pretty tv => Pretty (BaseConstraint tv) where
    pPrintPrec lvl prec (Equality eq)   = pPrintPrec lvl prec eq
    pPrintPrec lvl prec (Instance inst) = pPrintPrec lvl prec inst

instance Pretty tv => Pretty (TopLevelImplication tv) where
    pPrintPrec lvl prec (TLI tvs required inst) = prettyParen (prec > topPrec) $ pPrintPrecNAry lvl topPrec "forall" tvs <> char '.' <+> pPrintContext lvl required <+> pPrintPrec lvl topPrec inst
    pPrintPrec lvl prec (TLE tvs tf tys ty)     = prettyParen (prec > topPrec) $ pPrintPrecNAry lvl topPrec "forall" tvs <> char '.' <+> pPrintPrecNAry lvl topPrec tf tys <+> char '~' <+> pPrintPrec lvl topPrec ty

instance Pretty tv => Pretty (Implication tv) where
    pPrintPrec lvl prec (Imp tvs required imps) = prettyParen (prec > topPrec) $ pPrintPrecNAry lvl topPrec "exists" tvs <> char '.' <+> pPrintContext lvl required <+> pPrintPrec lvl topPrec imps

type TySubst tv = M.Map tv (Type tv)


-- Use an ordering function as the basis rather than an equality function because we'd quite like
-- an Ord instance for the purposes of normalising test results, and we can share all the code this way.
alphaOrd :: Ord tv => (Integer, M.Map tv Integer, M.Map tv Integer) -> Type tv -> Type tv -> Ordering
alphaOrd (_, rigid_l, rigid_r) (TyVar v1) (TyVar v2) = case (M.lookup v1 rigid_l, M.lookup v2 rigid_r) of
    (Just n1, Just n2) -> n1 `compare` n2
    (Nothing, Nothing) -> v1 `compare` v2
    (Just _,  Nothing) -> LT
    (Nothing, Just _ ) -> GT
alphaOrd rigids (TyConApp tc1 tys1) (TyConApp tc2 tys2)
  | tc1 == tc2 = plusOrdering $ zipWith (alphaOrd rigids) tys1 tys2
alphaOrd rigids (TyFamApp tf1 tys1) (TyFamApp tf2 tys2)
  | tf1 == tf2 = plusOrdering $ zipWith (alphaOrd rigids) tys1 tys2
alphaOrd (next, rigid_l, rigid_r) (TyForAll tv1 ty1) (TyForAll tv2 ty2)
  = alphaOrd (next + 1, M.insert tv1 next rigid_l, M.insert tv2 next rigid_r) ty1 ty2
alphaOrd _ (TyConApp _ _) _ = LT
alphaOrd _ _ (TyConApp _ _) = GT
alphaOrd _ (TyFamApp _ _) _ = LT
alphaOrd _ _ (TyFamApp _ _) = GT
alphaOrd _ (TyForAll _ _) _ = LT
alphaOrd _ _ (TyForAll _ _) = GT

plusOrdering :: [Ordering] -> Ordering
plusOrdering [] = EQ
plusOrdering (EQ:ords) = plusOrdering ords
plusOrdering (ord:_)   = ord


fvs :: Ord tv => Type tv -> S.Set tv
fvs (TyVar tv) = S.singleton tv
fvs (TyConApp _ tys) = S.unions (map fvs tys)
fvs (TyFamApp _ tys) = S.unions (map fvs tys)
fvs (TyForAll tv ty) = S.delete tv (fvs ty)

fvsConstraint :: TyVarLike tv => BaseConstraint tv -> S.Set tv
fvsConstraint (Equality (ty1 :~ ty2)) = fvs ty1 `S.union` fvs ty2
fvsConstraint (Instance (I _ tys))    = S.unions $ map fvs tys


uniqAway :: TyVarLike tv => S.Set tv -> tv -> (S.Set tv, tv)
uniqAway in_scope tv
  | tv `S.notMember` in_scope = (S.insert tv in_scope, tv)
  | otherwise                 = uniqAway in_scope (derived tv)

subst :: TyVarLike tv => TySubst tv -> Type tv -> Type tv
subst theta = subst' (S.unions $ map fvs $ M.elems theta) theta
  
subst' :: TyVarLike tv => S.Set tv -> TySubst tv -> Type tv -> Type tv
subst' in_scope theta ty = case ty of
  TyVar tv -> case M.lookup tv theta of
      Nothing  -> TyVar tv
      Just ty' -> ty'
  TyConApp tc tys -> TyConApp tc (map (subst' in_scope theta) tys)
  TyFamApp tf tys -> TyFamApp tf (map (subst' in_scope theta) tys)
  TyForAll tv ty -> TyForAll tv' (subst' in_scope' (M.insert tv (TyVar tv') theta) ty)
    where (in_scope', tv') = uniqAway in_scope tv

substConstraint :: TyVarLike tv => TySubst tv -> BaseConstraint tv -> BaseConstraint tv
substConstraint theta (Equality (ty1 :~ ty2)) = Equality (subst theta ty1 :~ subst theta ty2)
substConstraint theta (Instance (I cls tys))  = Instance (I cls (map (subst theta) tys))


-- antiSubst ty1 ty2 == Just theta
--  ==> subst theta ty1 == ty2
antiSubst :: TyVarLike tv
          => Type tv -> Type tv -> Maybe (TySubst tv)
antiSubst = antiSubst' (0, M.empty, M.empty)

antiSubst' :: TyVarLike tv
           => (Integer, M.Map tv Integer, M.Map tv Integer) -> Type tv -> Type tv -> Maybe (TySubst tv)
antiSubst' (_, rigid_l, rigid_r) (TyVar tv1) ty2 = case M.lookup tv1 rigid_l of
    -- A rigid variable can only match against the exact same rigid variable
    Just n1 | TyVar tv2 <- ty2
            , Just n2 <- M.lookup tv2 rigid_r
            , n1 == n2
            -> Just M.empty
            | otherwise
            -> Nothing
    -- We can instantiate a non-rigid variable freely as long as the thing we instantiate with does not mention any rigids
    Nothing | S.null (M.keysSet rigid_r `S.intersection` fvs ty2)
            -> Just (M.singleton tv1 ty2)
            | otherwise
            -> Nothing
antiSubst' rigid (TyConApp tc1 tys1) (TyConApp tc2 tys2) | tc1 == tc2 = zipWithM (antiSubst' rigid) tys1 tys2 >>= joinSubsts
antiSubst' rigid (TyFamApp tf1 tys1) (TyFamApp tf2 tys2) | tf1 == tf2 = zipWithM (antiSubst' rigid) tys1 tys2 >>= joinSubsts
antiSubst' (next, rigid_l, rigid_r) (TyForAll tv1 ty1) (TyForAll tv2 ty2)
  = antiSubst' (next + 1, M.insert tv1 next rigid_l, M.insert tv2 next rigid_r) ty1 ty2
antiSubst' _ _ _ = Nothing

joinSubsts :: TyVarLike tv => [TySubst tv] -> Maybe (TySubst tv)
joinSubsts = foldM joinSubst M.empty

joinSubst :: TyVarLike tv => TySubst tv -> TySubst tv -> Maybe (TySubst tv)
joinSubst = unionMapA $ \ty1 ty2 -> if ty1 == ty2 then Just ty1 else Nothing


solve :: TyVarLike tv
      => [TopLevelImplication tv] -> [BaseConstraint tv] -> [tv] -> Implications tv
      -> Maybe ([BaseConstraint tv], TySubst tv)
solve tlis givens touchables (wanted_impls, wanteds)
  | trace ("solve " ++ prettyShow (tlis, givens, touchables, (wanted_impls, wanteds))) False = undefined
  | otherwise  = do
    forM_ wanted_impls $ \(Imp touchables' imp_givens imp_wanteds) -> do
        ([], imp_theta) <- solve tlis (imp_givens ++ givens') touchables' imp_wanteds
        return ()
    return (residuals, theta)
  where (residuals, theta) = simp tlis givens touchables wanteds
        givens' = residuals ++ givens


simp :: TyVarLike tv
     => [TopLevelImplication tv] -> [BaseConstraint tv] -> [tv] -> [BaseConstraint tv]
     -> ([BaseConstraint tv], TySubst tv)
simp tlis givens touchables wanteds = (residuals, theta_pruned)
  where (residuals, theta) = simp' tlis givens M.empty touchables wanteds
        theta_pruned = M.filterWithKey (\tv _ -> tv `elem` touchables) theta -- Restrict the domain to the *original* touchables

simp' :: TyVarLike tv
     => [TopLevelImplication tv] -> [BaseConstraint tv] -> TySubst tv -> [tv] -> [BaseConstraint tv]
     -> ([BaseConstraint tv], TySubst tv)
simp' tlis givens0 given_subst0 touchables0 wanteds0
  | trace ("simp' " ++ prettyShow (tlis, givens0, given_subst0, touchables0, wanteds0)) False = undefined
  | null givens_noncanon
  , null wanteds_noncanon
  , let -- FIXME: maybe the check that (tv1 `S.notMember` fvs ty2) is actually necessary here?
        f (Equality (ty1 :~ ty2)) | TyVar tv1 <- ty1, tv1 `elem` touchables = Just (tv1, ty2)
                                  | TyVar tv2 <- ty2, tv2 `elem` touchables = Just (tv2, ty1)
        f _ = Nothing
        wanteds        = map (substConstraint given_subst) wanteds4
        (e, residuals) = extract f wanteds
        -- NB: we have to use subst' here since subst inspects range of map it is given to build the InScopeSet
        in_scope = S.unions $ map fvsConstraint wanteds
        theta    = M.fromListWith (error "simp'") [(beta, subst' in_scope theta ty) | (beta, ty) <- e]
  = (map (substConstraint theta) residuals, theta)
  | otherwise
  = simp' tlis (givens_noncanon ++ givens3) given_subst touchables (wanteds_noncanon ++ wanteds4)
  where (_,           given_subst1, givens1)  = canonicaliseMany givens0
        (touchables1, _,            wanteds1) = canonicaliseMany wanteds0
        (givens2,  givens2_noncanon)  = interactMany givens1
        (wanteds2, wanteds2_noncanon) = interactMany wanteds1
        (wanteds3, wanteds3_noncanon) = simplifyMany givens2 wanteds2
        
        (             givens3,  givens3_noncanon)  = topReactGivenMany  tlis givens2
        (touchables2, wanteds4, wanteds4_noncanon) = topReactWantedMany tlis wanteds3

        given_subst      = given_subst0 `M.union` given_subst1
        givens_noncanon  = givens2_noncanon ++ givens3_noncanon
        wanteds_noncanon = wanteds2_noncanon ++ wanteds3_noncanon ++ wanteds4_noncanon
        touchables       = touchables0 ++ touchables1 ++ touchables2


canonicaliseMany :: TyVarLike tv => [BaseConstraint tv] -> ([tv], TySubst tv, [(BaseConstraint tv)])
canonicaliseMany constraints = (concat touchabless, M.unionsWith (error "canonicaliseMany") substs, concat constraintss)
  where (touchabless, substs, constraintss) = unzip3 (map canonicalise constraints)

canonicalise :: TyVarLike tv => BaseConstraint tv -> ([tv], TySubst tv, [(BaseConstraint tv)])
canonicalise constraint = case canonicalise' constraint of
    Nothing                                  -> ([], M.empty, [constraint])
    Just (touchables1, subst1, constraints1) -> (touchables1 ++ touchables2, M.unionWith (error "canonicalise") subst1 subst2, constraints2)
      where (touchables2, subst2, constraints2) = canonicaliseMany constraints1

canonicalise' :: TyVarLike tv => BaseConstraint tv -> Maybe ([tv], TySubst tv, [(BaseConstraint tv)])
canonicalise' c | trace ("canonicalise' " ++ prettyShow c) False = undefined
canonicalise' (Equality (ty1 :~ ty2))
  -- REFL
  | ty1 == ty2
  = Just ([], M.empty, [])
  -- TDEC/FAILDEC
  | TyConApp tc1 tys1 <- ty1
  , TyConApp tc2 tys2 <- ty2
  = if tc1 == tc2
     then Just ([], M.empty, map Equality $ zipWith (:~) tys1 tys2)
     else error "FIXME: fail"
  -- ORIENT
  | case () of _ | TyFamApp _ _ <- ty2
                 , case ty1 of TyFamApp _ _ -> False; _ -> True
                 -> True
                 | TyVar tv2 <- ty2
                 , TyVar tv1 <- ty1
                 -> tv2 < tv1
                 | TyVar _ <- ty2
                 -> True  -- NB: ty1 certainly isn't a tyvar since we already tried that case
                 | otherwise
                 -> False
  = Just ([], M.empty, [Equality (ty2 :~ ty1)])
  -- FFLATWL/FFLATGL
  | TyFamApp tf1 tys1 <- ty1
  , Just (tys1', (tv_float, ty_float)) <- canonicaliseTypes tys1
  = Just ([tv_float], M.singleton tv_float ty_float, [Equality (TyFamApp tf1 tys1' :~ ty2), Equality (ty_float :~ TyVar tv_float)])
  -- FFLATWR/FFLATGR
  | case ty1 of TyFamApp _ _ -> True; TyVar _ -> True; _ -> False
  , Just (ty2', (tv_float, ty_float)) <- canonicaliseType ty2
  = Just ([tv_float], M.singleton tv_float ty_float, [Equality (ty1 :~ ty2'), Equality (ty_float :~ TyVar tv_float)])
  -- NB: critical to test strict type equality before this since (a ~ a) is OK
  -- NB: critical to float out all nested type families before this since a TV in an TyFam argument is OK
  | TyVar tv1 <- ty1
  , tv1 `S.member` fvs ty2
  = error "FIXME: fail"
canonicalise' (Instance (I cls tys))
  -- DFLATW/DFLATG
  | Just (tys', (tv, ty)) <- canonicaliseTypes tys
  = Just ([tv], M.singleton tv ty, [Instance (I cls tys'), Equality (ty :~ TyVar tv)])
canonicalise' _ = Nothing

canonicaliseType :: Type tv -> Maybe (Type tv, (tv, Type tv))
canonicaliseType (TyVar _)         = Nothing
canonicaliseType (TyConApp tc tys) = fmap (first (TyConApp tc)) $ canonicaliseTypes tys
canonicaliseType ty@(TyFamApp _ _) = error "FIXME: fresh" $ \a -> Just (TyVar a, (a, ty))
canonicaliseType (TyForAll _ _)    = Nothing

canonicaliseTypes :: [Type tv] -> Maybe ([Type tv], (tv, Type tv))
canonicaliseTypes []       = Nothing
canonicaliseTypes (ty:tys) = case canonicaliseType ty of
    Nothing           -> fmap (first (ty:)) $ canonicaliseTypes tys
    Just (ty', float) -> Just (ty':tys, float)


interactMany :: TyVarLike tv => [BaseConstraint tv] -> ([BaseConstraint tv] {- normalised inerts -}, [BaseConstraint tv] {- unnormalised -})
interactMany = go []
  where go inerts []     = (inerts, [])
        go inerts (c:cs) = case interactMany' inerts c of
            Nothing    -> go (c:inerts) cs -- Didn't interact so inert by definition, and normalised since it was before
            Just mb_c' -> second (maybe id (:) mb_c') $ go inerts cs

interactMany' :: TyVarLike tv => [BaseConstraint tv] -> BaseConstraint tv -> Maybe (Maybe (BaseConstraint tv))
interactMany' []             _  = Nothing
interactMany' (inert:inerts) c' = case interact inert c' `mplus` interact c' inert of
    Nothing    -> interactMany' inerts c'
    Just mb_c' -> Just mb_c'

-- When reading this, bear in mind that after canonicalization, the LHS of an equality is always a TyVar or TyFamApp
interact :: TyVarLike tv => BaseConstraint tv -> BaseConstraint tv -> Maybe (Maybe (BaseConstraint tv))
interact c1 c2 | trace ("interact " ++ prettyShow (c1, c2)) False = undefined
interact (Equality (ty1a :~ ty1b)) (Equality (ty2a :~ ty2b))
  -- EQSAME/FEQFEQ
  | ty1a == ty2a
  = Just $ Just $ Equality (ty1b :~ ty2b)
interact (Equality (TyVar tv1a :~ ty1b)) c2
  -- EQDIFF/EQFEQ/EQDICT
  | tv1a `S.member` fvsConstraint c2
  = Just $ Just $ substConstraint (M.singleton tv1a ty1b) c2
interact (Instance (I cls1 tys1)) (Instance (I cls2 tys2))
  -- DDICT
  | cls1 == cls2
  , tys1 == tys2
  = Just Nothing
interact _ _ = Nothing


simplifyMany :: TyVarLike tv
             => [BaseConstraint tv] -> [BaseConstraint tv]
             -> ([BaseConstraint tv] {- normalised wanteds -}, [BaseConstraint tv] {- unnormalised wanteds -})
simplifyMany = apply simplify

-- SEQSAME/SFEQFEQ == EQSAME/FEQFQ
-- SEQDIFF/SEQFEQ/SEQDICT == EQDIFF/EQFEQ/EQDICT
-- SDDICTG == DDICT
simplify :: TyVarLike tv => BaseConstraint tv -> BaseConstraint tv -> Maybe (Maybe (BaseConstraint tv))
simplify = interact


-- NB: very similar to interactMany except that if a given doesn't interact with a wanted, we don't put the wanted into the givens!
apply :: forall a b c. (a -> b -> Maybe (Maybe c))
      -> [a] -> [b] -> ([b], [c])
apply rule = many
  where many :: [a] -> [b] -> ([b], [c])
        many givens []               = ([], [])
        many givens (wanted:wanteds) = case many' givens wanted of
            Nothing    -> first (wanted:)             $ many givens wanteds -- Didn't interact so still normalised since it was before
            Just mb_c' -> second (maybe id (:) mb_c') $ many givens wanteds

        -- NB: very similar to interactMany'
        many' :: [a] -> b -> Maybe (Maybe c)
        many' []             wanted = Nothing
        many' (given:givens) wanted = case rule given wanted of
            Nothing    -> many' givens wanted
            Just mb_c' -> Just mb_c'


topReactGivenMany :: TyVarLike tv => [TopLevelImplication tv] -> [BaseConstraint tv] -> ([BaseConstraint tv], [BaseConstraint tv])
topReactGivenMany tlis = second concat . apply topReactGiven tlis

topReactGiven :: TyVarLike tv => TopLevelImplication tv -> BaseConstraint tv -> Maybe (Maybe [BaseConstraint tv])
topReactGiven (TLI _ _ (I cls1 tys1)) (Instance (I cls2 tys2))
  -- DINSTG
  | cls1 == cls2
  , Just _ <- zipWithM antiSubst tys1 tys2 >>= joinSubsts
  = error "FIXME: fail"
topReactGiven (TLE tvs tf1a tys1a ty1b) (Equality (TyFamApp tf2a tys2b :~ ty2b))
  -- FINST[g]
  -- TODO: share code with FINST[w]
  | tf1a == tf2a
  , Just theta <- zipWithM antiSubst tys1a tys2b >>= joinSubsts
  , let tvs_c = tvs \\ S.toList (S.unions (map fvs tys1a))
        tvs_gamma = error "FIXME: fresh" tvs_c
        theta' = theta `M.union` M.fromList (tvs_c `zip` map TyVar tvs_gamma)
  = Just $ Just [Equality (subst theta ty1b :~ ty2b)]
topReactGiven _ _ = Nothing


topReactWantedMany :: TyVarLike tv => [TopLevelImplication tv] -> [BaseConstraint tv] -> ([tv], [BaseConstraint tv], [BaseConstraint tv])
topReactWantedMany tlis wanteds = (touchables', wanteds', wanteds_denorm')
  where (wanteds', (touchables', wanteds_denorm')) = second ((concat *** concat) . unzip) $ apply topReactWanted tlis wanteds

topReactWanted :: TyVarLike tv => TopLevelImplication tv -> BaseConstraint tv -> Maybe (Maybe ([tv], [BaseConstraint tv]))
topReactWanted tli c | trace ("topReactWanted " ++ prettyShow (tli ,c)) False = undefined
topReactWanted (TLI tvs required (I cls1 tys1)) (Instance (I cls2 tys2))
  -- DINSTW
  | cls1 == cls2
  , Just theta <- zipWithM antiSubst tys1 tys2 >>= joinSubsts
  , let tvs_c = tvs \\ S.toList (S.unions (map fvs tys1))
        tvs_gamma = error "FIXME: fresh" tvs_c
        theta' = theta `M.union` M.fromList (tvs_c `zip` map TyVar tvs_gamma)
  = Just $ Just (tvs_gamma, map (substConstraint theta') required)
topReactWanted (TLE tvs tf1a tys1a ty1b) (Equality (TyFamApp tf2a tys2b :~ ty2b))
  -- FINST[w]
  -- TODO: share code with FINST[g]
  | tf1a == tf2a
  , Just theta <- zipWithM antiSubst tys1a tys2b >>= joinSubsts
  , let tvs_c = tvs \\ S.toList (S.unions (map fvs tys1a))
        tvs_gamma = error "FIXME: fresh" tvs_c
        theta' = theta `M.union` M.fromList (tvs_c `zip` map TyVar tvs_gamma)
  = Just $ Just (tvs_gamma, [Equality (subst theta ty1b :~ ty2b)])
topReactWanted _ _ = Nothing


a = TcSkolem "a"; aTy = TyVar a
b = TcSkolem "b"; bTy = TyVar b

alpha = TcUnif "alpha"; alphaTy = TyVar alpha
beta  = TcUnif "beta";  betaTy  = TyVar beta

list ty = TyConApp "[]" [ty]
eq ty = I "Eq" [ty]


tests = [
    -- p19
    (solve [TLI [a] [Instance (eq aTy)] (eq (list aTy))]
           [] [alpha, beta]
           ([], [Instance (eq alphaTy), Equality (list betaTy :~ alphaTy)]),
     Just ([Instance (eq betaTy)], M.singleton alpha (list betaTy)))
  ]

main :: IO ()
main = forM_ tests $ \(actual, expected) -> do
  if fmap (fmapFst sort) actual == fmap (fmapFst sort) expected
   then return ()
   else putStrLn $ prettyShow actual ++ "\n /=\n" ++ prettyShow expected


{-
solve :: TyVarLike tv
      => [TopLevelImplication tv] -> [BaseConstraint tv] -> [tv] -> Implications tv
      -> Maybe ([BaseConstraint tv], TySubst tv)

-}