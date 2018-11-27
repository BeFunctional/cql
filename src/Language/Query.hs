{-# LANGUAGE ExplicitForAll, StandaloneDeriving, DuplicateRecordFields, ScopedTypeVariables, InstanceSigs, KindSignatures, GADTs, FlexibleContexts, RankNTypes, TypeSynonymInstances, FlexibleInstances, MultiParamTypeClasses, AllowAmbiguousTypes, TypeOperators
,LiberalTypeSynonyms, ImpredicativeTypes, UndecidableInstances, FunctionalDependencies, DataKinds #-}

module Language.Query where
import Prelude hiding (EQ)
import Data.Set as Set
import Data.Map.Strict as Map
import Language.Term
import Data.Void
import Language.Schema
import Language.Common
import Control.DeepSeq

data Query var ty sym en fk att en' fk' att'
  = Query
  { srcQ :: Schema var ty sym en  fk  att
  , dstQ :: Schema var ty sym en' fk' att'

  , ens  :: Map en'  (Ctx  var en, Set (EQ   var ty   sym  en fk att  Void Void))
  , fks  :: Map fk'  (Ctx  var         (Term var Void Void en fk Void Void Void))
  , atts :: Map att'                   (Term var ty   sym  en fk att  Void Void)
  }

instance (Show var, Show ty, Show sym, Show en, Show fk, Show att, Show en', Show fk', Show att')
  => Show (Query var ty sym en fk att en' fk' att') where
  show (Query _ _ ens' fks' atts') =
      "ens = "  ++ show ens'  ++
    "\nfks = "  ++ show fks'  ++
    "\natts = " ++ show atts'

instance (Eq var, Eq ty, Eq sym, Eq en, Eq fk, Eq att, Eq en', Eq fk', Eq att')
  => Eq (Query var ty sym en fk att en' fk' att') where
  (==) (Query s1' s2' ens' fks' atts') (Query s1'' s2'' ens'' fks'' atts'')
    = (s1' == s1'') && (s2' == s2'') && (ens' == ens'') && (fks' == fks'') && (atts' == atts'')

instance (NFData var, NFData ty, NFData sym, NFData en, NFData fk, NFData att, NFData en', NFData fk', NFData att')
  => NFData (Query var ty sym en fk att en' fk' att') where
  rnf (Query s t e f a) = deepseq s $ deepseq t $ deepseq e $ deepseq f $ rnf a

data QueryEx :: * where
  QueryEx
    :: forall var ty sym en fk att en' fk' att'
    .  (ShowOrdTypeableN '[var, ty, sym, en, fk, att, en', fk', att'])
    => Query var ty sym en fk att en' fk' att' -> QueryEx

instance NFData QueryEx where
  rnf (QueryEx x) = rnf x

deriving instance Show QueryEx

data QueryExp where
  QueryVar     :: String       -> QueryExp
  QueryId      :: SchemaExp    -> QueryExp
  QueryRaw     :: QueryExpRaw' -> QueryExp
  deriving (Eq)

instance Show QueryExp where
  show _ = error "todo"

instance Deps QueryExp where
  deps x = case x of
    QueryVar v -> [(v, QUERY)]
    QueryId  s -> deps s
    QueryRaw (QueryExpRaw' s t _ _ _ _ i)  -> deps s ++ deps t ++ concatMap deps i

getOptionsQuery :: QueryExp -> [(String, String)]
getOptionsQuery x = case x of
  QueryVar _ -> []
  QueryId  _ -> []
  QueryRaw (QueryExpRaw' _ _ _ _ _ o _) -> o

--old school queries without overlapping names across entities
data QueryExpRaw' = QueryExpRaw'
  { qraw_src     :: SchemaExp
  , qraw_dst     :: SchemaExp
  , qraw_ens  :: [(String, ([(String,String)],[(RawTerm,RawTerm)]))]
  , qraw_fks :: [(String, [(String,RawTerm)])]
  , qraw_atts  :: [(String, RawTerm)]
  , qraw_options :: [(String, String)]
  , qraw_imports :: [QueryExp]
} deriving (Eq, Show)

typecheckQuery
  :: -- (ShowOrdN '[var, ty], ShowOrdTypeableN '[sym, en, fk, att, en', fk', att'])
  => Query var ty sym en fk att en' fk' att'
  -> Err ()
typecheckQuery = undefined

--------------------------------------------------------------------------------
