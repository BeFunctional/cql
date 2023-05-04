{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Algebra.PartialOrd
import Data.Bifunctor (bimap)
import qualified Data.Char as Char
import Data.List (intercalate)
import Data.Map (mapMaybe)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set hiding (filter, foldr)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Language.CQL (Env, runProg)
import Language.CQL.Program
import Language.CQL.Schema hiding (Att, Fk)
import Language.CQL.Term hiding (Att, Fk)
import Options.Applicative

-- Create a SchemaEntity type to represent the minimal set of schema entities
data SchemaEntity = SchemaEntity
  { schemaName :: SchemaName,
    minimalEntities :: Set Entity
  }
  deriving stock (Eq, Show)

instance PartialOrd SchemaEntity where
  leq a b = minimalEntities a `leq` minimalEntities b

newtype Entity = Entity {unEntity :: String}
  deriving stock (Eq, Ord, Show)

newtype Fk = Fk {unFk :: String}
  deriving stock (Eq, Ord, Show)

newtype Att = Att {unAtt :: String}
  deriving stock (Eq, Ord, Show)

newtype Ty = Ty {unTy :: String}
  deriving stock (Eq, Ord, Show)

newtype SchemaName = SchemaName {unSchemaName :: String}
  deriving stock (Eq, Ord, Show)

newtype EntityDefintions = EntityDefintions
  { unEntityDefinition ::
      Map.Map
        Entity
        ( Set (Main.Fk, Entity),
          Set (Main.Att, Ty)
        )
  }
  deriving newtype (Eq, Monoid, Show)

instance Semigroup EntityDefintions where
  (<>) (EntityDefintions a) (EntityDefintions b) =
    EntityDefintions $
      Map.unionWith go a b
    where
      go (as, bs) (as', bs') = (as <> as', bs <> bs')

takeSchemas :: (Prog, Types, Env) -> Ctx SchemaName SchemaEx
takeSchemas (_, _, e) = Map.mapKeys SchemaName (schemas e)

schemaEntities :: SchemaEx -> Set Entity
schemaEntities (SchemaEx s) = Set.map (Entity . show) (ens s)

schemaFks :: SchemaEx -> Map.Map Main.Fk (Entity, Entity)
schemaFks (SchemaEx s) =
  bimap (Entity . show) (Entity . show)
    <$> Map.mapKeys (Fk . show) (fks s)

fkDomainEntities :: Map.Map Main.Fk (Entity, Entity) -> Set Entity
fkDomainEntities m = Set.fromList $ fmap fst (Map.elems m)

schemaAtts :: SchemaEx -> Map.Map Main.Att (Entity, Ty)
schemaAtts (SchemaEx s) =
  bimap (Entity . show) (Ty . show)
    <$> Map.mapKeys (Att . show) (atts s)

maybeEntityDomain :: (Ord a) => Set a -> Map.Map k (a, b) -> Map.Map k (a, b)
maybeEntityDomain ent =
  mapMaybe
    ( \v ->
        if (`Set.member` ent)
          . fst
          $ v
          then Just v
          else Nothing
    )

extract :: String -> EntityDefintions
extract src = foldr accR mempty scms
  where
    go (Right e) = e
    go (Left err) = error err
    scms = takeSchemas . go . runProg $ src
    accR :: SchemaEx -> EntityDefintions -> EntityDefintions
    accR scex eds =
      EntityDefintions
        (Map.unionsWith (<>) [ents', atts, fks])
        <> eds
      where
        grp ::
          (Ord a, Ord k, Ord b) =>
          Map.Map k (a, b) ->
          Map.Map a (Set (k, b))
        grp =
          Map.foldrWithKey'
            ( \k (a, b) acc ->
                Map.insertWith (<>) a (Set.singleton (k, b)) acc
            )
            mempty
        fks =
          fmap (,mempty) . grp
            . maybeEntityDomain ents
            $ schemaFks scex
        ents = schemaEntities scex
        ents' =
          Map.fromList
            (((,(mempty, mempty))) <$> Set.toList ents)
        atts =
          fmap (mempty,) . grp
            . maybeEntityDomain ents
            $ schemaAtts scex

capitalized :: String -> String
capitalized ('"' : tail) = capitalized tail
capitalized (head : tail) = Char.toUpper head : tail
capitalized [] = []

lowerCased :: [Char] -> [Char]
lowerCased ('"' : tail) = lowerCased tail
lowerCased [] = []
lowerCased (head : tail) = Char.toLower head : tail

toCamelCase :: String -> String
toCamelCase [] = []
toCamelCase ('"' : tail) = toCamelCase tail
toCamelCase (x : xs) = Char.toLower x : go False xs
  where
    go _ [] = []
    go capitalize (y : ys)
      | y == '_' = go True ys
      | y == '"' = go capitalize ys
      | y == '"' = go capitalize ys
      | capitalize = Char.toUpper y : go False ys
      | otherwise = y : go False ys

capAndCamel :: String -> String
capAndCamel = capitalized . toCamelCase

generateRecord :: String -> String -> Entity -> Set (Fk, Entity) -> Set (Att, Ty) -> String
generateRecord typeSuffix ctorSuffix (Entity e') fks atts =
  unlines
    [ mempty,
      "newtype " ++ pktypeName ++ " = " ++ pkctorName ++ " {un" ++ pkctorName ++ " :: UUID} deriving stock (Eq, Ord, Show)",
      "    deriving newtype (NFData, ToJSON, FromJSON)",
      "",
      "data " ++ e ++ " f = " ++ e,
      "  { " ++ lowerCased e ++ "Id :: f (" ++ pktypeName ++ ")",
      fkFields,
      attFields,
      "  } deriving Generic"
    ]
    <> generateBarbieDeriving
      e
      [ "Show",
        "Eq",
        "Ord",
        "NFData",
        "FromJSON",
        "ToJSON",
        "Semigroup",
        "Monoid"
      ]
  where
    e = capAndCamel e'
    pktypeName = e <> typeSuffix
    pkctorName = e <> ctorSuffix
    fkFields = unlines . Set.toList . Set.map (\(Fk fk, Entity ref) -> "  , " ++ toCamelCase fk ++ " :: f (" ++ (capAndCamel ref <> typeSuffix) ++ ")") $ fks
    attFields = unlines . Set.toList . Set.map (\(Att att, Ty ty) -> "  , " ++ toCamelCase att ++ " :: f " ++ generateType ty) $ atts
    generateType name = case map Char.toLower $ filter (not . Char.isPunctuation) name of
      "integer" -> "Integer -- Sumtype tbd"
      "int" -> "Int32"
      "bigint" -> "Int64"
      "smallint" -> "Int"
      "float" -> "Float"
      "double" -> "Double"
      "real" -> "Double"
      "numeric" -> "Double"
      "timestamp" -> "UTCTime"
      "timestamptz" -> "UTCTime"
      "date" -> "Day"
      "time" -> "TimeOfDay"
      "timetz" -> "TimeOfDay"
      "uuid" -> "UUID"
      "UUID" -> "UUID"
      "text" -> "Text"
      "varchar" -> "Text"
      "character varying" -> "Text"
      "jsonb" -> "Value"
      a -> a

    generateBarbieDeriving tableName instances =
      intercalate
        "\n"
        $ fmap
          ( \i ->
              "deriving instance AllBF "
                <> i
                <> " f "
                <> tableName
                <> " => "
                <> i
                <> " ("
                <> tableName
                <> "  f)"
          )
          instances

generateDbRecord :: EntityDefintions -> Text
generateDbRecord (EntityDefintions defs) =
  T.pack
    . unlines
    $ [ mempty,
        "data Db f = Db",
        "  { " ++ fields,
        "  } deriving Generic"
      ]
  where
    fields = intercalate "\n  , " . map (\(Entity e) -> toCamelCase e ++ " :: f " ++ capAndCamel e) $ Map.keys defs

-- Update the generateEntityRecords function to accept a SchemaEx
generateEntityRecords :: String -> String -> SchemaEx -> EntityDefintions -> Text
generateEntityRecords typeSuffix ctorSuffix schema (EntityDefintions defs) =
  T.pack $
    concatMap generateRecordFromDefinition (Map.toList relevantDefs)
  where
    relevantDefs = Map.filterWithKey (\k _ -> k `Set.member` schemaEntities schema) defs
    generateRecordFromDefinition (entity, (fks, atts)) = generateRecord typeSuffix ctorSuffix entity fks atts

-- Update the moduleHeader function to accept a schema name and import the necessary entity modules
moduleHeader :: String -> String -> SchemaName -> Set Entity -> T.Text
moduleHeader typeSuffix preFix (SchemaName schemaName) imports =
  T.pack
    . unlines
    $ [ "{-# LANGUAGE DeriveAnyClass #-}",
        "{-# LANGUAGE DeriveGeneric #-}",
        "{-# LANGUAGE DerivingVia #-}",
        "{-# LANGUAGE FlexibleContexts #-}",
        "{-# LANGUAGE TypeFamilies #-}",
        "",
        "module " ++ preFix ++ schemaName ++ " where",
        "",
        "import Data.Int (Int64)",
        "import Data.Aeson (FromJSON, ToJSON)",
        "import Data.Barbie (AllBF, ApplicativeB, ConstraintsB, FunctorB, TraversableB)",
        "import GHC.Generics (Generic)",
        "import Control.DeepSeq (NFData)",
        "import Data.Semigroup (Semigroup)",
        "import Data.Monoid (Monoid)"
      ]
      ++ importList
  where
    importList = map (\(Entity e) -> "import " ++ preFix ++ capAndCamel e ++ " (" ++ (capAndCamel e <> typeSuffix) ++ ")") $ Set.toList imports

minimalSets :: [SchemaEntity] -> [SchemaEntity]
minimalSets entities = out
  where
    out = fmap minimize entities
    minimize e =
      e
        { minimalEntities =
            Set.difference
              (minimalEntities e)
              ( Set.unions
                  [minimalEntities x | x <- entities, x /= e, leq x e]
              )
        }

-- Function to filter EntityDefinitions for a specific schema
filterEntityDefinitionsForSchema :: Set Entity -> EntityDefintions -> EntityDefintions
filterEntityDefinitionsForSchema entities (EntityDefintions defs) =
  EntityDefintions $ Map.filterWithKey (\k _ -> k `Set.member` entities) defs

data GenSchema = HKD | Beam
  deriving stock (Show, Read, Eq, Enum, Bounded)

data Options = Options
  { filePath :: String,
    modulePrefix :: String,
    primaryKeyTypeSuffix :: String,
    primaryKeyCtorSuffix :: String,
    schemaOption :: GenSchema
  }
  deriving stock (Show)

genSchemaParser :: Parser GenSchema
genSchemaParser =
  flag' HKD (long "hkd" <> help "generate higher-kinded-data with barbies instances")
    <|> flag' Beam (long "beam" <> help "generate a beam database schema with beam instances")

optionsParser :: Parser Options
optionsParser =
  Options
    <$> strOption
      ( long "file" <> short 'f'
          <> metavar "FILE"
          <> help "File path to read content from"
      )
    <*> strOption
      ( long "module" <> short 'm'
          <> metavar "STRING"
          <> help "the string prefiex to use for modules"
      )
    <*> strOption
      ( long "type-suffix" <> short 's'
          <> metavar "STRING"
          <> help "the string suffix to use for primary key types"
      )
    <*> strOption
      ( long "constructor-suffix" <> short 'c'
          <> metavar "STRING"
          <> help "the string suffix to use for primary key constructors"
          <> showDefault
          <> value "UUID"
      )
    <*> genSchemaParser

main :: IO ()
main = do
  Options {..} <-
    execParser $
      info
        (optionsParser <**> helper)
        ( fullDesc
            <> progDesc "Generate haskell datatypes from a CQL specification"
        )
  if Beam == schemaOption
    then putStrLn "Beam codegen not yet implemented"
    else do
      src <-
        readFile
          filePath
      let entityDefs = extract src
      let go (Right e) = e
          go (Left err) = error err
      let scms = takeSchemas . go . runProg $ src
      let minimalSchemaEntities =
            minimalSets
              . fmap
                ( \(schemaName, schemaEx) ->
                    SchemaEntity schemaName (schemaEntities schemaEx)
                )
              . Map.toList
              $ scms
      let minimalSchemaEntitiesMap =
            Map.fromList
              . fmap
                ( \(SchemaEntity schemaName entities) ->
                    (schemaName, entities)
                )
              $ minimalSchemaEntities
      print minimalSchemaEntities
      let genPath = "gen/"

      -- Generate one file per schema
      mapM_
        ( \(schemaName, schema) -> do
            let minimalEntities =
                  Map.findWithDefault
                    Set.empty
                    schemaName
                    minimalSchemaEntitiesMap
            let filteredEntityDefs = filterEntityDefinitionsForSchema minimalEntities entityDefs
            let imports =
                  Set.unions $
                    fmap (schemaEntities . snd) $
                      filter (\(k, _) -> k /= schemaName) $ Map.toList scms
            T.writeFile
              (genPath <> unSchemaName schemaName ++ ".hs")
              ( moduleHeader primaryKeyTypeSuffix modulePrefix schemaName imports
                  <> generateEntityRecords primaryKeyTypeSuffix primaryKeyCtorSuffix schema filteredEntityDefs
              )
        )
        $ Map.toList scms

      -- Generate Db module
      let dbModuleName = "Db"
      let dbImports = (\(SchemaName name, _) -> "import " ++ modulePrefix ++ name) <$> Map.toList scms
      T.writeFile
        (genPath <> dbModuleName ++ ".hs")
        ( dbModuleHeader
            (modulePrefix <> dbModuleName)
            dbImports
            <> generateDbRecord entityDefs
        )

-- Function to generate the module header for the Db module
dbModuleHeader :: String -> [String] -> Text
dbModuleHeader moduleName imports =
  T.pack . unlines $
    [ "{-# LANGUAGE DeriveAnyClass #-}",
      "{-# LANGUAGE DeriveGeneric #-}",
      "{-# LANGUAGE DerivingVia #-}",
      "{-# LANGUAGE FlexibleContexts #-}",
      "{-# LANGUAGE TypeFamilies #-}",
      "",
      "module " ++ moduleName ++ " where",
      ""
    ]
      ++ imports
      ++ [ "",
           "import Data.Int (Int64)",
           "import Data.Aeson (FromJSON, ToJSON)",
           "import Data.Barbie (AllBF, ApplicativeB, ConstraintsB, FunctorB, TraversableB)",
           "import GHC.Generics (Generic)",
           "import Control.DeepSeq (NFData)",
           "import Data.Semigroup (Semigroup)",
           "import Data.Monoid (Monoid)",
           ""
         ]
