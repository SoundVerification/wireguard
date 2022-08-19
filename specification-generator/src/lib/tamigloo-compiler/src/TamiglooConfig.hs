module TamiglooConfig(


        defaultConfig
    ,   tamiglooReadConfig

    ,   defaultRelativePaths
    ,   defaultRelativeModules


) where

import              Prelude
import qualified    Data.Map as Map
import              System.FilePath

-- Takes the inputConfig from user and fills up unspecified options with the defaults
-- Also calculates the paths for import statements, etc and adds them to config
-- A minimal working input config needs to contain the base_dir and input_file key
defaultConfig :: Map.Map String String -> Map.Map String String
defaultConfig inputConfig =
    let 
        -- Map.union is left-biased: in case of duplicates left value is kept
        -- add default options if not specified
        config = Map.union inputConfig defaultOptions
    in
        Map.union 
            config $
            Map.union 
                (defaultModules config) $ -- add package names for input 
                defaultPaths config -- add paths for output files

-- package names with modules prefix. Used for import statements
defaultModules :: Map.Map String String -> Map.Map String String
defaultModules config =
    let
        baseMod = config Map.! "module"
    in
        Map.map (baseMod </>) defaultRelativeModules

-- package names
defaultRelativeModules :: Map.Map String String
defaultRelativeModules = 
    Map.fromList(
        [ ("mod_iospec", "iospec")
        , ("mod_claim", "claim")
        , ("mod_fact", "fact")
        , ("mod_term", "term")
        , ("mod_place", "place")
        , ("mod_pub", "pub")
        , ("mod_fresh", "fresh")
        ])

-- supported options
defaultOptions :: Map.Map String String
defaultOptions =
    Map.fromList(
        [ ("triggers", "Lhs")
        , ("module", "")
        , ("gobra_jar", "")
        , ("input_file", "")
        , ("make_go_mod", "False") 
        , ("verifier", "gobra")
        -- ("base_dir", "needs to be specified")
        ])

-- paths of output files
defaultPaths :: Map.Map String String -> Map.Map String String
defaultPaths config =
    let
        baseDir = config Map.! "base_dir"
    in
        Map.map (baseDir </>) defaultRelativePaths

-- paths of file outputs relative to a base directory
defaultRelativePaths :: Map.Map String String
defaultRelativePaths =
    (Map.map addSuffix $ Map.mapKeys modToPath $ filterMod defaultRelativeModules)
    where
        -- returns keys starting with "mod"
        filterMod :: Map.Map String String -> Map.Map String String
        filterMod = Map.filterWithKey (\k _ -> takeWhile (/= '_') k == "mod")
        modToPath :: String -> String
        modToPath s = "path" ++ (dropWhile (/= '_') s)
        -- adds a file of the same name to the directory s
        addSuffix :: String -> String
        addSuffix s = s </> (s++".gobra")

-- reads a file (containing an even number of whitespace separated words)
-- and turns it into a String key-value Map
tamiglooReadConfig :: FilePath -> IO (Map.Map String String)
tamiglooReadConfig inFile = do
    inp <- readFile inFile
    return (readConfig inp)

-- Takes a String of an even number of whitespace separated words
-- and turns them into a String key-value Map
readConfig :: String -> Map.Map String String
readConfig s = 
    let
        ws = words s
    in
        if odd (length ws)
        then error "odd number of config words"
        else Map.fromList (makePairs ws)
    where
        makePairs :: [a] -> [(a,a)]
        makePairs [] = []
        makePairs (a:b:cs) = (a, b) : (makePairs cs)
        makePairs [_] = error "Should not be here: makePairs singleton list"


