{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  ProtocolFormat(factSigAct, factSigEnv, factSigState, extractEnvRules,
                  extractStateRulesWithRole, extractFactsWithRole)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified List;
import qualified Arith;
import qualified HOL;
import qualified GenericHelperFunctions;
import qualified TamiglooDatatypes;

getRole :: TamiglooDatatypes.Rule -> String;
getRole (TamiglooDatatypes.Rule (TamiglooDatatypes.StateRule s) uu uv uw ux) =
  s;
getRole (TamiglooDatatypes.Rule TamiglooDatatypes.EnvRule va vb vc vd) =
  error "undefined";

factSigAct :: TamiglooDatatypes.Theory -> [TamiglooDatatypes.FactTag];
factSigAct thy =
  GenericHelperFunctions.nub
    (map TamiglooDatatypes.accFactTag
      (concatMap TamiglooDatatypes.getActFacts
        (TamiglooDatatypes.extractRules thy)));

factSigEnv :: TamiglooDatatypes.Theory -> [TamiglooDatatypes.FactTag];
factSigEnv thy =
  GenericHelperFunctions.nub
    (map TamiglooDatatypes.accFactTag
      (concatMap TamiglooDatatypes.getEnvFacts
        (TamiglooDatatypes.extractRules thy)));

getFactsWithRole ::
  TamiglooDatatypes.Rule -> [(String, TamiglooDatatypes.Fact)];
getFactsWithRole r =
  let {
    roles =
      List.replicate (List.size_list (TamiglooDatatypes.getFacts r))
        (getRole r);
  } in zip roles (TamiglooDatatypes.getFacts r);

factSigState ::
  TamiglooDatatypes.Theory -> [(String, [TamiglooDatatypes.FactTag])];
factSigState thy =
  let {
    stateRules =
      filter TamiglooDatatypes.isStateRule (TamiglooDatatypes.extractRules thy);
    stateFacts =
      filter (TamiglooDatatypes.isStateFact . snd)
        (concatMap getFactsWithRole stateRules);
  } in GenericHelperFunctions.sortIntoBuckets
         (GenericHelperFunctions.nubBy
           (\ p1 p2 -> TamiglooDatatypes.equal_FactTag (snd p1) (snd p2))
           (map (\ p -> (fst p, TamiglooDatatypes.accFactTag (snd p)))
             stateFacts));

extractEnvRules :: TamiglooDatatypes.Theory -> [TamiglooDatatypes.Rule];
extractEnvRules thy =
  filter TamiglooDatatypes.isEnvRule (TamiglooDatatypes.extractRules thy);

getRuleWithRole :: TamiglooDatatypes.Rule -> (String, TamiglooDatatypes.Rule);
getRuleWithRole r =
  (if TamiglooDatatypes.isStateRule r then (getRole r, r)
    else error "undefined");

extractStateRulesWithRole ::
  TamiglooDatatypes.Theory -> [(String, TamiglooDatatypes.Rule)];
extractStateRulesWithRole thy =
  let {
    a = filter TamiglooDatatypes.isStateRule
          (TamiglooDatatypes.extractRules thy);
  } in map getRuleWithRole a;

extractFactsWithRole ::
  TamiglooDatatypes.Theory -> [(String, TamiglooDatatypes.Fact)];
extractFactsWithRole thy =
  let {
    a = GenericHelperFunctions.sndList (extractStateRulesWithRole thy);
  } in concatMap getFactsWithRole a;

}
