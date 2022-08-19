{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Decomposition(extractIoEnvAndIoProtoRules, extractProtoAndIoRules,
                 extractEnvMinusAndIoRules)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified InterfaceModel;
import qualified GenericHelperFunctions;
import qualified List;
import qualified HOL;
import qualified TamiglooDatatypes;
import qualified Arith;

splitIoInRule ::
  (String, TamiglooDatatypes.Rule) ->
    (TamiglooDatatypes.Rule, (String, TamiglooDatatypes.Rule));
splitIoInRule (role, TamiglooDatatypes.Rule rGroup rName pr ac cncl) =
  let {
    terms = TamiglooDatatypes.accTermList (List.hd cncl);
    ruleName =
      GenericHelperFunctions.prependToString "In"
        (GenericHelperFunctions.splitAndGetSnd rName);
    slName =
      GenericHelperFunctions.prependToString "slIn"
        (TamiglooDatatypes.getNameFact (List.hd pr));
    sl = TamiglooDatatypes.Fact TamiglooDatatypes.ActionGroup
           (TamiglooDatatypes.ProtoFact ForeignImports.Linear slName
             (Arith.integer_of_nat (List.size_list terms)))
           terms;
  } in (TamiglooDatatypes.Rule rGroup ruleName pr (sl : ac) [],
         (role, TamiglooDatatypes.Rule rGroup ruleName [] (sl : ac) cncl));

splitIoOutRule ::
  (String, TamiglooDatatypes.Rule) ->
    ((String, TamiglooDatatypes.Rule), TamiglooDatatypes.Rule);
splitIoOutRule (role, TamiglooDatatypes.Rule rGroup rName pr ac cncl) =
  let {
    terms = TamiglooDatatypes.accTermList (List.hd pr);
    ruleName =
      GenericHelperFunctions.prependToString "Out"
        (GenericHelperFunctions.splitAndGetSnd rName);
    slName =
      GenericHelperFunctions.prependToString "slOut"
        (TamiglooDatatypes.getNameFact (List.hd cncl));
    sl = TamiglooDatatypes.Fact TamiglooDatatypes.ActionGroup
           (TamiglooDatatypes.ProtoFact ForeignImports.Linear slName
             (Arith.integer_of_nat (List.size_list terms)))
           terms;
  } in ((role, TamiglooDatatypes.Rule rGroup ruleName pr (sl : ac) []),
         TamiglooDatatypes.Rule rGroup ruleName [] (sl : ac) cncl);

splitIoSetupRule ::
  (String, TamiglooDatatypes.Rule) ->
    (TamiglooDatatypes.Rule, (String, TamiglooDatatypes.Rule));
splitIoSetupRule (role, TamiglooDatatypes.Rule rGroup rName pr ac cncl) =
  let {
    terms = TamiglooDatatypes.accTermList (List.hd cncl);
    ruleName =
      GenericHelperFunctions.prependToString "In"
        (GenericHelperFunctions.splitAndGetSnd rName);
    slName =
      GenericHelperFunctions.prependToString "slIn"
        (TamiglooDatatypes.getNameFact (List.hd cncl));
    sl = TamiglooDatatypes.Fact TamiglooDatatypes.ActionGroup
           (TamiglooDatatypes.ProtoFact ForeignImports.Linear slName
             (Arith.integer_of_nat (List.size_list terms)))
           terms;
  } in (TamiglooDatatypes.Rule rGroup ruleName pr (sl : ac) [],
         (role, TamiglooDatatypes.Rule rGroup ruleName [] (sl : ac) cncl));

extractSplitIoInRules ::
  TamiglooDatatypes.Theory ->
    [(TamiglooDatatypes.Rule, (String, TamiglooDatatypes.Rule))];
extractSplitIoInRules thy =
  let {
    a = fst (InterfaceModel.extractIoRulesWithRole thy);
  } in map splitIoInRule a;

extractSplitIoSetupRules ::
  TamiglooDatatypes.Theory ->
    [(TamiglooDatatypes.Rule, (String, TamiglooDatatypes.Rule))];
extractSplitIoSetupRules thy =
  let {
    a = snd (snd (InterfaceModel.extractIoRulesWithRole thy));
  } in map splitIoSetupRule a;

extractSplitIoOutRules ::
  TamiglooDatatypes.Theory ->
    [(TamiglooDatatypes.Rule, (String, TamiglooDatatypes.Rule))];
extractSplitIoOutRules thy =
  let {
    a = fst (snd (InterfaceModel.extractIoRulesWithRole thy));
  } in map (GenericHelperFunctions.flipPair . splitIoOutRule) a;

extractIoEnvAndIoProtoRules ::
  TamiglooDatatypes.Theory ->
    ([TamiglooDatatypes.Rule],
      ([(String, TamiglooDatatypes.Rule)], [(String, TamiglooDatatypes.Rule)]));
extractIoEnvAndIoProtoRules thy =
  let {
    splitIoInRules = extractSplitIoInRules thy ++ extractSplitIoSetupRules thy;
    splitIoOutRules = extractSplitIoOutRules thy;
    splitIoRules = splitIoInRules ++ splitIoOutRules;
  } in (GenericHelperFunctions.fstList splitIoRules,
         (GenericHelperFunctions.sndList splitIoInRules,
           GenericHelperFunctions.sndList splitIoOutRules));

extractProtoAndIoRules ::
  TamiglooDatatypes.Theory ->
    [(String,
       ([TamiglooDatatypes.Rule],
         ([TamiglooDatatypes.Rule], [TamiglooDatatypes.Rule])))];
extractProtoAndIoRules thy =
  let {
    splitIoRulesState = snd (extractIoEnvAndIoProtoRules thy);
    splitIoInRules = fst splitIoRulesState;
    splitIoOutRules = snd splitIoRulesState;
    stateRules = InterfaceModel.extractStateRulesWithRid thy;
    roles =
      GenericHelperFunctions.nub
        (map fst (stateRules ++ splitIoInRules ++ splitIoOutRules));
    sortedIoIn =
      GenericHelperFunctions.sortIntoBucketsOrdered roles splitIoInRules;
    sortedIoOut =
      GenericHelperFunctions.sortIntoBucketsOrdered roles splitIoOutRules;
    sortedState =
      GenericHelperFunctions.sortIntoBucketsOrdered roles stateRules;
  } in GenericHelperFunctions.zipWith
         (\ pSt pIo -> (fst pSt, (snd pSt, (fst pIo, snd pIo)))) sortedState
         (GenericHelperFunctions.zipWith (\ pIn pOut -> (snd pIn, snd pOut))
           sortedIoIn sortedIoOut);

extractEnvMinusAndIoRules ::
  TamiglooDatatypes.Theory -> [TamiglooDatatypes.Rule];
extractEnvMinusAndIoRules thy =
  InterfaceModel.extractEnvMinusRules thy ++
    fst (extractIoEnvAndIoProtoRules thy);

}
