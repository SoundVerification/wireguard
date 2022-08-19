{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  InterfaceModel(extractIoRulesWithRole, factSigBuf, extractEnvMinusRules,
                  extractStateRulesWithRid)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified ProtocolFormat;
import qualified Arith;
import qualified GenericHelperFunctions;
import qualified List;
import qualified HOL;
import qualified TamiglooDatatypes;

extractSetupRulesWithRole ::
  TamiglooDatatypes.Theory -> [(String, TamiglooDatatypes.Rule)];
extractSetupRulesWithRole thy =
  List.map_filter
    (\ x ->
      (if TamiglooDatatypes.isSetupRule x
        then Just (TamiglooDatatypes.getRoleFromSetupFact
                     (List.hd (TamiglooDatatypes.accCncl x)),
                    x)
        else Nothing))
    (TamiglooDatatypes.extractRules thy);

isEnvInMinusFact :: TamiglooDatatypes.Fact -> Bool;
isEnvInMinusFact f =
  TamiglooDatatypes.isEnvInFact f && not (TamiglooDatatypes.isSetupFact f);

envInMinusFactSigWithRole ::
  TamiglooDatatypes.Theory -> [(String, TamiglooDatatypes.Fact)];
envInMinusFactSigWithRole thy =
  GenericHelperFunctions.nubBy
    (\ p1 p2 ->
      TamiglooDatatypes.eqFactSig (snd p1) (snd p2) && fst p1 == fst p2)
    (filter (isEnvInMinusFact . snd) (ProtocolFormat.extractFactsWithRole thy));

envOutFactSigWithRole ::
  TamiglooDatatypes.Theory -> [(String, TamiglooDatatypes.Fact)];
envOutFactSigWithRole thy =
  GenericHelperFunctions.nubBy
    (\ p1 p2 ->
      TamiglooDatatypes.eqFactSig (snd p1) (snd p2) && fst p1 == fst p2)
    (filter (TamiglooDatatypes.isEnvOutFact . snd)
      (ProtocolFormat.extractFactsWithRole thy));

makeNameBufferOutFact :: String -> TamiglooDatatypes.Fact -> String;
makeNameBufferOutFact role f =
  GenericHelperFunctions.prependToString (TamiglooDatatypes.getNameFact f) role;

createNewLVar :: ForeignImports.LSort -> Arith.Nat -> ForeignImports.LVar;
createNewLVar lsort n =
  ForeignImports.LVar "new_x" lsort (Arith.integer_of_nat n);

createNewLNTerms ::
  Arith.Nat ->
    ForeignImports.LSort ->
      [ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar)];
createNewLNTerms n lsort =
  let {
    a = map (createNewLVar lsort) (List.upt Arith.zero_nat n);
  } in map (\ v -> ForeignImports.LIT (ForeignImports.Var v)) a;

createNewProtoFact ::
  String -> TamiglooDatatypes.Fact -> TamiglooDatatypes.Fact;
createNewProtoFact newName (TamiglooDatatypes.Fact fGroup fTag termList) =
  let {
    ar = TamiglooDatatypes.getFactTagAr fTag;
    newFTag =
      TamiglooDatatypes.ProtoFact
        (if TamiglooDatatypes.isFactTagPers fTag then ForeignImports.Persistent
          else ForeignImports.Linear)
        newName (Arith.integer_of_nat ar);
  } in TamiglooDatatypes.Fact fGroup newFTag termList;

prependTermToFact ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    TamiglooDatatypes.Fact -> TamiglooDatatypes.Fact;
prependTermToFact t f =
  let {
    terms = t : TamiglooDatatypes.accTermList f;
  } in TamiglooDatatypes.addToFactAr (1 :: Integer)
         (TamiglooDatatypes.replaceTermsFact terms f);

createBufferFact ::
  String ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      TamiglooDatatypes.Fact -> TamiglooDatatypes.Fact;
createBufferFact newName rid oldFact =
  prependTermToFact rid (createNewProtoFact newName oldFact);

createIoOutRule ::
  (String, TamiglooDatatypes.Fact) -> (String, TamiglooDatatypes.Rule);
createIoOutRule (role, oldFact) =
  let {
    ruleName =
      GenericHelperFunctions.prependToString "OutIntf"
        (makeNameBufferOutFact role oldFact);
    f = TamiglooDatatypes.replaceTermsFact
          (createNewLNTerms (TamiglooDatatypes.getFactAr oldFact)
            ForeignImports.LSortMsg)
          oldFact;
    rid = ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar "added_rid" ForeignImports.LSortMsg (0
                            :: Integer)));
    frid = createBufferFact (makeNameBufferOutFact role oldFact) rid f;
  } in (role,
         TamiglooDatatypes.Rule TamiglooDatatypes.EnvRule ruleName [frid] []
           [f]);

makeNameBufferInFact :: String -> TamiglooDatatypes.Fact -> String;
makeNameBufferInFact role f =
  GenericHelperFunctions.prependToString (TamiglooDatatypes.getNameFact f) role;

createIoInRule ::
  (String, TamiglooDatatypes.Fact) -> (String, TamiglooDatatypes.Rule);
createIoInRule (role, oldFact) =
  let {
    ruleName =
      GenericHelperFunctions.prependToString "InIntf"
        (makeNameBufferInFact role oldFact);
    lsortF = ForeignImports.LSortMsg;
    f = TamiglooDatatypes.replaceTermsFact
          (createNewLNTerms (TamiglooDatatypes.getFactAr oldFact) lsortF)
          oldFact;
    rid = ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar "added_rid" ForeignImports.LSortMsg (0
                            :: Integer)));
    frid = createBufferFact (makeNameBufferInFact role oldFact) rid f;
  } in (role,
         TamiglooDatatypes.Rule TamiglooDatatypes.EnvRule ruleName [f] []
           [frid]);

extractIoRulesWithRole ::
  TamiglooDatatypes.Theory ->
    ([(String, TamiglooDatatypes.Rule)],
      ([(String, TamiglooDatatypes.Rule)], [(String, TamiglooDatatypes.Rule)]));
extractIoRulesWithRole thy =
  let {
    envInMinusFacts = envInMinusFactSigWithRole thy;
    envOutFacts = envOutFactSigWithRole thy;
    ioInRules = map createIoInRule envInMinusFacts;
    ioOutRules = map createIoOutRule envOutFacts;
    prependToRuleName =
      (\ r ->
        TamiglooDatatypes.updateRuleName
          (GenericHelperFunctions.prependToString "IoInIntf"
            (TamiglooDatatypes.accRuleName r))
          r);
    ioSetupRules =
      map (\ p -> (fst p, prependToRuleName (snd p)))
        (extractSetupRulesWithRole thy);
  } in (ioInRules, (ioOutRules, ioSetupRules));

factSigBuf :: TamiglooDatatypes.Theory -> [(String, [TamiglooDatatypes.Fact])];
factSigBuf thy =
  let {
    bufInCncl =
      map (\ p -> (fst p, List.hd (TamiglooDatatypes.accCncl (snd p))))
        (fst (extractIoRulesWithRole thy));
    bufInPr =
      map (\ p -> (fst p, List.hd (TamiglooDatatypes.accPr (snd p))))
        (fst (snd (extractIoRulesWithRole thy)));
  } in GenericHelperFunctions.sortIntoBuckets (bufInCncl ++ bufInPr);

auxReplaceFacts ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    [(String, TamiglooDatatypes.Fact)] -> [TamiglooDatatypes.Fact];
auxReplaceFacts rid fl =
  map (\ p ->
        (if isEnvInMinusFact (snd p)
          then createBufferFact (makeNameBufferInFact (fst p) (snd p)) rid
                 (snd p)
          else (if TamiglooDatatypes.isEnvOutFact (snd p)
                 then createBufferFact (makeNameBufferOutFact (fst p) (snd p))
                        rid (snd p)
                 else snd p)))
    fl;

addRidToFactsInARule ::
  (String, TamiglooDatatypes.Rule) -> (String, TamiglooDatatypes.Rule);
addRidToFactsInARule (role, TamiglooDatatypes.Rule rGroup rName pr ac cncl) =
  let {
    rid = (((List.hd . TamiglooDatatypes.accTermList) . List.hd) .
            TamiglooDatatypes.getStateFacts)
            (TamiglooDatatypes.Rule rGroup rName pr ac cncl);
    prid = auxReplaceFacts rid (map (\ a -> (role, a)) pr);
    acid = auxReplaceFacts rid (map (\ a -> (role, a)) ac);
    cnid = auxReplaceFacts rid (map (\ a -> (role, a)) cncl);
  } in (role, TamiglooDatatypes.Rule rGroup rName prid acid cnid);

extractEnvMinusRules :: TamiglooDatatypes.Theory -> [TamiglooDatatypes.Rule];
extractEnvMinusRules thy =
  filter (\ r -> not (TamiglooDatatypes.isSetupRule r))
    (ProtocolFormat.extractEnvRules thy);

extractStateRulesWithRid ::
  TamiglooDatatypes.Theory -> [(String, TamiglooDatatypes.Rule)];
extractStateRulesWithRid thy =
  map addRidToFactsInARule (ProtocolFormat.extractStateRulesWithRole thy);

}
