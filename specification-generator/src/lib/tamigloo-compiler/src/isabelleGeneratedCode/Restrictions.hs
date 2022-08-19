{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Restrictions(ruleRestrs, separateRestr, iosfRestrictions) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import qualified Prelude;
import qualified ForeignImports;
import qualified Arith;
import qualified List;
import qualified HOL;
import qualified GenericHelperFunctions;
import qualified TamiglooDatatypes;

isDbi ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Bool;
isDbi (ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar name lsort i)))
  = (if name == "Bound" then True else False);
isDbi (ForeignImports.LIT (ForeignImports.Con va)) = False;
isDbi (ForeignImports.FAPP v va) = False;

getDbiLit ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Integer;
getDbiLit
  (ForeignImports.LIT (ForeignImports.Var (ForeignImports.LVar name lsort i))) =
  i;
getDbiLit (ForeignImports.LIT (ForeignImports.Con va)) = error "undefined";
getDbiLit (ForeignImports.FAPP v va) = error "undefined";

safeGetDbiLit ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    Maybe Integer;
safeGetDbiLit lnTerm =
  (if isDbi lnTerm then Just (getDbiLit lnTerm) else Nothing);

getDbis ::
  ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
    [Integer];
getDbis lnTerm =
  ((GenericHelperFunctions.collectThe .
     map (safeGetDbiLit . TamiglooDatatypes.varToVTerm)) .
    TamiglooDatatypes.getVarsVTerm)
    lnTerm;

replaceDbiLNTerm ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
        ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar);
replaceDbiLNTerm i repl original =
  (case original of {
    ForeignImports.LIT _ ->
      (if isDbi original && i == getDbiLit original then repl else original);
    ForeignImports.FAPP fun ts ->
      ForeignImports.FAPP fun (map (replaceDbiLNTerm i repl) ts);
  });

replaceDbiAtom ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      TamiglooDatatypes.Atom -> TamiglooDatatypes.Atom;
replaceDbiAtom i t a =
  (case a of {
    TamiglooDatatypes.Atom _ -> a;
    TamiglooDatatypes.EqE t1 t2 ->
      TamiglooDatatypes.EqE (replaceDbiLNTerm i t t1) (replaceDbiLNTerm i t t2);
    TamiglooDatatypes.TF _ -> a;
  });

replaceDbi ::
  Integer ->
    ForeignImports.Term (ForeignImports.Lit ForeignImports.Name ForeignImports.LVar) ->
      TamiglooDatatypes.RestrFormula -> TamiglooDatatypes.RestrFormula;
replaceDbi i t f =
  (case f of {
    TamiglooDatatypes.Ato a -> TamiglooDatatypes.Ato (replaceDbiAtom i t a);
    TamiglooDatatypes.Not fa -> TamiglooDatatypes.Not (replaceDbi i t fa);
    TamiglooDatatypes.Conn conn l r ->
      TamiglooDatatypes.Conn conn (replaceDbi i t l) (replaceDbi i t r);
  });

instantiateRestr ::
  TamiglooDatatypes.Fact ->
    (TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula) ->
      TamiglooDatatypes.RestrFormula;
instantiateRestr f def =
  (if TamiglooDatatypes.eqFactSig f (fst def)
    then let {
           lnTerms = TamiglooDatatypes.accTermList f;
           dbis =
             GenericHelperFunctions.nub
               (concatMap getDbis (TamiglooDatatypes.accTermList (fst def)));
           zipped = zip dbis lnTerms;
         } in List.fold (\ p -> replaceDbi (fst p) (snd p)) zipped (snd def)
    else error "undefined");

instantiateRestrictions ::
  [(TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula)] ->
    TamiglooDatatypes.Fact -> [TamiglooDatatypes.RestrFormula];
instantiateRestrictions restrs actFact =
  List.map_filter
    (\ x ->
      (if TamiglooDatatypes.eqFactSig actFact (fst x)
        then Just (instantiateRestr actFact x) else Nothing))
    restrs;

factListRestrs ::
  [TamiglooDatatypes.Fact] ->
    [(TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula)] ->
      [TamiglooDatatypes.RestrFormula];
factListRestrs acts restrs = concatMap (instantiateRestrictions restrs) acts;

ruleRestrs ::
  [(TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula)] ->
    TamiglooDatatypes.Rule -> [TamiglooDatatypes.RestrFormula];
ruleRestrs restrs r = factListRestrs (TamiglooDatatypes.accAc r) restrs;

separateRestr ::
  TamiglooDatatypes.RestrFormula ->
    (TamiglooDatatypes.Fact, TamiglooDatatypes.RestrFormula);
separateRestr (TamiglooDatatypes.Conn ForeignImports.Imp l r) =
  (case l of {
    TamiglooDatatypes.Ato (TamiglooDatatypes.Atom f) -> (f, r);
  });
separateRestr (TamiglooDatatypes.Ato v) = error "undefined";
separateRestr (TamiglooDatatypes.Not v) = error "undefined";
separateRestr (TamiglooDatatypes.Conn ForeignImports.And va vb) =
  error "undefined";
separateRestr (TamiglooDatatypes.Conn ForeignImports.Or va vb) =
  error "undefined";
separateRestr (TamiglooDatatypes.Conn ForeignImports.Iff va vb) =
  error "undefined";

iosfRestrictions ::
  [TamiglooDatatypes.RestrFormula] -> TamiglooDatatypes.IOSFormula;
iosfRestrictions restrs =
  let {
    iosfRestrs = map TamiglooDatatypes.IOSFRestr restrs;
    n = List.size_list iosfRestrs;
  } in (if Arith.equal_nat n Arith.zero_nat then error "undefined"
         else List.foldl TamiglooDatatypes.IOSFand (List.hd iosfRestrs)
                (List.tl iosfRestrs));

}
