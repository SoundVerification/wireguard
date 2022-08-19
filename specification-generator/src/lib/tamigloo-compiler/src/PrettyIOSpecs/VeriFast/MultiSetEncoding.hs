{-# LANGUAGE QuasiQuotes #-}
module PrettyIOSpecs.VeriFast.MultiSetEncoding (

          hardcodedMsetEncoding
        , mFunc
        , filterIsLinFunc
        , filterIsPersFunc
        , uFunc

  ) where

--
import              Prelude
import              Text.PrettyPrint.Class
import Text.RawString.QQ

{- ---- M(l, s) -}
{- part of the guard condition in an IO spec: ensures that l is a subset of s -}
mFunc :: Document d => d
mFunc = text $ [r|
fixpoint boolean M(mset<Fact> l, mset<Fact> s) {
    return msetIncl(linearFacts(l), s) && msetIncl(persistentFacts(l), s);
}
|]


{- filters a multiset of facts so that only linear/non-persistent facts remain -}
filterIsLinFunc :: Document d => d
filterIsLinFunc = text $ [r|
fixpoint mset<Fact> linearFacts(mset<Fact> l) {
    return msetList(filter(msetToList(l), nonpersistent));
}
|]

{- filters a multiset of facts so that only a set of persistent facts remains -}
filterIsPersFunc :: Document d => d
filterIsPersFunc = text $ [r|
fixpoint mset<Fact> persistentFacts(mset<Fact> l) {
    return msetList(nub(filter(msetToList(l), persistent)));
}
|]

uFunc :: Document d => d
uFunc = text $ [r|
fixpoint mset<Fact> U(mset<Fact> l, mset<Fact> r, mset<Fact> s) {
    return msetUnion(msetMinus(s, linearFacts(l)), r);
}
|]


hardcodedMsetEncoding :: Document d => d
hardcodedMsetEncoding = text $ [r|

inductive mset<T> = msetList(list<T>);


fixpoint list<T> msetToList<T>(mset<T> m) {
    switch (m) {
        case msetList(l): return l;
    }
}

lemma_auto void mset_toFromList<T>(mset<T> m);
    requires true;
    ensures msetList(msetToList(m)) == m;
lemma_auto void mset_fromToList<T>(list<T> l);
    requires true;
    ensures msetToList(msetList(l)) == l;   


fixpoint mset<T> msetAdd<T>(T t, mset<T> m) {
    return msetList( cons(t, msetToList(m)) );
}

fixpoint mset<T> msetRemove<T>(T t, mset<T> m) {
    return msetList( remove(t, msetToList(m)) );
}


fixpoint int count<T>(T t, list<T> l) {
    switch (l) {
        case nil: return 0;
        case cons(x, xs): return t == x ? 1 + count(t, xs) : count(t, xs);
    
    }
}
fixpoint int msetMultiplicity<T>(T t, mset<T> m) {
    switch (m) {
        case msetList(l): return count(t, l);
    }
}
lemma_auto void msetMultiplicity_nonnegative<T>(T t, mset<T> m);
    requires true;
    ensures msetMultiplicity(t, m) >= 0;
    
    

fixpoint boolean msetIn<T>(T t, mset<T> m) {
    return mem(t, msetToList(m));
}

fixpoint mset<T> msetUnion<T>(mset<T> a, mset<T> b) {
    return msetList(append(msetToList(a), msetToList(b)));
}

fixpoint list<T> nub<T>(list<T> l) {
    switch (l) {
        case nil: return nil;
        case cons(x, xs): return cons(x, remove_every(x, nub(xs)));
    }
}
lemma_auto void nub_distinct<T>(list<T> l);
    requires true;
    ensures distinct(nub(l)) == true;

fixpoint mset<T> msetToSet<T>(mset<T> m) {
    return msetList(nub(msetToList(m)));
}

// a - b or a \ b in set notation (remove_all(x, y) does y - x) 
fixpoint mset<T> msetMinus<T>(mset<T> a, mset<T> b) {
    return msetList(remove_all(msetToList(b), msetToList(a)));
}
lemma void msetPlusMinus<T>(mset<T> a, mset<T> b);
    requires true;
    ensures msetMinus(msetUnion(a, b), b) == a;

// a subset of b
fixpoint boolean msetIncl<T>(mset<T> a, mset<T> b) {
    return msetMinus(a, b) == msetList(nil);
}

// keeps elements where f(elem) == true
fixpoint list<T> filter<T>(list<T> l, fixpoint(T, boolean) f) {
    switch (l) {
        case nil: return nil;
        case cons(x, xs): return f(x) ? cons(x, filter(xs, f)) : filter(xs, f);
    }

}

|]



{-
-- multiset as function (T -> int)
hardcodedMSetDef :: Document d => d
hardcodedMSetDef =
    text "// empty multiset" $$ 
    fixpoint "int" "empty_mset<T>" ["T x"] (text "return 0;") $$
    text "// update multiset" $$
    fixpointNoBody "fixpoint(t1, t2)" "fupdate<t1, t2>" ["fixpoint(t1, t2) f, t1 i, t2 v"] $$
    autoLemmaNoBody "void" "apply_fupdate<t1, t2>" ["fixpoint(t1, t2) f, t1 i, t1 j, t2 v"]
        "true" "(i == j ? v : f(j)) == (fupdate(f, i, v))(j)" $$
--  fixpoint "fixpoint(T, int)" "msetUpdate<T>" ["fixpoint(T, int) f, T i, int v"] (text "v >= 0 ? fupdate(f, i, v) : f") -- either f or fupdate(f, i, 0)
    text "// apply f" $$
    fixpoint "int" "apply<T>" ["fixpoint(T, int) f, T arg"] (text "return f(arg);") $$
    text "// mset operations" $$
    fixpoint "boolean" "msetIn<T>" ["fixpoint(T, int) f", "T arg"] (text "return apply(f, arg) > 0;") $$
    fixpoint "fixpoint(T, int)" "msetInc<T>" ["fixpoint(T, int) f", "T i"] (text "return fupdate(f, i, apply(f, i) + 1);") $$
    fixpoint "fixpoint(T, int)" "msetDec<T>" ["fixpoint(T, int) f", "T i"] (text "return (msetIn(f, i) ? fupdate(f, i, apply(f, i) - 1) : f);")
-}