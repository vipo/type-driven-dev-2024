-- cspell:words snoc
module Lesson09
import Data.List
import Data.Vect
%default total

namespace NonTotal
    describeList : List Int -> String
    describeList [] = "Empty"
    describeList (x :: xs) = "Non-Empty, tail=" ++ (show xs)

    failing
        describeListEnd : List Int -> String
        describeListEnd [] = "Empty"
        describeListEnd (xs ++ [x]) = "Non-Empty, prefix=" ++ (show xs)


    data ListLast : List a -> Type where
        Empty : ListLast []
        NonEm : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

    listLast : (xs : List a) -> ListLast xs
    listLast [] = Empty
    listLast (x :: xs) =
        case listLast xs of
            Empty => NonEm [] x
            (NonEm ys y) => NonEm (x :: ys) y


    describeListEnd : List Int -> String
    describeListEnd xs = describeListEndHelp xs (listLast xs)
    -- describeListEnd xs = case listLast xs of
    --                           Empty => ?asd_0
    --                           (NonEm ys x) => ?asd_1
        where
            describeListEndHelp : (xs : List Int) -> (ListLast xs) -> String
            describeListEndHelp [] Empty = "Empty"
            describeListEndHelp (xs ++ [x]) (NonEm xs x) = "Non-Empty, prefix=" ++ (show xs)

    describeListEnd' : List Int -> String
    describeListEnd' xs with (listLast xs)
        describeListEnd' [] | Empty = "Empty"
        describeListEnd' (xs ++ [x]) | (NonEm xs x) = "Non-Empty, prefix=" ++ (show xs)

    covering
    myReverse : List a -> List a
    myReverse xs with (listLast xs)
        myReverse [] | Empty = []
        myReverse (xs ++ [x]) | (NonEm xs x) = x :: (myReverse xs)

    failing
        mergeSort : Ord a => List a -> List a
        mergeSort [] = []
        mergeSort [x] = [x]
        mergeSort (ls ++ rs) = merge (mergeSort ls) (mergeSort rs)

    data SplitList : List a -> Type where
        SLNil : SplitList []
        SLOne : (x : a) -> SplitList [x]
        SLPair : (ls : List a) -> (rs : List a) -> SplitList (ls ++ rs)

    splitList : (xs : List a) -> (SplitList xs)
    splitList xs = splitListHelp xs xs
        where
            splitListHelp : List a -> (xs : List a) -> SplitList xs
            splitListHelp _ [] = SLNil
            splitListHelp _ [x] = SLOne x
            splitListHelp (_ :: _ :: counter) (x :: xs) =
                case splitListHelp counter xs of
                    SLNil => SLOne x
                    (SLOne y) => SLPair [x] [y]
                    (SLPair ls rs) => SLPair (x :: ls) rs
            splitListHelp _ xs = SLPair [] xs

    export
    covering
    mergeSort : Ord a => List a -> List a
    mergeSort xs with (splitList xs)
      mergeSort [] | SLNil = []
      mergeSort [x] | (SLOne x) = [x]
      mergeSort (ls ++ rs) | (SLPair ls rs) = merge (mergeSort ls) (mergeSort rs)


namespace MoreTotal

    data SnocList' : List a -> Type where
        Empty : SnocList' []
        Snoc : (xs : List a) -> (x : a) -> (rec : SnocList' xs) -> SnocList' (xs ++ [x])

    snocList'Help :
        {xs : List a} -> (snoc : SnocList' xs) ->
        (rest : List a) -> SnocList' (xs ++ rest)
    snocList'Help snoc [] =
        rewrite appendNilRightNeutral xs in snoc
    snocList'Help {xs} snoc (x :: ys) =
        rewrite appendAssociative xs [x] ys in
        snocList'Help (Snoc xs x snoc) ys

    snocList' : (xs : List a) -> (SnocList' xs)
    snocList' xs = snocList'Help Empty xs


    myReverseHelp : {a : Type} -> (input : List a) -> (snoc : SnocList' input) -> List a
    myReverseHelp [] Empty = []
    myReverseHelp (xs ++ [x]) (Snoc xs x rec) = x :: myReverseHelp xs rec

    myReverse : {a : Type} -> (List a) -> (List a)
    myReverse xs = myReverseHelp xs (snocList' xs)

    -- Merge sort for labs.

namespace Hiding

    namespace DataStore

        {-  We have seen this impl before.
            Just repeating it here to have it.
        -}

        infixr 5 .+.

        public export
        data Schema = SStr | SInt | (.+.) Schema Schema

        public export
        SchemaType : Schema -> Type
        SchemaType SStr = String
        SchemaType SInt = Int
        SchemaType (x .+. y) = (SchemaType x, SchemaType y)

        export
        record DataStore (schema : Schema) where
            constructor MkData
            size : Nat
            items : Vect size (SchemaType schema)

        export
        empty : {schema : Schema} -> DataStore schema
        empty = MkData 0 []

        export
        addToStore :
            (val : SchemaType schema) ->
            (store : DataStore schema) ->
            DataStore schema
        addToStore val (MkData _ items) = MkData _ (val :: items)

        {- Only for experiments. -}
        testStore : DataStore (SStr .+. SStr .+. SInt)
        testStore =
            addToStore ("a", "x", 10) $
            addToStore ("b", "y", 11) $
            addToStore ("c", "z", 12) $
            empty

        public export
        data StoreView : {schema : Schema} -> DataStore schema -> Type where
            SNil : {schema : Schema} -> StoreView (empty {schema=schema})
            SAdd : {schema : Schema} ->
                {ds : DataStore schema} -> {v : SchemaType schema} ->
                (rec : StoreView ds) -> StoreView (addToStore v ds)


        public export
        storeView : {schema : Schema} -> (ds : DataStore schema) -> StoreView ds
        storeView (MkData size items) = storeView' items
            where
                storeView' :
                    {size : Nat} -> {schema : Schema} ->
                    (items : Vect size (SchemaType schema)) ->
                    StoreView {schema=schema} (MkData size items)
                storeView' [] = SNil
                storeView' (x :: xs) = SAdd (storeView' xs)


    listItems : {schema : Schema} -> DataStore schema -> List (SchemaType schema)
    listItems {schema} ds with (storeView ds)
        listItems {schema = schema} (empty {schema=schema}) | SNil = []
        listItems {schema = schema} (addToStore v ds) | (SAdd rec) =
            v :: (listItems ds | rec)
