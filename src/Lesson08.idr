module Lesson08
import Decidable.Equality -- decEq
import Data.Nat -- LTE/GTE
import Data.List -- NonEmpty
import Data.List.Elem -- Elem
%default total

namespace OnMax

    -- Only a helper for the following functions.
    -- The closest thing in Stdlib is Connex (for LTE) or StrongConnex (for LT).
    public export
    decCmp : (a : Nat) -> (b : Nat) -> Either (LTE a b) (LTE b a)
    decCmp 0 0 = Left LTEZero
    decCmp 0 (S k) = Left LTEZero
    decCmp (S k) 0 = Right LTEZero
    decCmp (S k) (S j) =
        case decCmp k j of
            (Left x) => Left (LTESucc x)
            (Right x) => Right (LTESucc x)

    -- The same, just reusing the connect and decEq from stdlib.
    decCmp' : (a : Nat) -> (b : Nat) -> Either (LTE a b) (LTE b a)
    decCmp' a b =
        case decEq a b of
            (Yes Refl) => Left reflexive
            (No contra) => connex contra

    data Max : (a : Nat) -> (b : Nat) -> (m : Nat) -> Type where
        MaxA : LTE b a -> Max a b a
        MaxB : LTE a b -> Max a b b

    {-  And that's how we can use it.

            ∀ a, b ∈ Nat :
                ∃ m ∈ Nat :
                    m = max a b
    -}
    maxOfNats : (a : Nat) -> (b : Nat) -> (m : Nat ** Max a b m)
    maxOfNats a b =
        case decCmp a b of
            (Left prf) => (b ** MaxB prf)
            (Right prf) => (a ** MaxA prf)

    {-  And to prove additional properties of it.

            ∀ a, b, m ∈ Nat :
                (m = max a b) ⇒
                    a ≤ m ∧ b ≤ m ∧ (a = m ∨ b = m)
    -}
    maxOfNatsProps : {a : Nat} -> {b : Nat} -> Max a b m -> (LTE a m, LTE b m, Either (a = m) (b = m))
    maxOfNatsProps (MaxA x) = (reflexive, x, Left Refl)
    maxOfNatsProps (MaxB x) = (x, reflexive, Right Refl)

    maxOfNats_test : Max 1 2 2
    maxOfNats_test = MaxB (LTESucc LTEZero)


    data MaxOfList : (m : Nat) -> List Nat -> Type where
        MaxSingle : (m : Nat) -> MaxOfList m [m]
        MaxAddGT : (e : Nat) -> MaxOfList m l -> LTE m e -> MaxOfList e (e :: l)
        MaxAddLT : (e : Nat) -> MaxOfList m l -> LTE e m -> MaxOfList m (e :: l)

    {-  Here we calculate the maximum of a list.
        Note that we use another predicate `NonEmpty l` to express non-emptiness of a list.

            ∀ l ∈ [Nat] :
                l ≠ [] ⇒
                    ∃ m ∈ Nat :
                        m = maxOfList l
    -}
    maxOfList : (l : List Nat) -> {prf : NonEmpty l} -> ( m : Nat ** MaxOfList m l )
    maxOfList [] impossible
    maxOfList (e :: []) = (e ** MaxSingle e)
    maxOfList (e :: (x :: xs)) =
        case maxOfList (x :: xs) {prf = IsNonEmpty} of
            (xsMax ** xsPrf) =>
                case decCmp e xsMax of
                    (Left y) => (xsMax ** MaxAddLT e xsPrf y)
                    (Right y) => (e ** MaxAddGT e xsPrf y)

    -- maxOfList_test : MaxOfList 3 [1, 2, 3]
    -- maxOfList_test = ?maxOfList_test_rhs


    {-  And derive the properties we need.
        A simple case is on the head element.

            ∀ m ∈ Nat, l ∈ [Nat] :
                m = maxOfList l ⇒
                    m ≥ l[0]
    -}
    maxOfListPropsHd : MaxOfList m (x :: xs) -> LTE x m
    maxOfListPropsHd (MaxSingle x) = reflexive
    maxOfListPropsHd (MaxAddGT x xs prf) = reflexive
    maxOfListPropsHd (MaxAddLT x xs prf) = prf


    {-  More complicated can be to prove that max element is in the list.
        Also we show how to use the `Elem` predicate from `Data.List.Elem`.

            ∀ m ∈ Nat, l ∈ [Nat] :
                m = maxOfList l ⇒
                    m ∈ l
    -}
    maxOfListInList : MaxOfList m l -> Elem m l
    maxOfListInList (MaxSingle e) = Here
    maxOfListInList (MaxAddGT e max lte) = Here
    maxOfListInList (MaxAddLT e max lte) =
        case maxOfListInList max of
            Here => There Here
            (There x) => There (There x)

namespace OnSum

    data ListWithSum : (s : Nat) -> (l : List Nat) -> Type where
        ListWith0 : ListWithSum 0 []
        ListWithS : ListWithSum s l -> (e : Nat) -> ListWithSum (s + e) (e :: l)

    listWithSum : (l : List Nat) -> (s : Nat ** ListWithSum s l)
    listWithSum [] = (0 ** ListWith0)
    listWithSum (x :: xs) =
        case listWithSum xs of
           ((xsSum ** xsPrf)) => (xsSum + x ** ListWithS xsPrf x)

    listWithSum_test0 : ListWithSum 0 []
    listWithSum_test0 = ListWith0

    listWithSum_test1 : ListWithSum 7 [7]
    listWithSum_test1 = ListWithS ListWith0 7

    listWithSum_test2 : ListWithSum 12 [7, 5]
    listWithSum_test2 = ListWithS (ListWithS ListWith0 5) 7

    namespace UselessUtxo

        {-  Example use of ListWithSum -- a TX, where inputs and outputs must match.
            For now, the type itself has no properties on it.
        -}
        data UtxoTX : Type where
            MkUtxoTX :
                (inputs : List Nat) ->
                (outputs : List Nat) ->
                {s : Nat} ->
                {prfI : ListWithSum s inputs} ->
                {prfO : ListWithSum s outputs} ->
                UtxoTX


        {-  Let's build a trivial TX.
        -}
        utxoTxEmpty : UtxoTX
        utxoTxEmpty = MkUtxoTX [] [] {s=0} {prfI = ListWith0} {prfO = ListWith0}


        {-  And here is a way to build a tx of provided inputs/outputs.
            This function is not decidable for now (cannot return Dec Utxo),
            because the type is not precise enough yet (type has no params).
        -}
        -- TODO: Decidable in labs?
        utxoTx : (inp : List Nat) -> (out : List Nat) -> Maybe UtxoTX
        utxoTx inp out =
            let (inpS ** inpPrf) = listWithSum inp in
            let (outS ** outPrf) = listWithSum out in
            case decEq inpS outS of
                (Yes Refl) => Just (MkUtxoTX inp out {prfI = inpPrf} {prfO = outPrf})
                (No contra) => Nothing


    namespace OnListWithOpSum

        {-  Try to make the Sum over a list more useful.
        -}
        public export
        data ListWithOpSum : {a : Type} -> (s : Nat) -> (a -> Nat) -> List a -> Type where
            ListWithOp0 : ListWithOpSum 0 _ []
            ListWithOpS :
                {s : Nat} ->
                {op : a -> Nat} ->
                (e : a) ->
                ListWithOpSum s op l ->
                ListWithOpSum (s + (op e)) op (e :: l)

        public export
        listWithOpSum : {op : a -> Nat} -> (l : List a) -> (s : Nat ** ListWithOpSum s op l)
        listWithOpSum {op} [] = (0 ** ListWithOp0)
        listWithOpSum {op} (x :: xs) =
            case listWithOpSum xs of
            ((xsSum ** xsPrf)) => (xsSum + op(x) ** ListWithOpS x xsPrf)


    namespace BetterUtxo
        {- Example use of ListWithSum -- a TX, where inputs and outputs must match.
        -}
        record Address where
            constructor MkAddress
            hex : String

        record Input where
            constructor MkInput
            amt : Nat
            sender : Address

        record Output where
            constructor MkOutput
            amt : Nat
            receiver : Address

        data UtxoTX : Type where
            MkUtxoTX :
                (inputs : List Input) ->
                (outputs : List Output) ->
                {s : Nat} ->
                {prfI : ListWithOpSum s Input.amt inputs} ->
                {prfO : ListWithOpSum s Output.amt outputs} ->
                UtxoTX

        utxoTx : (inp : List Input) -> (out : List Output) -> Maybe UtxoTX
        utxoTx inp out =
            let (inpS ** inpPrf) = listWithOpSum {op = Input.amt} inp in
            let (outS ** outPrf) = listWithOpSum {op = Output.amt} out in
            case decEq inpS outS of
                (Yes Refl) => Just (MkUtxoTX inp out {prfI = inpPrf} {prfO = outPrf})
                (No contra) => Nothing

    namespace AccountBasedLedger

        namespace NatSub
            {-  Safe subtraction for Nats.
                Might be useful.
            -}
            public export
            sub : (a : Nat) -> (b : Nat) -> {prf : GTE a b} -> (d : Nat ** a = b + d)
            sub 0 0 = (0 ** Refl)
            sub 0 (S k) impossible
            sub (S k) 0 = (S k ** Refl)
            sub (S k) (S j) {prf} =
                case sub k j {prf=(fromLteSucc prf)} of
                    ((d ** dPrf)) => (d ** cong S dPrf)


        data IBAN = MkIban String

        DecEq(IBAN) where
            decEq (MkIban str1) (MkIban str2) =
                case decEq str1 str2 of
                    (Yes Refl) => Yes Refl
                    (No contra) => No (\Refl => contra Refl)


        record Account where
            constructor MkAccount
            iban : IBAN
            amount : Nat

        account_add : (a : Account) -> (amt : Nat) -> (a' : Account ** a'.amount = a.amount + amt)
        account_add a amt = (MkAccount a.iban (a.amount + amt) ** Refl)

        account_sub : (a : Account) -> (amt : Nat) -> (prf : GTE a.amount amt) -> (a' : Account ** a.amount = (amt + a'.amount))
        account_sub a amt prf =
            case sub (a.amount) amt {prf=prf} of
                ((amt' ** amt'prf)) => (MkAccount a.iban (amt') ** amt'prf)


        namespace ElemPred
            {-  Given a list and a predicate, return an element satisfying
                the predicate and the proof it satisfies it.
            -}

            {-  A helper for elemPred.

                ∄ x ∈ [].
            -}
            elemPredContra1 :
                (p : (a -> Type)) ->
                (t : (x : a) -> Dec (p x)) ->
                (e : a ** (Elem e [], p e)) ->
                Void
            elemPredContra1 p t ((e ** (eElem, ePe))) = absurd eElem


            {-  A helper for elemPred.

                p(e) ∉ xs ∧ ¬p(x) ⇒ p(e) ∉ x::xs
            -}
            elemPredContra2 :
                {a : Type} ->
                {xs : List a} ->
                (p : (a -> Type)) ->
                (x : a) ->
                (notPx : Not (p x)) ->
                (notExs : Not (e : a ** (Elem e xs, p e))) ->
                (ePxXs : (e : a ** (Elem e (x :: xs), p e))) ->
                Void
                {- Proof sketch:
                    Elem e (x :: xs)            \ ==> Elem e xs
                    p e           \ ==> e != x  /
                    p x -> Void   /
                    ------------------------------
                    goal : Elem fst xs
                -}
            elemPredContra2 p x notPx notExs (e ** (eElem, ePx)) =
                let e_neq_x = lemma1 p e x ePx notPx in
                let e_in_xs = lemma2 eElem e_neq_x in
                notExs (e ** (e_in_xs, ePx))
            where
                -- (p x) ∧ ¬(p y) ⇒ x ≠ y
                lemma1 : {a : Type} -> (p : (a -> Type)) -> (x : a) -> (y : a) -> p x -> Not (p y) -> Not (x = y)
                lemma1 p x y z f prf = f (rewrite sym prf in z)

                -- e ∈ x::xs ∧ e ≠ x ⇒ e e ∈ xs
                lemma2 : {a : Type} -> {e, x : a} -> {xs : List a} -> (el : Elem e (x :: xs)) -> Not (e = x) -> Elem e xs
                lemma2 Here f = void (f Refl)
                lemma2 (There y) f = y


            {- That's the main function we have defined in this section.

                ∀ la ∈ [a], t:(∀x. p(x) ∨ ¬p(x)) ⇒
                    ∨ ∃e∈la. p(e)
                    ∨ ∀e∈la. ¬p(a)
            -}
            public export
            elemPred :
                {a : Type} ->
                {p : (a -> Type)} ->            -- the property to check.
                (la : List a) ->                -- Where to look.
                (t : (x : a) -> Dec (p x)) ->   -- the way (test) to decide on the property.
                Dec (e : a ** (Elem e la, (p e)))
            elemPred [] t = No (elemPredContra1 p t)
            elemPred (x :: xs) t =
                case t x of
                    (Yes prf) => Yes (x ** (Here, prf))
                    (No tContra) =>
                        case elemPred xs t of
                            (Yes ((found ** (elem, pPrf)))) => Yes (found ** (There elem, pPrf))
                            (No nextContra) => No (elemPredContra2 p x tContra nextContra)

            {-  Just an example on how to use the `elemPred` function.
                Given a list, a projection and `x`, find an element whose projection equals to `x`.
            -}
            exampleQueryByField : DecEq b =>
                {a : Type} ->
                (la : List a) ->
                (op : (a -> b)) ->
                (x : b) ->
                Dec (e : a ** (Elem e la, op e = x))
            exampleQueryByField la op x = (elemPred la (\e : a => decEq (op e) x))

        namespace LedgerV2

            Ledger : (s : Nat) -> (as : List Account) -> Type
            Ledger s as = ListWithOpSum s Account.amount as

            ledger : (as : List Account) -> (s : Nat ** Ledger s as)
            ledger as = listWithOpSum as

            statement :
                {as : List Account} ->
                (ib : IBAN) ->
                (l : Ledger s as) ->
                Dec (a : Account ** (Elem a as, Account.iban a = ib))
            statement {as} ib l = elemPred as (\x => decEq (Account.iban x) ib)


            namespace LedgerInc
                -- A helper for ledger_inc
                ledger_inc' :
                    {as : List Account} ->
                    {s : Nat} ->
                    {a : Account} ->
                    (a_in_as : Elem a as) ->
                    (amt : Nat) ->
                    (l : ListWithOpSum s Account.amount as) ->
                    (as' : List Account ** ListWithOpSum (amt+s) Account.amount as')
                ledger_inc' {as = []} {s = s} {a = a} a_in_as amt l = absurd a_in_as
                ledger_inc' {as = (x :: xs)} {s = (s' + x.amount)} {a = x} Here amt (ListWithOpS x l') =
                    case account_add x amt of
                        ((x''@(MkAccount iban (plus (x .amount) amt)) ** Refl)) =>
                            (x'' :: xs ** rewrite sym (lemma14 {amt=amt} {iban=iban} s' x) in (ListWithOpS x'' l'))
                    where
                        lemma12 : {a : Nat} -> {b : Nat} -> {c : Nat} -> plus a (plus b c) = plus b (plus c a)
                        lemma12 {a} {b} {c} =
                            rewrite plusCommutative b (plus c a) in     -- ==> plus a (plus b c) = plus (plus c a) b
                            rewrite plusCommutative c a in              -- ==> plus a (plus b c) = plus (plus a c) b
                            rewrite sym (plusAssociative a c b) in      -- ==> plus a (plus b c) = plus a (plus c b)
                            rewrite sym (plusCommutative c b) in
                            Refl

                        -- Cancel out a pair of `Account.amount (MkAccount _ amt) = amt`
                        lemma13 : {iban : IBAN} -> {amt : Nat} -> (x : Account) -> Account.amount (MkAccount iban (plus (x.amount) amt)) = (plus (x.amount) amt)
                        lemma13 x = Refl

                        lemma14 : {amt : Nat} -> {iban : IBAN} -> (x1 : Nat) -> (x2 : Account) -> plus x1 ((MkAccount iban (plus (x2.amount) amt)).amount) = plus amt (plus x1 (x2.amount))
                        lemma14 {amt} {iban} x1 x2 =
                            rewrite (lemma13 {iban=iban} {amt=amt} x2) in
                            rewrite lemma12 {a=amt} {b=x1} {c=x2.amount} in
                            Refl

                ledger_inc' {as = (x :: xs)} {s = (s' + x.amount)} {a = a} (There a_in_as') amt (ListWithOpS x l') =
                    case ledger_inc' {as=xs} {s=s'} {a=a} a_in_as' amt l' of
                        ((as'' ** l'')) =>
                            let pp = ((plus (plus amt s') (x .amount)) = (plus amt (plus s' (x .amount)))) in
                            let zz = ListWithOpS x l'' in  (x :: as'' ** rewrite (plusAssociative amt s' x.amount) in zz)

                public export
                ledger_inc :
                    {s : Nat} ->
                    {as : List Account} ->
                    (a : Account) ->
                    (a_in_as : Elem a as) ->
                    (amt : Nat) ->
                    (l : Ledger s as) ->
                    (as' : List Account ** Ledger (amt+s) as')
                ledger_inc a a_in_as amt l = ledger_inc' a_in_as amt l -- Transform Ledger to ListWithOpSum.


            namespace LedgerDec
                -- A helper for ledger_inc
                ledger_dec' :
                    {as : List Account} ->
                    {s : Nat} ->
                    {a : Account} ->
                    (a_in_as : Elem a as) ->
                    (amt : Nat) ->
                    (a_gte_amt : GTE (a.amount) amt) ->
                    (l : ListWithOpSum (amt+s) Account.amount as) ->
                    (as' : List Account ** ListWithOpSum s Account.amount as')
                -- TODO: Port the implementation from ledger_inc'

                public export
                ledger_dec :
                    {s : Nat} ->
                    {as : List Account} ->
                    (a : Account) ->
                    (a_in_as : Elem a as) ->
                    (amt : Nat) ->
                    (a_gte_amt : GTE (a.amount) amt) ->
                    (l : Ledger (amt+s) as) ->
                    (as' : List Account ** Ledger s as')
                ledger_dec a a_in_as amt l = ledger_dec' a_in_as amt l -- Transform Ledger to ListWithOpSum.

            transferOptimistic :
                {s : Nat} ->
                {as : List Account} ->
                (src : IBAN) ->
                (dst : IBAN) ->
                (amt : Nat) ->
                (l : Ledger s as) ->
                (as' : List Account ** (Ledger s as'))
            transferOptimistic src dst amt l = (as ** l)


            transfer :
                {s : Nat} ->
                {as : List Account} ->
                (src : IBAN) ->
                (dst : IBAN) ->
                (amt : Nat) ->
                (l : Ledger s as) ->
                Maybe
                    (src_a : Account **
                        (dst_a : Account **
                            (src_a' : Account **
                                (dst_a' : Account **
                                    (as' : List Account ** (
                                        Elem src_a as,
                                        Elem dst_a as,
                                        Ledger s as',
                                        Elem src_a' as',
                                        Elem dst_a' as',
                                        Account.amount src_a' + amt = Account.amount src_a,
                                        Account.amount dst_a' = Account.amount dst_a + amt
                                    ))
                                )
                            )
                        )
                    )
            transfer {as} src dst amt l =
                case elemPred as (\a => decEq (a.iban) dst) of
                    (Yes ((dst_a ** (dst_a_elem, dst_a_iban)))) =>
                        let (as' ** l') = ledger_inc dst_a dst_a_elem amt l in -- l' : (as' : List Account ** ListWithOpSum (plus amt s) .amount as')
                        case elemPred as' (\a => decEq a.iban src) of
                            (Yes ((src_a ** (src_a_elem, src_a_iban)))) =>
                                case isGTE (src_a.amount) amt of
                                    (Yes src_gte_amt) =>
                                        let (as'' ** l'') = ledger_dec {as=as'} src_a src_a_elem amt src_gte_amt l' in
                                        Just (src_a ** (dst_a ** ?todo_query_updated)) -- TODO: Continue here.
                                        -- Also, return proofs on src_a' and dst_a' from the ledger_inc/ledger_dec functions.
                                    (No amtGtSrc) => Nothing
                            (No noSrc) => Nothing
                    (No noDst) => Nothing

