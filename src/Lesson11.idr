module Lesson11
import Data.Vect
%default total

namespace FirstAttempt

    data CartCmd : Type where
        AddItem : CartCmd
        DelItem : CartCmd
        Checkout : CartCmd
        Pay : CartCmd
        Deliver : CartCmd

    program : List CartCmd
    program = [AddItem, AddItem, DelItem, Checkout, Pay, Deliver]

    program' : List CartCmd -- nelogiška
    program' = [Deliver, Pay, AddItem, AddItem, DelItem, Checkout, Pay]

namespace MakeItMonadic

    data CartCmd : Type -> Type where
        AddItem : i -> CartCmd ()
        DelItem : i -> CartCmd ()
        Checkout : CartCmd ()
        Pay : CartCmd ()
        Deliver : CartCmd ()
        Pure : a -> CartCmd a
        (>>=) : CartCmd a -> (a -> CartCmd b) -> CartCmd b
        (>>) : CartCmd a -> (CartCmd b) -> CartCmd b

    program : CartCmd ()
    program =
        do  AddItem "butter"
            AddItem "bread"
            Checkout
            Pay
            Deliver

    program' : CartCmd () -- illogic
    program' =
        do  Checkout
            Deliver
            AddItem "butter"
            AddItem "bread"

namespace WithStates

    data CartState = CartPending | CartPreview | CartDelivering | CartDone

    data CartCmd :
        (return : Type) ->
        (preCondition : CartState) ->
        (postCondition : CartState) ->
        Type where
        AddItem : i -> CartCmd () CartPending CartPending
        DelItem : i -> CartCmd () CartPending CartPending
        Checkout : CartCmd () CartPending CartPreview
        Pay : CartCmd () CartPreview CartDelivering
        Deliver : CartCmd () CartDelivering CartDone
        Pure : a -> CartCmd a CartPending CartPending
        (>>=) :
            CartCmd a s1 s2 ->
            (a -> CartCmd b s2 s3) ->
            CartCmd b s1 s3
        (>>) :
            CartCmd a s1 s2 ->
            (CartCmd b s2 s3) ->
            CartCmd b s1 s3

    program : CartCmd () CartPending CartDone
    program =
        do  Pure ()
            AddItem "butter" -- We still able to keep it empty.
            AddItem "bread"
            Checkout
            Pay
            Deliver

namespace InfiniteStateSpace

    data CartState : Type where
        CartPending    : Nat -> CartState
        CartPreview    : Nat -> CartState
        CartDelivering : Nat -> CartState
        CartDone       : CartState

    data CartCmd :
        (return : Type) ->
        (preCondition : CartState) ->
        (postCondition : CartState) ->
        Type where
        AddItem : i -> CartCmd () (CartPending n) (CartPending (S n))
        DelItem : Fin (S n) -> CartCmd () (CartPending (S n)) (CartPending n)
        Checkout : CartCmd () (CartPending (S n)) (CartPreview (S n))
        Pay : CartCmd () (CartPreview (S n)) (CartDelivering (S n))
        Deliver : CartCmd () (CartDelivering (S n)) CartDone
        Pure : a -> CartCmd a (CartPending 0) (CartPending 0)
        (>>=) :
            CartCmd a s1 s2 ->
            (a -> CartCmd b s2 s3) ->
            CartCmd b s1 s3
        (>>) :
            CartCmd a s1 s2 ->
            (CartCmd b s2 s3) ->
            CartCmd b s1 s3

    program : CartCmd () (CartPending 0) CartDone
    program =
        do  Pure ()
            AddItem "butter"
            AddItem "bread"
            DelItem 1
            Checkout
            Pay
            Deliver

namespace DependOnResults

    data CartState : Type where
        CartPending    : Nat -> CartState
        CartPreview    : Nat -> CartState
        CartDelivering : Nat -> CartState
        CartDone       : CartState

    data AddItemRes = OK | OutOfStock
    data PayRes = Success | Rejected

    data CartCmd :
        (res : Type) ->
        CartState -> -- precondition
        (res -> CartState) -> -- post-condition
        Type where
        AddItem : {n : Nat} -> i -> CartCmd AddItemRes (CartPending n)
            (\res =>
                case res of
                    OK => CartPending (S n)
                    OutOfStock => CartPending n
            )
        DelItem : Fin (S n) -> CartCmd () (CartPending (S n)) (const (CartPending n))
        Checkout : CartCmd () (CartPending (S n)) (const (CartPreview (S n)))
        Pay : {n : Nat} -> CartCmd PayRes (CartPreview (S n))
            (\res =>
                case res of
                    Success => CartDelivering (S n)
                    Rejected => CartPreview (S n))
        Deliver : CartCmd () (CartDelivering (S n)) (const CartDone)
        Pure : a -> CartCmd a (CartPending 0) (const (CartPending 0))
        (>>=) :
            CartCmd a s1 sf2 ->
            ((res : a) -> CartCmd b (sf2 res) s3) ->
            CartCmd b s1 s3
        (>>) :
            CartCmd a s1 (\_ => s2) ->
            (CartCmd b s2 s3) ->
            CartCmd b s1 s3

    program : CartCmd () (CartPending 0) (const CartDone)
    program =
        do  Pure ()
            add1 <- AddItem "butter"
            case add1 of
                OK =>
                    do  OK <- AddItem "bread" | OutOfStock => ?program_add2_failed
                        DelItem 1
                        Checkout
                        Success <- Pay | Rejected => ?program_pay_failed
                        Deliver
                OutOfStock =>
                    ?program_add1_failed

namespace WithPredicate

    data CartState : Type where
        CartPending    : Nat -> CartState
        CartPreview    : Nat -> CartState
        CartDelivering : Nat -> CartState
        CartDone       : CartState
        CartEnd        : CartState

    data AddItemRes = OK | OutOfStock
    data PayRes = Success | Rejected

    data CartFinal : CartState -> Type where
        FinalPending : CartFinal (CartPending n)
        FinalPreview : CartFinal (CartPreview n)
        FinalDone    : CartFinal (CartDone)

    data CartCmd :
        (res : Type) ->
        CartState -> -- precondition
        (res -> CartState) -> -- post-condition
        Type where
        AddItem : {n : Nat} -> i -> CartCmd AddItemRes (CartPending n)
            (\res =>
                case res of
                    OK => CartPending (S n)
                    OutOfStock => CartPending n
            )
        DelItem : Fin (S n) -> CartCmd () (CartPending (S n)) (const (CartPending n))
        Checkout : CartCmd () (CartPending (S n)) (const (CartPreview (S n)))
        Pay : {n : Nat} -> CartCmd PayRes (CartPreview (S n))
            (\res =>
                case res of
                    Success => CartDelivering (S n)
                    Rejected => CartPreview (S n))
        Deliver : CartCmd () (CartDelivering (S n)) (const CartDone)
        Final : CartFinal fin -> CartCmd () fin (const CartEnd)
        Pure : a -> CartCmd a (CartPending 0) (const (CartPending 0))
        (>>=) :
            CartCmd a s1 sf2 ->
            ((res : a) -> CartCmd b (sf2 res) s3) ->
            CartCmd b s1 s3
        (>>) :
            CartCmd a s1 (\_ => s2) ->
            (CartCmd b s2 s3) ->
            CartCmd b s1 s3

    program : CartCmd () (CartPending 0) (const CartEnd)
    program =
        do  Pure ()
            OK <- AddItem "butter" | OutOfStock => (Final FinalPending)
            OK <- AddItem "bread" | OutOfStock => (Final FinalPending)
            DelItem 1
            Checkout
            Success <- Pay | Rejected => (Final FinalPreview)
            Deliver
            (Final FinalDone)
