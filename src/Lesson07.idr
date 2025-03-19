||| Predicate logic and inductive predicates.
module Lesson07
import Data.Nat
import Data.Vect


namespace RecapOnCH

    {-
        a => b => c   <=>    a /\ b => c
    -}

    impImpAnd : (a -> b -> c) -> ((a, b) -> c)
    -- impImpAnd f (x, y) = f x y
    impImpAnd = uncurry

    andImpImp : ((a, b) -> c) -> (a -> b -> c)
    -- andImpImp f x y = f (x, y)
    andImpImp = curry

    -- TODO: Equiv.
    andImpEquiv : ((a, b) -> c) <=> (a -> b -> c)
    andImpEquiv = MkEquivalence andImpImp impImpAnd

    natBoolEquiv : Nat <=> Bool
    natBoolEquiv = MkEquivalence (\k => False) (\x => 0)

    failing
        natBoolEquivX : Vect Bool Bool

    equivLeftEM' : (a -> b -> c) -> (a -> b -> c)
    equivLeftEM' = andImpImp . impImpAnd

    equivRightEM' : ((a, b) -> c) -> ((a, b) -> c)
    equivRightEM' = impImpAnd . andImpImp ---- Iso, if = id,  f = g^1, f (g x) = x

    EndoMorphism : (a : Type) -> Type
    EndoMorphism a = a -> a

    equivLeftEM : EndoMorphism (a -> b -> c)
    equivLeftEM = andImpImp . impImpAnd

    equivRightEM : EndoMorphism ((a, b) -> c)
    equivRightEM = impImpAnd . andImpImp


||| Predicate logic, ∀, ∃, P(x)
namespace OnForall
    {-
        (a \in Nat) => (a >= 0)  ====>  \A a. a \in Nat => a >= 0
        (\A a \in Nat : a >= 0)  ====>  \A a. a \in Nat => a >= 0

        Introduction rules:

               Γ,x : A ⊢ b(x) : B
            ------------------------ (⇒-Intro, Fun)
             Γ ⊢ (x↦b(x)) : A⇒B

                Γ,x∈A ⊢ b(x) : B(x)
            ---------------------------- (∀-Intro)
              Γ ⊢ λx.b(x) : ∀x∈A.B(x)

        Elimination rules:

              Γ ⊢ f : A⇒B    Γ ⊢ a : A
            ----------------------------- (⇒-Elim, MP)
                     Γ ⊢ f(a) : B

             Γ ⊢ f : ∀x∈A.B(x)    Γ ⊢ a∈A
            ---------------------------------- (∀-Elim)
                   Γ ⊢ f(a) : B[a/x]

    -}

    mp : a -> (a -> b) -> b
    mp x f = f x

    {-

        \A f \in (a -> b), x, y \in a.
            (x = y) => (f x = f y)
    -}
    fa : (f : a -> b) -> (x : a) -> (y : a) -> (x = y) -> (f x = f y)
    fa f x x Refl = Refl

namespace OnExists

    {-
        How to prove \E?
            a) ~\A x. ~P(x)  ==> \E x. P(x) -- classical logic.
            b) find such witness.`a` that P(a) ==> \E x. P(x).

        See (https://ncatlab.org/nlab/show/propositional+logic+as+a+dependent+type+theory).

                Γ ⊢ A type      Γ,x∈A ⊢ B(x) prop
            ----------------------------------------- (∃-Intro)
             Γ, x∈A, y∈B(x) ⊢ in(x,y) : ∃x∈A.B(x)

    -}

    exIntro :
        {a : Type} ->       -- Premise 1
        {b : a -> Type} ->  -- Premise 2
        (x : a) ->          -- Conclusion, x∈A
        (y : b x) ->        -- Conclusion, y∈B(x)
        (x' : a ** b x')    -- Conclusion, consequence ∃x∈A.B(x)
    exIntro x y = (x ** y)

    {-
             Γ                  ⊢ A type      -- Type A exists.
             Γ,            x∈A ⊢ B(x) prop    -- Dependent type B(x) exist.
             Γ,   z:∃x∈A.B(x) ⊢ C(z) prop     -- Dependent type C(z) exist.
             Γ,   x∈A, y∈B(x) ⊢ c:C(in(x,y))
            ----------------------------------------------------- (∃-Elim)
             Γ, z:∃x∈A.B(x) ⊢ ind^C_(∃x∈A.B(x))(c)(z) : C(z)
    -}

    exElim'' :
        {j : Nat} ->
        ({m : Nat} -> (m+m=m*m) -> j=13) -> -- x∈A, y∈B(x) ⊢ c:C(in(x,y))
        (n : Nat ** n+n=n*n) ->             -- z:∃x∈A.B(x)
        (j = 13)                            -- C(z)
    exElim'' f ((fst ** snd)) = f snd

    {-  We can replace concrete types with abstract ones:
        First introduce `a : Type`, `b : a -> Type`.
         - `j=13 : Type` ---> `c : Type`,
         - `n : Nat` ---> `x : a`, and `n+n=n*n` ---> `b x`
         - `m : Nat` ---> `x : a`, and `m+m=m*m` ---> `b x`
    -}
    exElim' :
        {a : Type} ->                   -- A type
        {b : a -> Type} ->              -- B(x) prop
        {c : Type} ->                   -- ~~~ C(z) prop
        ({x' : a} -> (y : b x') -> c) -> -- x'∈A, y∈B(x') ⊢ c:C(in(x',y))
        (x : a ** b x) ->               -- z:∃x∈A.B(x)
        c                               -- C(z)
    exElim' f ((fst ** snd)) = f snd

    {- make c dependent on (x ** y)
    -}

    exElim :
        {a : Type} ->                       -- A type
        {b : a -> Type} ->                  -- B(x) prop
        {c : (x : a ** b x) -> Type} ->     -- ~~~ C(z) prop
        ({x' : a} -> (y : b x') -> c (x' ** y)) -> -- x'∈A, y∈B(x') ⊢ c:C(in(x',y))
        (z : (x : a ** b x)) ->           -- z:∃x∈A.B(x)
        c z                               -- C(z)
    exElim f ((a ** ba)) = f ba

namespace OnEq

    some : (x : a) -> (x = x) -- Type represents a fact / proposition / predicate.
    some x = Refl

    tra : (a = b) -> (b = c) -> (a = c)
    tra Refl Refl = Refl

namespace OnLTE

    {-
        \A a, b \in Nat : (a =< b \/ b =< a)
    -}
    some : (a : Nat) -> (b : Nat) -> Either (LTE a b) (LTE b a)
    some 0 0 = Left LTEZero
    some 0 (S k) = Left LTEZero
    some (S k) 0 = Right LTEZero
    some (S k) (S j) = case some k j of
                        (Left x) => Left (LTESucc x)
                        (Right x) => Right (LTESucc x)

    {-
        \A a, b \in Nat : a >= b /\ a =< b => a = b
    -}
    other : {a : Nat} -> {b : Nat} -> GTE a b -> LTE a b -> Equal a b -- a = b
    other LTEZero LTEZero = Refl
    other (LTESucc x) (LTESucc y) = case other x y of
                                         Refl => Refl

namespace OnEvenOdd

    data Even : Nat -> Type where
        EvenZero : Even 0
        EvenNext : {x : Nat} -> Even x -> Even (S (S x))

    -- Would be better to define as a function.
    data Odd : Nat -> Type where
        OddOne : Odd 1
        OddNext : {x : Nat} -> Odd x -> Odd (S (S x))

    {-
        \A n \in Nat : (even x) -> (odd x+1)
    -}
    evenToOdd : {x : Nat} -> (Even x) -> (Odd (S x))
    evenToOdd EvenZero = OddOne
    evenToOdd (EvenNext y) = OddNext $ evenToOdd y

    -- Labs: oddToEven, ...
