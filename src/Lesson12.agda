module Lesson12 where

module Basics where
    open import Agda.Builtin.Bool

    not : Bool → Bool
    not false = true
    not true = false

    data Nat : Set where
        zero : Nat
        succ : Nat → Nat

    _+_ : Nat → Nat → Nat
    zero + b = b
    succ a + b = succ (a + b)

    n-test : Nat
    n-test = zero + succ zero

    if_then_else_ : {A : Set} → Bool → A → A → A
    if false then a₁ else a₂ = a₂
    if true then a₁ else a₂ = a₁

    data _×_ (A B : Set) : Set where
        _,_ : A → B → A × B
    infixr 4 _,_
    
    p : Nat × Bool
    p = zero , true

    fst : {A B : Set} → A × B → A
    fst (x , x₁) = x

module Equiv where
    open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

    data _≡_ {A : Set} : A → A → Set where
        refl : {x : A} → x ≡ x
    infix 4 _≡_

    one-plus-one : 1 + 1 ≡ 2
    one-plus-one = refl

    data ⊥ :  Set where
        -- no constructors

    zero-not-one : 1 ≡ 0 → ⊥
    zero-not-one ()

    -- zero-not-one₁ : 1 ≡ 1 → ⊥
     

module StackMachine where
    open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
    open import Data.List using (List; []; [_]; _∷_; _++_)
    open import Data.Maybe
    open import Relation.Binary.PropositionalEquality using (_≡_; refl)
    open import Data.List.Properties using (++-assoc)
    

    data Binop : Set where
        Plus : Binop
        Times : Binop

    data Exp : Set where
        Const : ℕ → Exp
        Op : Binop → Exp → Exp → Exp

    binopDenote : Binop → ℕ → ℕ → ℕ
    binopDenote Plus o₁ o₂ = o₁ + o₂
    binopDenote Times o₁ o₂ = o₁ * o₂

    expDenote : Exp → ℕ
    expDenote (Const x) = x
    expDenote (Op x e e₁) = (binopDenote x) (expDenote e) (expDenote e₁)

    e-test₁ : expDenote (Op Plus (Const 1) (Const 2)) ≡ 3
    e-test₁ = refl

    data Instr : Set where
        IConst : ℕ → Instr
        IOp : Binop → Instr
    
    Prog = List Instr
    Stack = List ℕ

    instrDenote : Instr → Stack → Maybe Stack
    instrDenote (IConst x) s = just (x ∷ s) 
    instrDenote (IOp x) (x₁ ∷ x₂ ∷ s) =  just (binopDenote x x₁ x₂ ∷ s)
    instrDenote (IOp x) _ = nothing

    progDenote : Prog → Stack → Maybe Stack
    progDenote [] s = just s
    progDenote (x ∷ p) s with instrDenote x s
    ...                  | nothing = nothing
    ...                  | just y = progDenote p y

    compile : Exp → Prog
    compile (Const x) = [ IConst x ]
    compile (Op x e₁ e₂) = (compile e₂) ++ (compile e₁) ++ [ IOp x ]

    compileCorrect : ∀ (e : Exp) → ∀ (p : Prog) → ∀ (s : Stack) →
                     progDenote (compile e ++ p) s ≡ progDenote p (expDenote e ∷ s)
    compileCorrect (Const x) p s = refl
    compileCorrect (Op x e₁ e₂) p s 
                                    rewrite ++-assoc (compile e₂) (compile e₁ ++ IOp x ∷ []) p
                                    | compileCorrect e₂ ((compile e₁ ++ IOp x ∷ []) ++ p) s
                                    | ++-assoc (compile e₁) (IOp x ∷ []) p
                                    | compileCorrect e₁ (IOp x ∷ [] ++ p) (expDenote e₂ ∷ s)
                                    = refl


module EquationalReasonong where
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; trans)
    open import Data.List using (List; []; _∷_; _++_)
 
    begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
    begin p = p

    _end : {A : Set} → (x : A) → x ≡ x
    x end = refl

    _=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
    x =⟨ p ⟩ q = trans p q

    _=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
    x =⟨⟩ q = x =⟨ refl ⟩ q

    infix 1 begin_
    infix 3 _end
    infixr 2 _=⟨_⟩_
    infixr 2 _=⟨⟩_

    [_] : {A : Set} → A → List A
    [ x ] = x ∷ []

    reverse : {A : Set} → List A → List A
    reverse [] = []
    reverse (x ∷ l) = reverse l ++ [ x ]

    reverse-singleton : {A : Set} (x : A) → reverse [ x ] ≡ [ x ]
    reverse-singleton x =
        begin
            reverse [ x ]
        =⟨⟩
            reverse ( x ∷ [] )
        =⟨⟩ 
            reverse [] ++ [ x ]
        =⟨⟩
            [] ++ [ x ]
        =⟨⟩
            [ x ]
        end
