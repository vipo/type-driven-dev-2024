||| Curry-Howard correspondence, propositional logic.
module Lesson06
%default total

------=================== Types <=> Theorems

-------- Implication

apply: a -> (a -> b) -> b
apply x f = f x

trans: (a -> b) -> (b -> c) -> a -> c
trans f g x = g (f x)


-- A => (A => B) => B

--     A => B, A
--    ----------- (MP, =>-elim)
--         B
--
--       A |- B
--   -------------- (=>-intro)
--      |- A => B
--
--    |- A => B, B => C
--   ---------------------
--         |- A => C
--
--  type `a` --> proposition A
--  a -> b   --> implication.
--

--    A => B, B
--  -------------
--      ???
ylppa : (a -> b) -> b -> a
ylppa f x = ?ylppa_rhs -- impossible.

natural : Nat
natural = 0

natto : (Nat -> String) -> String -> Nat
natto f str = 0

-- TRUE
tt : ()
tt = ()


---- Conjunction

{-
     |- A, B                    |- A /\ B                   |- A /\ B
  ------------- (/\-intro)    ------------- (/\-elim-1)   ------------- (/\=elim-2)
    |- A /\ B                    |- A                         |- B
-}


pair : a -> b -> (a, b)
pair x y = (x, y)

pair_elim_1 : (a, b) -> a
pair_elim_1 (x, _) = x

pair_elim_2 : (a, b) -> b
pair_elim_2 (_, y) = y


---- Disjunction

{-
       |- A
  --------------- (\/-intro-1)
     |- A \/ B

       |- B
  --------------- (\/-intro-2)
     |- A \/ B

-}

disj_intro_1 : a -> Either a b
disj_intro_1 x = Left x

disj_intro_2 : b -> Either a b
disj_intro_2 x = Right x


{- proof by cases.

  |- P => Q, R => Q, P \/ R
------------------------------ (\/-elim)
            |- Q
-}

disj_elim : (p -> q) -> (r -> q) -> Either p r -> q
disj_elim f g (Left x) = f x
disj_elim f g (Right x) = g x


---------  Negation

-- FALSE -- empty type.

false : Void


-- Neg

{-
   a,   b,   a -> b
   F    F      T
   F    T      T
   T    F      F
   T    T      T
-}

neg : a -> Void

{-
  P => Q     ==>     ~Q => ~P
-}

neg_contrapos : (p -> q) -> (Not q -> Not p)
neg_contrapos f g x = g (f x)

------=================== Impl <=> Proof

{- func application

 env |- e1 : t -> u,     env |- e2 : t
-----------------------------------------
           env |- e1 e2 : u

  |- A -> B, A
--------------- (MP)
    |-  B

-}

{- pair

 env |- e : (a, b)
--------------------    (/\-elim-1)
  env |- fst e : a

 env |- e : (a, b)
--------------------    (/\-elim-2)
  env |- snd e : b

-}


------=================== Eval <=> Proof simpl.

{-
THEOREM 1: B => A => (A /\ B)     -- note the order.


LEMMA 1: (B /\ A) => (A /\ B)
           x      =>     y
Proof.

Suffices assume (B /\ A) and prove (A /\ B) by (=>intro).
    / (B /\ A)=x, (A /\ B)=y...   x |- y    ------> |- x => y
From (B /\ A) we have (A) by (/\-elim-2).
From (B /\ A) we have (B) by (/\-elim-1).
From (A) and (B) we have (A /\ B) by (/\-intro). QED


Proof of THEOREM 1s.
Suffices assume (B) and prove (A => (A /\ B)) by (=>intro).
Next, suffices assume (A) and prove (A /\ B) by (=>intro).
From (B) and (A) we have (B /\ A) by (/\-intro).
From (B /\ A) we have (A /\ B) by LEMMA 1.
-}


{- ============================== Formal: LEMMA 1 ==============================
|  ------------------------------ (ax)          ------------------------------ (ax)
|   (B ∧ A) ⊢ (B ∧ A), (A ∧ B)                (B ∧ A) ⊢ (B ∧ A), (A ∧ B)
|  ------------------------------ (∧-elim)     ------------------------------- (∧-elim)
|       (B ∧ A) ⊢ A, (A ∧ B)                       (B ∧ A) ⊢ B, (A ∧ B)
|      --------------------------------------------------------------------- (∧-intro)
|                          (B ∧ A) ⊢ (A ∧ B), (A ∧ B)
|                         ------------------------------ (contr)
|                               (B ∧ A) ⊢ (A ∧ B)
|                            ------------------------ (⇒-intro)
|                              ⊢ (B ∧ A) ⇒ (A ∧ B)
|-}

{- ============================== Formal: THEOREM ==============================
|                                       ----------- (ax)   ----------- (ax)
|                                        B, A ⊢ B           B, A ⊢ A
|    ---------------------- (LEMMA 1)   ------------------------------ (∧-intro)
|     ⊢ (B ∧ A) ⇒ (A ∧ B)                     B, A  ⊢ (B ∧ A)
|    ------------------------------------------------------------ (⇒-elim)
|                          B, A  ⊢ (A ∧ B)
|                         ------------------ (⇒-intro)
|                          B ⊢ A ⇒ (A ∧ B)
|                        -------------------- (⇒-intro)
|                         ⊢ B ⇒ A ⇒ (A ∧ B)
|-}


pair_t : {a : Type} -> {b : Type} -> Type
pair_t = (a -> b -> (a, b))

pair_2 : pair_t {a} {b}
pair_2 x y = (\z => ((snd z), (fst z))) (y, x)

pair_2' : pair_t {a} {b}
pair_2' x y = ((snd (y, x)), (fst (y, x)))

pair_2'' : pair_t {a} {b}
pair_2'' x y = (x, (fst (y, x)))

pair_2''' : pair_t {a} {b}
pair_2''' x y = (x, y)


{- ========================= THEOREM (simplified) =========================
|    ------------ (ax)     ----------- (ax)
|      B, A ⊢ A             B, A ⊢ B
|    ---------------------------------- (∧-intro)
|             B, A ⊢ (A ∧ B)
|          ------------------- (⇒-intro)
|            B ⊢ A ⇒ (A ∧ B)
|         ---------------------- (⇒-intro)
|           ⊢ B ⇒ A ⇒ (A ∧ B)
|-}

{- =================== Proof as in math books ==================
|  THEOREM: B ⇒ A ⇒ (A ∧ B).
|
|  Proof of the THEOREM.
|  Suffices assume (B) and prove (A ⇒ A ∧ B) by "⇒-intro".
|  Next, suffices assume (A) and prove (A ∧ B) by "⇒-intro".
|  We have both (A) and (B), thus (A ∧ B) by "∧-intro". □
-}



-----------
-- traditional types provides smaller guarantees.

add_num : Nat -> Nat -> Nat
add_num a b = a + b

add_num' : Nat -> Nat -> Nat
add_num' a b = 0

-- add_num'' : (a : Nat) -> (b : Nat) -> a + b
