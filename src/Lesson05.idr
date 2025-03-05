module Lesson05

import Data.Vect
import Decidable.Equality

%default total


test : Void -> Vect 1 Int
test _ = [1]


test1 : Void -> 3 = 3
test1 _ = Refl

test2 : Void -> 3 = 2
test2 _ impossible

failing 
    test3 : 2 + 2 = 4 -> Void
    test3 Refl impossible

twoPlusTwoIsNotFive: 2 + 2 = 5 -> Void
twoPlusTwoIsNotFive Refl impossible

zeroNotSuc : 0 = S k -> Void
zeroNotSuc Refl impossible

sucNotZero : S k = 0 -> Void
sucNotZero Refl impossible

noRec : (k = j -> Void) -> S k = S j -> Void
noRec f Refl = f Refl

checkEqNat : (nat1 : Nat) -> (nat2 : Nat) -> Dec (nat1 = nat2)
checkEqNat 0 0 = Yes Refl
checkEqNat 0 (S k) = No zeroNotSuc
checkEqNat (S k) 0 = No sucNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              (Yes prf) => Yes $ cong S prf
                              (No contra) => No $ noRec contra

exactLength : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength len input = case checkEqNat m len of
                             (Yes Refl) => Just input
                             (No contra) => Nothing

exactLength' : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength' len input = case decEq m len of
                              (Yes Refl) => Just input
                              (No contra) => Nothing

failing
    loop : Void
    loop = loop


---------

-- proof by simplification

plusZn : (n : Nat) -> Z + n = n
plusZn n = Refl

plus1l : (n : Nat) -> 1 + n = S n
plus1l n = Refl

-- proof by induction

plusNz : (n : Nat) -> n + Z = n
plusNz 0 = Refl
plusNz (S k) =
    let indH = plusNz k in
    cong S indH

plusNz' : (n : Nat) -> n + Z = n
plusNz' 0 = Refl
plusNz' (S k) =
    let indH = plusNz' k in
    rewrite indH in Refl

plus_id : (n, m : Nat) -> (n = m) -> n + n = m + m
plus_id n n Refl = Refl

plus_id' : (n, m : Nat) -> (n = m) -> n + n = m + m
plus_id' n m prf = rewrite prf in Refl

plus_n_Sm : (n, m : Nat) -> S (n+m) = n + S m
plus_n_Sm 0 m = Refl
plus_n_Sm (S k) m =
    let indH = plus_n_Sm k m in
    rewrite indH in Refl

plus_comm : (n, m : Nat) -> n + m = m + n
plus_comm 0 m = rewrite plusNz m in Refl
plus_comm (S k) m =
    let indH = plus_comm k m in
    rewrite indH in
    rewrite plus_n_Sm m k in
    Refl

double : (n : Nat) -> Nat
double 0 = 0
double (S k) = S (S (double k))

double_plus : (n : Nat) -> double n = n + n
double_plus 0 = Refl
double_plus (S k) =
    let indH = double_plus k in
    rewrite indH in
    rewrite plus_n_Sm k k in
    Refl
