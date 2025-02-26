module Lesson04

import Data.Vect

%default total

failing
    exactLength : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
    exactLength len input = case m == len of
                            False => Nothing
                            True => Just input

data EqNat : (nat1 : Nat) -> (nat2 : Nat) -> Type where
    Same : (nat : Nat) -> EqNat nat nat


sameS : (k : Nat) -> (j : Nat) -> EqNat k j -> EqNat (S k) (S j)
sameS k k (Same k) = Same (S k)

checkEqNat : (nat1 : Nat) -> (nat2 : Nat) -> Maybe (EqNat nat1 nat2)
checkEqNat 0 0 = Just (Same 0)
checkEqNat 0 (S k) = Nothing
checkEqNat (S k) 0 = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just x) => Just (sameS k j x)

exactLength : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength len input = case checkEqNat len m of
                             Nothing => Nothing
                             (Just (Same m)) => Just input

-- data (=) -> a -> b -> Type
--    Refl: a -> a = a 

test : 5 = 5
test = Refl

failing
    test' : 5 = 1
    test' = Refl

checkEqNat' : (nat1 : Nat) -> (nat2 : Nat) -> Maybe (nat1 = nat2)
checkEqNat' 0 0 = Just Refl
checkEqNat' 0 (S k) = Nothing
checkEqNat' (S k) 0 = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                               Nothing => Nothing
                               (Just Refl) => Just Refl

checkEqNat'' : (nat1 : Nat) -> (nat2 : Nat) -> Maybe (nat1 = nat2)
checkEqNat'' 0 0 = Just Refl
checkEqNat'' 0 (S k) = Nothing
checkEqNat'' (S k) 0 = Nothing
checkEqNat'' (S k) (S j) = case checkEqNat'' k j of
                                Nothing => Nothing
                                (Just x) => Just $ cong S x

exactLength' : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength' len input = case checkEqNat'' m len of
                              Nothing => Nothing
                              (Just Refl) => Just input

test1 : S k = S k
test1 = Refl

test2 : S k = plus 1 k
test2 = Refl

failing
    test3 : S k = plus k 1
    test3 = Refl

    test4 : plus k 1 = S k 
    test4 = Refl

myReverseProof : Vect (plus len 1) a -> Vect (S len) a
myReverseProof xs = rewrite plusCommutative 1 len in xs

myReverse : Vect n a -> Vect n a
myReverse [] = []
myReverse (x :: xs) = myReverseProof $ myReverse xs ++ [x]

myReverse' : {n: Nat} -> Vect n a -> Vect n a
myReverse' {n = 0} [] = ?myReverse'_rhs_0
myReverse' {n = (S len)} (x :: xs) = let rev_xs = myReverse xs
                                         result = rev_xs ++ [x] in
                                         rewrite plusCommutative 1 len in result

append' : Vect n e -> Vect m e -> Vect (n + m) e
append' [] ys = ys
append' (x :: xs) ys = x :: append' xs ys

failing 
    test10 : m = plus m 0
    test10 = Refl

test11 : m = plus 0 m
test11 = Refl

failing
    append'' : Vect n e -> Vect m e -> Vect (m + n) e
    append'' [] ys = ys
    append'' (x :: xs) ys = ?append''_rhs_1
