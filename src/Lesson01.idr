module Lesson01

import Data.Vect

%default total

i : Int
i = 59874593847598547 * 45325856

ii : Integer
ii = 59874593847598547 * 45325856

b : Bool
b = True

s : String
s = "fsdf"

c : Char
c = 's'

t : (Int, Integer, Char)
t = (?t_rhs_0, (?t_rhs_2, ?t_rhs_3))

l : List Int
l = []

f : Bool -> String
f False = "False"
f True = "True"

StringOrInt : Bool -> Type
StringOrInt False = Int
StringOrInt True = String

strOrInt : (x : Bool) -> StringOrInt x
strOrInt False = 42
strOrInt True = "42"

n : Nat
n = 0

len : List a -> Nat
len [] = Z
len (_ :: xs) = S (len xs)

v : Vect 4 Int
v = [1,2,3,4]

v' : Vect 5 Int
v' = 5 :: v

len' : {k: Nat} -> Vect k a -> Nat
len' xs = k

ll : List Nat
ll = do
    a <- [1,2,3]
    b <- [4,5,6]
    c <- [7,8,9]
    [a, b, c]

vv : Vect 3 Nat
vv = do
    a <- [1,2,3]
    b <- [4,5,6]
    c <- [7,8,9]
    [a, b, c]

vvv : Vect 2 Nat
vvv = do
    a <- [1,2]
    b <- [4,5]
    c <- [7,8]
    [a, c]

public export
msg : String
msg = "Everything I Say Will Be On the Exam"
