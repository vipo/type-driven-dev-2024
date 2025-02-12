module Lesson02

import Data.Vect

%default total

append : Vect n a -> Vect m a -> Vect (n+m) a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys


-- ADT
-- Enumeration
data Direction = North
               | East
               | South
               | West

turn : Direction -> Direction
turn North = East
turn East = South
turn South = West
turn West = North

-- Union
data Shape = Triangle Double Double
           | Rectangle Double Double
%name Shape shape, shape1, shape2

data Picture = Primitive Shape
             | Combination Shape Shape
%name Picture pic, pic1, pic2, pic3

testPicture : Picture
testPicture = Combination (Triangle ?testPicture_rhs_2 ?testPicture_rhs_3) (Rectangle ?testPicture_rhs_4 ?testPicture_rhs_5)

pictureArea : Picture -> Double
pictureArea (Primitive shape) = ?pictureArea_rhs_0
pictureArea (Combination (Triangle dbl dbl1) shape1) = ?pictureArea_rhs_2
pictureArea (Combination (Rectangle dbl dbl1) shape1) = ?pictureArea_rhs_3

-- Generics
data Tree a = Empty
            | Node (Tree a) a (Tree a)
%name Tree tree, tree1, tree2

insert : Ord e => e -> Tree e -> Tree e
insert x Empty = Node Empty x Empty
insert x orig@(Node tree y tree1) = case compare x y of
                                    LT => Node (insert x tree) y tree1
                                    EQ => orig
                                    GT => Node tree y (insert x tree1)

data BSTree : Type -> Type where
    BSEmpty : Ord a => BSTree a
    BSNode : Ord a => (left: BSTree a) -> a -> (right: BSTree a) -> BSTree a

insert' : e -> BSTree e -> BSTree e
insert' x BSEmpty = BSNode BSEmpty x BSEmpty
insert' x (BSNode left y right) = ?insert'_rhs_1

-- Dependant

data PowerSource = Petrol | Pedal

data Vehicle : PowerSource -> Type where
    Bicycle : Vehicle Pedal
    Tricycle : Vehicle Pedal
    Car : (fuel: Nat) -> Vehicle Petrol
    Bus : (fuel: Nat) -> Vehicle Petrol

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car (S fuel)
refuel (Bus fuel) = Bus (S (S fuel))
refuel Bicycle impossible

data DataStore : Type where
    MkData : (size : Nat) -> (items : Vect size String) -> DataStore


size : DataStore -> Nat
size (MkData k _) = k

items : (store : DataStore) -> Vect (size store) String
items (MkData size xs) = xs

addToTail : Vect size_0 String -> String -> Vect (S size_0) String
addToTail [] str = [str]
addToTail (x :: xs) str = x :: addToTail xs str

addToStore : DataStore -> String -> DataStore
addToStore (MkData size items) str = MkData (S size) (addToTail items str)

dependantPair : (len ** Vect len String)
dependantPair = (2 ** ["labas", "medis"])

covering
readVect : IO (len ** Vect len String)
readVect = do
            x <- getLine
            case x == "" of
                 True => pure (0 ** [])
                 False => do (_ ** xs) <- readVect
                             pure (_ ** x :: xs)
