module Lesson03

import Data.Vect

%default total


index' : Fin n -> Vect n a -> a
index' FZ (x :: xs) = x
index' (FS x) (y :: xs) = index' x xs

data Op : Nat -> Nat -> Type where
    Push : Integer -> Op k (S k)
    Pop : Op (S k) k
    Add : Op (S (S k)) (S k)

run : Op k n -> Vect k Integer -> Vect n Integer
run (Push i) xs = i :: xs
run Pop (x :: xs) = xs
run Add (x :: (y :: xs)) = x + y :: xs

-- printf! ("%s = %d", "fsdf", "fsdf")
-- printf "%s = %d" : String -> Nat -> String
-- printf "%s" : String -> String
-- printf "%d" : Nat -> String


data Format = Number Format
            | Str Format
            | Lit Char Format
            | End

-- Str (Lit " = " (Number End))

PrintfType : Format -> Type
PrintfType (Number x) = (i : Int) -> PrintfType x
PrintfType (Str x) = (s : String) -> PrintfType x
PrintfType (Lit str x) = PrintfType x
PrintfType End = String

printFmt : (fmt : Format) -> (acc : String) -> PrintfType fmt
printFmt (Number x) acc = \i => printFmt x (acc ++ show i)
printFmt (Str x) acc = \s => printFmt x (acc ++ s)
printFmt (Lit str x) acc = printFmt x (acc ++ pack [str])
printFmt End acc = acc


toFormat : (xs : List Char) -> Format
toFormat [] = End
toFormat ('%' :: 'd' :: xs) = Number (toFormat xs)
toFormat ('%' :: 's' :: xs) = Str (toFormat xs)
toFormat (x :: xs) = Lit x (toFormat xs)

data Matter = Solid | Liquid | Gas

Eq Matter where
    Solid == Solid = True
    Liquid == Liquid = True
    Gas == Gas = True
    _ == _ = False

record Album where
    constructor MkAlbum
    artist : String
    title : String
    year : Integer


Eq Album where
    (==) (MkAlbum artist1 title1 year1) (MkAlbum artist2 title2 year2) =
        artist1 == artist2 && title1 == title2 && year1 == year2

Show Album where
    show (MkAlbum artist title year) = ""

Cast (Maybe a) (List a) where
    cast Nothing = []
    cast (Just a) = [a]

--data Foo = Foo {
--    bar :: String
-- }

exactLength : {m : Nat} -> (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength len input = case m == len of
                             False => Nothing
                             True => Just input
