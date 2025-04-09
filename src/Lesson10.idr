module Lesson10
import Data.Bits
import Data.Stream
import Data.Primitives.Views
import System
%default total

labelFrom : List a -> List (Nat, a)
labelFrom xs = help 0 xs
    where
        help : Nat -> List a -> List (Nat, a)
        help k [] = []
        help k (x :: xs) = (k, x) :: help (k+1) xs

failing
    countFrom : Integer -> List Integer
    countFrom i = i :: countFrom (i+1)

namespace BasicSolution

    makeNext : Integer -> Integer
    makeNext i = i+1

    data Counter = MkCounter Integer (Integer -> Integer)

    inc : Counter
    inc = MkCounter 0 makeNext

    nxt : Counter -> (Integer, Counter)
    nxt (MkCounter i f) = (i, MkCounter (f i) f)


data InfList : Type -> Type where
    (::) : (value : e) -> Inf (InfList e) -> InfList e

countFrom : Integer -> InfList Integer
countFrom i = (i :: (Delay (countFrom (i+1))))

getPrefix : Nat -> InfList a -> List a
getPrefix 0 x = []
getPrefix (S k) (value :: il) = value :: getPrefix k (Force il)

{-
  Total:
    - well typed.
    - call cases.
    - either consumes data.
    - either produces (co)data.
-}

export
labelWith : Stream l -> List a -> List (l, a)
labelWith ls [] = []
labelWith (l :: ls) (x :: xs) = (l, x) :: labelWith ls xs


export
covering -- Non total, because non-productive nor terminating.
quiz: Stream Int -> (score : Nat) -> IO ()
quiz (x :: y :: z) score =
    do  putStrLn ("Score so far: " ++ show score)
        putStr (show x ++ " * " ++ show y ++ "?")
        answer <- getLine
        if cast answer == x * y
            then do putStrLn "Correct!"
                    quiz z (score + 1)
            else do putStrLn ("Wrong, the answer is " ++ show (x * y))
                    quiz z score



data InfIO : Type where
    Do : IO a -> (a -> Inf InfIO) -> InfIO


total
loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)

namespace Temp

    export
    covering
    run : InfIO -> IO ()
    run (Do action f) =
        do  res <- action
            run (f res)


namespace MyFuel

    data Fuel = Dry | More Fuel

    export
    tank : Nat -> Fuel
    tank 0 = Dry
    tank (S k) = More (tank k)

    export
    total
    run : Fuel -> InfIO -> IO ()
    run Dry iio = putStrLn "I'm done.."
    run (More fuel) (Do action iio) =
        do  res <- action
            run fuel (iio res)


public export
data Fuel' = Dry | More (Lazy Fuel')

export
covering
forever : Fuel'
forever = More forever

export
tank : Nat -> Fuel'
tank 0 = Dry
tank (S k) = More (tank k)

export
total
run : Fuel' -> InfIO -> IO ()
run Dry iio = putStrLn "I'm done.."
run (More fuel) (Do action iio) =
    do  res <- action
        run fuel (iio res)


namespace MakeItDoable

    export
    (>>=) : IO a -> (a -> Inf InfIO) -> InfIO
    (>>=) = Do

    export
    (>>) : IO a -> Inf InfIO -> Inf InfIO
    (>>) a c = Do a (\_ => c)

export
total
quiz': Stream Int -> (score : Nat) -> InfIO
quiz' (x :: y :: z) score =
    do  putStrLn ("Score so far: " ++ show score)
        putStr (show x ++ " * " ++ show y ++ "?")
        answer <- getLine
        if cast answer == x * y
            then do putStrLn "Correct!"
                    quiz' z (score + 1)
            else do putStrLn ("Wrong, the answer is " ++ show (x * y))
                    quiz' z score

covering
quiz'Main : IO ()
quiz'Main =
    do  seed <- time
        run forever (quiz' [1, 2..] 0)
