module Lesson13
import System
import System.Concurrency
import Data.List
import Data.Fuel
%default total

namespace SimpleThreads

  th1 : IO ()
  th1 = putStrLn "thread 1"

  th2 : IO ()
  th2 = putStrLn "thread 2"

  export
  main : IO ()
  main = do
    tid1 <- fork th1
    tid2 <- fork th2
    threadWait tid1
    threadWait tid2

namespace CommViaChannels

  th1 : Nat -> Channel Nat -> Channel Nat -> IO ()
  th1 n chOut chInp = do
    channelPut chOut n
    m <- channelGet chInp
    putStrLn "thread 1, send \{show n}, received \{show m}"

  th2 : Nat -> Channel Nat -> Channel Nat -> IO ()
  th2 n chOut chInp = do
    channelPut chOut n
    -- channelPut chOut n
    m <- channelGet chInp
    -- m2 <- channelGet chInp
    putStrLn "thread 2, send \{show n}, received \{show m}"

  export
  main : IO ()
  main = do
    ch12 <- makeChannel {a=Nat}
    ch21 <- makeChannel {a=Nat}
    tid1 <- fork (th1 7 ch12 ch21)
    tid2 <- fork (th2 5 ch21 ch12)
    threadWait tid1
    threadWait tid2

namespace ViaTypes

  namespace Interaction
    public export
    data Interaction : Type where
      Send : {a : Type} -> Channel a -> Interaction
      Recv : {a : Type} -> Channel a -> Interaction
      Done : Interaction
      (>>): Interaction -> Interaction -> Interaction

  public export
  CoInteraction : Interaction -> Interaction
  CoInteraction (Send ch) = Recv ch
  CoInteraction (Recv ch) = Send ch
  CoInteraction Done = Done
  CoInteraction (x >> y) = (CoInteraction x) >> (CoInteraction y)

  namespace Process
    public export
    data Process : Type -> Interaction -> Interaction -> Type where
      Send : {a : Type} -> {ch : Channel a} -> (msg : a) -> Process () ((Send ch) >> ib) ib
      Recv : {a : Type} -> {ch : Channel a} -> Process a (Recv ch >> ib) ib
      Action : IO a -> Process a i i
      Pure : a -> Process a Done Done
      (>>) : {t1 : Type} -> Process t1 ia ib -> Process t2 ib ic -> Process t2 ia ic
      (>>=) : {t1 : Type} -> {t2 : Type} -> Process t1 ia ib -> (t1 -> Process t2 ib ic) -> Process t2 ia ic

  public export
  run : {a : Type} -> Process a ia ib -> IO a
  run (Send msg {ch}) = channelPut ch msg
  run (Recv {ch}) = channelGet ch
  run (Action act) = act
  run (Pure x) = pure x
  run (x >> y) = do _ <- run x; run y
  run (x >>= f) = do r <- run x; run (f r)


  namespace Example

    public export
    example : (req : Channel Nat) -> (res : Channel Nat) -> Interaction
    example req res = do
      Send req -- Send 1st number.
      Send req -- Send 2nd number.
      Recv res -- Receive the result.
      Done

    implClient :
      {req : Channel Nat} ->
      {res : Channel Nat} ->
      (a : Nat) ->
      (b : Nat) ->
      Process Nat (example req res) Done
    implClient a b = do
      Send a
      Send b;    Action (putStrLn "CLIENT: Waiting for response...")
      x <- Recv; Action (putStrLn "CLIENT: Received response \{show x}")
      Pure x

    implServer :
      {req : Channel Nat} ->
      {res : Channel Nat} ->
      (f : Nat -> Nat -> Nat) ->
      Process Nat (CoInteraction (example req res)) Done
    implServer f = do
      a <- Recv;    Action (putStrLn "SRV: Received param a=\{show a}")
      b <- Recv;    Action (putStrLn "SRV: Received param b=\{show b}")
      Send (f a b); Action (putStrLn "SRV: Will respond with \{show (f a b)}")
      Pure 0

    export
    run : IO ()
    run = do
      req <- makeChannel {a=Nat}
      res <- makeChannel {a=Nat}
      tid1 <- fork (do _ <- run (implClient {req} {res} 2 3); pure ())
      tid2 <- fork (do _ <- run (implServer {req} {res} (*)); pure ())
      threadWait tid1
      threadWait tid2
      putStrLn "Done"
      pure ()

namespace Looping

  public export
  data LoopingProcess : Type -> Interaction -> Interaction -> Type where
    Send : {a : Type} -> {ch : Channel a} -> (msg : a) -> LoopingProcess () ((Send ch) >> ib) ib
    Recv : {a : Type} -> {ch : Channel a} -> LoopingProcess a (Recv ch >> ib) ib
    Action : IO a -> LoopingProcess a i i
    Pure : a -> LoopingProcess a Done Done
    Loop :                              -- Added!
      Inf (LoopingProcess a ia Done) -> -- We can only loop to a terminating process.
      LoopingProcess a Done Done
    (>>) : {t1 : Type} -> LoopingProcess t1 ia ib -> LoopingProcess t2 ib ic -> LoopingProcess t2 ia ic
    (>>=) : {t1 : Type} -> {t2 : Type} -> LoopingProcess t1 ia ib -> (t1 -> LoopingProcess t2 ib ic) -> LoopingProcess t2 ia ic

  runLooping : {a : Type} -> Fuel -> LoopingProcess a ia ib -> IO (Maybe a)
  runLooping (More f) (Send msg {ch}) = do v <- channelPut ch msg; pure (Just v)
  runLooping (More f) (Recv {ch}) = do v <- channelGet ch; pure (Just v)
  runLooping (More f) (Action act) = do v <- act; pure (Just v)
  runLooping (More f) (Pure x) = pure (Just x)
  runLooping (More f) (Loop p) = runLooping f p
  runLooping (More f) (x >> y) = do
    _ <- runLooping f x;
    runLooping f y
  runLooping (More f) (x >>= y) = do
    r <- runLooping f x
    case r of
      Nothing => pure Nothing
      Just rv => runLooping f (y rv)
  runLooping Dry _ = pure Nothing


  namespace Example

    loopingClient :
      {req : Channel Nat} ->
      {res : Channel Nat} ->
      (vals : List (Nat, Nat)) ->
      {auto prf : NonEmpty vals} ->
      LoopingProcess Nat (example req res) Done
    loopingClient ((a, b) :: vals) = do
      Send a
      Send b;    Action (putStrLn "Waiting for response...")
      x <- Recv; Action (putStrLn "Received response \{show x}")
      case vals of
        [] => Pure x
        v :: vs => Loop (loopingClient {req} {res} (v :: vs))

    loopingServer :
      {req : Channel Nat} ->
      {res : Channel Nat} ->
      (f : Nat -> Nat -> Nat) ->
      LoopingProcess Nat (CoInteraction (example req res)) Done
    loopingServer {req} {res} f = do
      a <- Recv;    Action (putStrLn "Received param a=\{show a}")
      b <- Recv;    Action (putStrLn "Received param b=\{show b}")
      Send (f a b); Action (putStrLn "Will respond with \{show (f a b)}")
      case (a, b) of
        (0, 0) => Pure 0
        (_, _) => Loop (loopingServer {req} {res} f)

    export
    runExampleWithFuel : Fuel -> IO ()
    runExampleWithFuel f = do
      req <- makeChannel {a=Nat}
      res <- makeChannel {a=Nat}
      tid1 <- fork (do _ <- runLooping f (loopingClient {req} {res} [(1, 2), (2, 3), (0, 0)]); pure ())
      tid2 <- fork (do _ <- runLooping f (loopingServer {req} {res} (*)); pure ())
      threadWait tid1
      threadWait tid2
      putStrLn "Done"
      pure ()

    export
    covering -- Because of forever
    runExampleForever : IO ()
    runExampleForever = runExampleWithFuel forever
