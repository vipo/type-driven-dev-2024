Require Import Bool Arith List.
Import ListNotations.
Require Extraction.
Set Implicit Arguments.

From Hammer Require Import Tactics.

Check 5.
Check tt.
Check unit.
Check true.
Check True.

Compute let f := fun x => (x*3, x) in f 3.

Lemma example1: forall a b: Prop, a /\ b -> b /\ a.
intros a b H.
split.
destruct H as [H1 H2].
exact H2.
destruct H as [H1 H2].
exact H1.
Qed.

Lemma example2: forall a b: Prop, a /\ b -> b /\ a.
Proof.
sauto.
Qed.

Print example1.

Inductive natlist: Type :=
| nil
| cons (n: nat) (l: natlist).

Print natlist_ind.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Fixpoint app (l1 l2: natlist): natlist :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Compute app mylist mylist.

Example test1: app mylist mylist = cons 1 (cons 2 (cons 3 (cons 1 (cons 2 (cons 3 nil))))).
Proof.
reflexivity.
Qed.

Theorem app_assoc: forall (lst1 lst2 lst3 : natlist), app (app lst1 lst2) lst3 = app lst1 (app lst2 lst3).
Proof.
intros lst1 lst2 lst3.
induction lst1 as [| h1 h2].
reflexivity.
simpl.
rewrite IHh2.
reflexivity.
Qed.

Fixpoint length (lst: natlist): nat :=
  match lst with
  | nil => 0
  | cons _ t => S (length t)
  end.
 
Compute length mylist.

Theorem app_lenght : forall (lst1 lst2 : natlist), length (app lst1 lst2) = (length lst1) + (length lst2).
Proof.
intros lst1 lst2.
induction lst1.
reflexivity.
simpl.
rewrite IHlst1. 
reflexivity.
Qed.

Fixpoint rev (lst : natlist): natlist :=
  match lst with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
  
Example test_rev: rev mylist = cons 3 (cons 2 (cons 1 nil)).
Proof.
reflexivity.
Qed.

Theorem rev_length : forall (lst : natlist), length (rev lst) = length lst.
Proof.
intros lst.
induction lst.
reflexivity.
simpl.
rewrite app_lenght.
simpl.
rewrite IHlst.
rewrite Nat.add_comm.
reflexivity.
Qed.

Check Nat.add_comm.


Definition tl (lst: natlist) : natlist :=
  match lst with
  | nil => nil
  | cons _ t => t
  end.
  
Print pred.
  
Theorem tl_length_pred : forall (lst : natlist), pred (length lst) = length (tl lst).
Proof.
intros lst.
destruct lst.
reflexivity.
reflexivity.
Qed.


Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.

Fixpoint expDenote (e : exp) : nat :=
  match e with
  | Const n => n
  | Binop b op1 op2 => (binopDenote b) (expDenote op1) (expDenote op2)
  end.
  

Eval simpl in expDenote (Binop Times (Const 2) (Const 2)).
Compute expDenote (Binop Times (Const 2) (Const 2)).

Inductive instr : Set :=
|iConst : nat -> instr
|iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list nat.


Definition instrDenote (i : instr) (s: stack) : option stack :=
  match i with
  |iConst n => Some (n :: s)
  |iBinop b =>
    match s with
    | arg1 :: arg2 :: s' =>
      Some ((binopDenote b) arg1 arg2 :: s')
    | _ => None
    end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
  | [] => Some (s)
  | i :: p' =>
    match instrDenote i s with
    |None => None
    |Some s' => progDenote p' s'
    end
  end.

Fixpoint compile (e : exp) : prog :=
  match e with
  |Const n => iConst n :: []
  |Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: []
  end.

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Check app_assoc_reverse.

Theorem compile_correct :
  forall e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s).
Proof.
induction e.
intros.
simpl.
reflexivity.
intros.
simpl.
rewrite app_assoc_reverse.
rewrite IHe2.
rewrite app_assoc_reverse.
rewrite IHe1.
simpl.
reflexivity.
Qed.

Print compile_correct.

Extraction Language Haskell.
Extraction compile.