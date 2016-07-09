Module AExp.

Inductive aexp : Type := 
 | ANum   : nat -> aexp
 | APlus  : aexp -> aexp -> aexp
 | AMinus : aexp -> aexp -> aexp
 | AMult  : aexp -> aexp -> aexp.

Inductive bexp : Type := 
 | BTrue  : bexp
 | BFalse : bexp
 | BEq    : aexp -> aexp -> bexp
 | BLe    : aexp -> aexp -> bexp
 | BNot   : bexp -> bexp
 | BAnd   : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
 match a with
 | ANum n => n
 | APlus a1 a2 => (aeval a1) + (aeval a2)
 | AMinus a1 a2 => (aeval a1) - (aeval a2)
 | AMult a1 a2 => (aeval a1) * (aeval a2)
end.

Notation beq_nat := Nat.eqb (compat "8.4").

Notation leb := Nat.leb (compat "8.4").

Fixpoint beval (b : bexp) : bool :=
 match b with
 | BTrue => true
 | BFalse => false
 | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
 | BLe a1 a2 => leb (aeval a1) (aeval a2)
 | BNot b1 => negb (beval b1)
 | BAnd b1 b2 => andb (beval b1) (beval b2)
end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall a, aeval (optimize_0plus a) = aeval a.
Proof.
intros a.
induction a.
simpl.
reflexivity.
destruct a1.
destruct n.
simpl.
apply IHa2.
simpl.
rewrite IHa2.
simpl.
reflexivity.
simpl.
simpl in IHa1.
rewrite IHa1.
rewrite IHa2.
reflexivity.
simpl.
simpl in IHa1.
rewrite IHa1.
rewrite IHa2.
reflexivity.
simpl.
simpl in IHa1.
rewrite IHa1.
rewrite IHa2.
reflexivity.
simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
simpl.
rewrite IHa1.
rewrite IHa2.
reflexivity.
Qed.

Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof.
try reflexivity.
Qed.

Theorem silly2 : forall(P : Prop), P -> P.
Proof.
intros P HP.
try reflexivity.
apply HP.
Qed.

Lemma foo : forall n, leb 0 n = true.
Proof.
intros.
destruct n;
simpl;
reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a, aeval (optimize_0plus a) = aeval a.
Proof.
intros a.
induction a;
try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
reflexivity.
destruct a1;
try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
destruct n;
      simpl; rewrite IHa2; reflexivity.
Qed.

(*General form of ; : T; [T1 | T2 | ... | Tn]*)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
   | BTrue => BTrue
   | BFalse => BFalse
   | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
   | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
   | BNot b1 => BNot (optimize_0plus_b b1)
   | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound:
  forall e, beval (optimize_0plus_b e) = beval e.
Proof.
intro e.
  induction e;
    try reflexivity;
    try (simpl; rewrite 2 optimize_0plus_sound; reflexivity).
    simpl. rewrite IHe. reflexivity.
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

Require Import Coq.omega.Omega.

Module aevalR_first_try.


Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall(e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).
