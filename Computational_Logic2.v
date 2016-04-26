Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Definition pred (x : nat) : nat :=
 match x with
   | O => O
   | S x' => x'
end.

Compute pred (S(S O)).

Compute pred (S(S(S(S(S(S(S(S(S(S(S(S(S(S(S O))))))))))))))).

Fixpoint plus (x y : nat) : nat :=
  match x with
   | O => y
   | S x' => S 
(plus x' y)
end.

Compute plus (S O)(S O).

Fixpoint leb (x y : nat) : bool :=
  match x with
   | O => true
   | S x' => match y with
              | O => false
              | S y' => leb x' y'
               end
end.

Fixpoint mult (x y : nat) : nat :=
  match x with
   | O => O
   | S x => plus x (mult x y)
end.

Lemma plus_O x : plus x O = x.
Proof.
induction x; simpl.
reflexivity.
rewrite IHx.
reflexivity.
Qed.

Lemma plus_S x y : plus x (S y) = S (plus x y).
Proof.
induction x; simpl.
reflexivity.
rewrite IHx.
reflexivity.
Qed.

Lemma plus_com x y : plus x y = plus y x.
Proof.
induction x; simpl.
rewrite plus_O; reflexivity.
rewrite plus_S; rewrite IHx.
reflexivity.
Qed.

Lemma plus_asso x y z : plus (plus x y) z = plus x (plus y z).
Proof.
induction x; simpl.
reflexivity.
rewrite IHx.
reflexivity.
Qed.

Print plus_asso.

Require Import Omega.

Lemma plus_AC x y z : plus y (plus x z) = plus (plus z y) x.
Proof.
setoid_rewrite plus_com at 3.
setoid_rewrite plus_com at 1.
apply plus_asso.
Qed.
