Theorem identity_fn_applied_twice : forall (f : bool -> bool), (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
intros.
rewrite -> H.
rewrite -> H.
reflexivity.
Qed.


Theorem andb_eq_orb : forall (b c : bool),(andb b c = orb b c) -> b = c.
Proof.
intros.
destruct b.
destruct c.
reflexivity.
Lemma andb_true_false : andb true false = false.
simpl.
reflexivity.
Qed.
Lemma orb_true_false : orb true false = true.
simpl.
reflexivity.
Qed.
rewrite -> andb_true_false in H.
rewrite -> orb_true_false in H.
symmetry.
apply H.
destruct c.
Lemma andb_false_true : andb false true = false.
simpl.
reflexivity.
Qed.
Lemma orb_false_true : orb false true = true.
simpl.
reflexivity.
Qed.
rewrite -> andb_false_true in H.
rewrite -> orb_false_true in H.
apply H.
reflexivity.
Qed.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem and_true_elim : forall b c : bool, andb b c = true -> b = true.
Proof.
intros b c H.
destruct b.
Case "b = true".
reflexivity.
rewrite <- H.
reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
intros b c H.
destruct c.
Case "c = true".
reflexivity.
Case "c = false".
rewrite <- H.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem plus_zero : forall n :nat, n + 0 = n.
Proof.
intros n.
destruct n as [| n'].
Case "n = 0".
simpl.
reflexivity.
Case "S n != 0".
simpl.
Abort.


Theorem plus_zero' : forall n : nat, n + 0 = n.
Proof.
intros n.
induction n.
Case "n = 0".
simpl.
reflexivity.
Case "n != 0".
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem minus_diag : forall n : nat, n - n = 0.
Proof.
intros n.
induction n.
Case "n = 0".
simpl.
reflexivity.
Case "n != 0".
simpl.
apply IHn.
Qed.


Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
intros n.
induction n.
Case "n = 0".
simpl.
reflexivity.
simpl.
apply IHn.
Qed.


Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
intros n m.
induction n.
simpl in |- *.
reflexivity.
auto.
Qed.


Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
intros n m.
induction n.
induction m.
simpl.
reflexivity.
simpl.
rewrite <- IHm.
simpl.
reflexivity.
simpl.
rewrite IHn.
elim m.
simpl.
reflexivity.
intros m'.
intros IHm.
simpl.
rewrite IHm.
reflexivity.
Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n.
induction m.
induction p.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_plus : forall n : nat, double n = n + n.
Proof.
intros n.
induction n.
reflexivity.
simpl.
rewrite -> IHn.
rewrite -> plus_n_Sm.
reflexivity.
Qed.

Theorem mult_0_plus : forall n m : nat, (0 + n) * m = n * m.
Proof.
intros n m.
assert (H : 0 + n = n).
simpl.
reflexivity.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
intros n m p q.
assert (H : n + m = m + n).
rewrite -> plus_comm; reflexivity.
rewrite -> H.
reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
intros n m p.
rewrite -> plus_comm.
rewrite -> plus_assoc.
induction n.
induction m.
induction p.
simpl.
reflexivity.
rewrite -> plus_zero'.
simpl.
reflexivity.
rewrite -> plus_zero'.
rewrite -> plus_zero'.
reflexivity.
rewrite <- plus_assoc.
rewrite <- plus_assoc.
assert (H : p + S n = S n + p).
rewrite -> plus_comm.
reflexivity.
rewrite -> H.
reflexivity.
Qed.


Theorem mult_comm : forall m n : nat, m * n = n * m.
Proof.
intros m n.
induction m.
rewrite -> mult_0_r.
simpl.
reflexivity.
induction n.
simpl.
rewrite -> mult_0_r.
reflexivity.
simpl.
rewrite -> IHm.
simpl.
rewrite -> plus_swap.
Lemma mult_1: forall n m : nat, n + n * m = n * S m.
intros n m.
induction n.
induction m.
simpl.
reflexivity.
reflexivity.
simpl.
rewrite <- IHn.
rewrite -> plus_assoc.
rewrite -> plus_assoc.
assert (H : n + m = m + n).
rewrite -> plus_comm.
reflexivity.
rewrite -> H.
reflexivity.
Qed.
rewrite -> mult_1.
reflexivity.
Qed.

Print plus_comm.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Theorem evenb_n__oddb_Sn : forall n : nat, evenb n = negb (evenb (S n)).
Proof.
intros n.
induction n.
simpl.
reflexivity.
assert (evenb n = evenb (S (S n))) as H.
reflexivity.
rewrite <- H.
rewrite IHn.
Lemma negb_involutive : forall b, negb (negb b) = b.
Proof.
intros b.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.
rewrite -> negb_involutive.
reflexivity.
Qed.


Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  if andb (ble_nat n m) (negb (beq_nat n m)) then true else false.

Theorem ble_nat_refl : forall n : nat, true = ble_nat n n.
Proof.
intros n.
induction n.
simpl.
reflexivity.
simpl.
rewrite -> IHn.
reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat, beq_nat 0 (S n) = false.
Proof.
intros n.
induction n.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
intros b.
destruct b.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat, ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
intros n m p.
intros H.
simpl.
induction p.
simpl.
rewrite H.
reflexivity.
simpl.
rewrite IHp.
reflexivity.
Qed.

Theorem S_nbeq_0 : forall n : nat, beq_nat (S n) 0 = false.
Proof.
intros n.
reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
intros n.
simpl.
rewrite -> plus_zero'.
reflexivity.
Qed.

Theorem all3_spec : forall b c : bool, orb (andb b c)(orb (negb b)(negb c)) = true.
Proof.
intros b c.
destruct b.
destruct c.
simpl.
reflexivity.
simpl.
reflexivity.
destruct c.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat, (n + m) * p = (n * p) + (m * p).
Proof.
intros n m p.
induction n.
reflexivity.
simpl.
rewrite IHn.
rewrite plus_assoc.
reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat, n * (m * p) = (n * m) * p.
Proof.
intros n m p.
induction n.
reflexivity.
simpl.
rewrite IHn.
rewrite mult_plus_distr_r.
reflexivity.
Qed.
