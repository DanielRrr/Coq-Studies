Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with 
  | true => true
  | false => b2
  end.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => negb b2
  | false => true
end.

Example test_nandb1: (nandb true false) = true.
Proof.
reflexivity.
Qed.

Example test_nandb2: (nandb false false) = true.
Proof.
reflexivity.
Qed.

Example test_nandb3: (nandb false true) = true.
Proof.
reflexivity.
Qed.

Example test_nandb4: (nandb true true) = false.
Proof.
reflexivity.
Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
  | false => false
  | true => match b2 with
            | false => false
            | true => b3
            end
end.

Example test_andb31: (andb3 true true true) = true.
Proof.
reflexivity.
Qed.

Example test_andb32: (andb3 false true true) = false.
Proof.
reflexivity.
Qed.

Example test_andb33: (andb3 true false true) = false.
Proof.
reflexivity.
Qed.

Example test_andb34: (andb3 true true false) = false.
Proof.
reflexivity.
Qed.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Check S(S(S(S(S O)))).


Fixpoint plus (n : nat)(m : nat) : nat :=
  match n with
   | O => m
   | S n' => S (plus n' m)
end.

Fixpoint mult (n m : nat) : nat :=
  match n with
   | O => O
   | S n' => plus m (mult n' m)
end.

Notation "x + y" := (plus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x - y" := (minus x y) 
                       (at level 50, left associativity) 
                       : nat_scope.
Notation "x * y" := (mult x y) 
                       (at level 40, left associativity) 
                       : nat_scope.


Fixpoint minus (n m : nat) : nat :=
  match n,m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
end.


Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Fixpoint factorial (n : nat) : nat := 
  match n with 
    | O => S O
    | S n' => S n' * factorial n'
end.

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


Theorem plus_O_n : forall n : nat, O + n = n.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem mult_0_l : forall n : nat, O * n = O.
Proof.
intros.
simpl.
reflexivity.
Qed.

Theorem trivial : forall n m : nat, n = m -> n + n = m + m.
Proof.
intros n m H.
rewrite -> H.
reflexivity.
Qed.

Theorem trivial_two : forall n m o : nat, n = m -> m = o -> n + m = m + o.
Proof.
intros.
rewrite -> H.
rewrite -> H0.
reflexivity.
Qed.

Theorem trivial_three : forall n m : nat, (O + n) * m = n * m.
Proof.
intros.
rewrite -> plus_O_n.
reflexivity.
Qed.

Theorem trivial_four : forall n m : nat, m = S n -> m * (S O + n) = m * m.
Proof.
intros.
rewrite -> H.
simpl.
reflexivity.
Qed.
