Goal false <> true.
intros A.
change (if false then True else False). 
rewrite A.
exact I.
Qed.

Variable n : nat.

Lemma the_first : 0 <> S n.
intros A.
change (match 0 with 0 => False | _ => True end).
rewrite A.
exact I.
Qed.

Lemma injective_S x y : S x = S y -> x = y.
intros A.
change (pred (S x) = pred (S y)).
rewrite A.
reflexivity.
Qed.

Goal forall x, S x <> 0.
intros x A.
discriminate A.
Qed.

Goal forall (X : Type)(x : X), Some x <> None.
intros x A.
congruence.
Qed.


Goal forall (X Y : Type)(x x' : X)(y y' : Y), (x,y) = (x',y') -> x = x' /\ y = y'.
intros.
split.
congruence.
congruence.
Qed.

Goal forall (X : Type)(x x' : X)(A A' : list X), cons x A = cons x' A' -> x = x' /\ A = A'.
intros.
split.
congruence.
congruence.
Qed.

Definition leibniz (X : Type)(x y : X) : Prop := forall p : X -> Prop, p x = p y.

Notation "x == y" := (leibniz x y)(at level 70, no associativity).

Definition surjective (X Y : Type)(f: X -> Y):Prop := forall y, exists x, f x = y.

Goal forall n, n + 0 = n.
Proof.
apply (nat_ind (fun n => n + 0 = n)).
reflexivity.
intros n IHn.
simpl.
f_equal.
exact IHn.
Qed.

Goal forall n m, n + S m = S (n + m).
intros n m.
revert n.
apply (nat_ind (fun n => n + S m = S (n + m))); simpl.
reflexivity.
intros n IHn.
f_equal.
exact IHn.
Qed.
