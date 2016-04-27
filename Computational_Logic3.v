Lemma eq_sym : forall (X : Type)(x y : X), x = y -> y = x.
intros X x y A.
rewrite A.
reflexivity.
Qed.

Lemma modus_ponens : forall X Y : Prop, X -> (X -> Y) -> Y.
intros X Y x A.
exact (A x).
Qed.

Lemma barbara : forall X Y Z : Prop, (X -> Y) -> (Y -> Z) -> (X -> Z).
intros X Y Z A B x.
exact (B (A x)).
Qed.


Lemma eq_trans : forall (X : Type)(x y z : X), x = y -> y = z -> x = z.
intros.
transitivity y.
assumption.
apply H0.
Qed.

Lemma const : forall X Y, X -> Y -> X.
intros.
apply X0.
Qed.

Goal forall X Y, (forall Z, (X -> Y -> Z) ->
 Z) -> X.
intros X Y Z0.
apply Z0.
apply const.
Qed.

Lemma const' : forall X Y, X -> Y -> Y.
intros.
apply X1.
Qed.


Goal forall X Y, (forall Z, (X -> Y -> Z) -> Z) -> Y.
intros.
apply X0.
apply const'.
Qed.

Lemma leibniz_equality : forall (X : Type)(x y : X),(forall p : X -> Prop, p x -> p y) -> x = y.
intros.
apply (H (fun z => x = z)).
reflexivity.
Qed.

Goal forall X : Type, (fun x : X => x) = (fun y : X => y).
intros.
reflexivity.
Qed.

Goal forall X : Prop, X -> ~~X.
intros X x A.
exact (A x).
Qed.
