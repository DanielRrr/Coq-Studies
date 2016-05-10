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

Goal forall p q : nat -> Prop, p 7 -> (forall x, p x -> q x) -> q 7.
Proof.
intros p q A B.
apply B.
exact A.
Qed.

Lemma const : forall X Y, X -> Y -> X.
intros.
apply X0.
Qed.

Goal forall X Y, (forall Z, (X -> Y -> Z) -> Z) -> X.
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

Goal forall (p : bool -> Prop)(x : bool), p true -> p false -> p x.
Proof.
intros.
induction x.
apply H.
apply H0.
Qed.

Goal forall (p : nat -> Prop)(x : nat), p O -> (forall n, p n -> p (S n)) -> p x.
intros.
induction x.
apply H.
apply H0.
apply IHx.
Qed.

Goal forall (X : Type)(p : list X -> Prop)(xs : list X), p nil -> (forall x xs, p xs -> p (cons x xs)) -> p xs.
Proof.
intros.
induction xs.
apply H.
apply H0.
apply IHxs.
Qed.


Goal forall X : Type, (fun x : X => x) = (fun y : X => y).
intros.
reflexivity.
Qed.

Goal forall X Y : Prop, (X -> Y) -> forall x : X, Y.
intros.
apply (H x).
Qed.

Goal forall X Y : Prop, (forall x : X, Y) -> X -> Y.
intros.
apply (H H0).
Qed.

Goal forall X Y : Prop, (X -> Y) = (forall x : X, Y).
intros.
reflexivity.
Qed.

Lemma double_negation : forall X : Prop, X -> ~~X.
intros X x A.
exact (A x).
Qed.

Goal forall X : Prop, ~~X -> (X -> ~X) -> X.
intros X A B.
exfalso.
apply A.
intros x.
exact (B x x).
Qed.

Goal forall X Y : Prop, ~~(((X -> Y) -> X) -> X).
intros.
tauto.
Qed.

Goal forall X Y : Prop, X /\ Y -> Y /\ X.
intros X Y A.
destruct A as [x y].
split.
apply y.
apply x.
Qed.

Goal forall X Y : Prop, X \/ Y -> Y \/ X.
intros X Y A.
destruct A as [x|y].
right. exact x.
left. exact y.
Qed.

Goal forall X Y Z : Prop, X \/ (Y /\ Z) -> (X \/ Y) /\ (X \/ Z).
intros X Y Z [x|[y z]].
split. left. exact x.
left. exact x.
split. right. exact y.
right. exact z.
Qed.

Goal forall X Y Z W : Prop, (X -> Y) \/ (X -> Z) -> (Y -> W) /\ (Z -> W) -> X -> W.
tauto.
Qed.

Goal forall X Y: Prop, X /\ Y -> Y /\ X.
intros X Y [x y].
split.
assumption.
apply x.
Qed.

Goal forall (X : Type)(p q : X -> Prop),(exists x, p x /\ q x) -> exists x, p x.
intros X p q A.
destruct A as [x B].
destruct B as [C _].
exists x.
apply C.
Qed.

Definition diagonal : Prop := forall (X : Type)(p : X -> X -> Prop), ~ exists x, forall y, p x y <-> ~ p y y.

Lemma circuit (X : Prop): ~(X <-> ~X).
tauto.
Qed.

Goal diagonal.
Proof.
intros X p [x A].
apply (@circuit(p x x)).
exact (A x).
Qed.

Goal diagonal.
intros X p [x A].
specialize (A x).
tauto.
Qed.

Axiom doub_neg : forall (X : Prop), ~~X -> X.

Variable X : Type.

Lemma fst_law :
 forall (p : X -> Prop), ~ (forall x:X, ~ p x) -> exists x : X, p x.
Proof.
intros P notall.
apply doub_neg.
intro abs.
apply notall.
intros x H.
apply abs.
exists x.
exact H.
Qed.

Lemma de_morgan_quatifier :
 forall p:X -> Prop, ~ (forall x:X, p x) -> exists x : X, ~ p x.
Proof.
intros P notall.
apply fst_law.
intro all; apply notall.
intro n; apply doub_neg.
apply all.
Qed.

Lemma conj_intro : forall X Y : Prop, X -> Y -> X /\ Y.
tauto.
Defined.

Lemma conj_elim_fst : forall X Y : Prop, X /\ Y -> X.
tauto.
Defined.

Lemma conj_elim_snd : forall X Y : Prop, X /\ Y -> Y.
tauto. Defined.
