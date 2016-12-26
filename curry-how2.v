Require Import Classical.

Theorem id: forall A : Prop, A -> A.
Proof.
intros.
apply H.
Qed.

Theorem const : forall A B : Prop, A -> B -> A.
Proof.
intros.
apply H.
Qed.

Theorem s_comb : forall A B C : Prop, (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
intros.
apply H.
apply H1.
apply H0.
apply H1.
Qed.

Theorem b_comb1 : forall A B C : Prop, (A -> B) -> (B -> C) -> A -> C.
Proof.
intros.
apply H0.
apply H.
apply H1.
Qed.

Theorem b_comb2 : forall A B C : Prop, (B -> C) -> (A -> B) -> A -> C.
Proof.
intros.
apply H.
apply H0.
apply H1.
Qed.

Theorem excluded_middle : forall A : Prop, (~~ A) -> A.
Proof. 
tauto.
Qed.

Theorem distr_next : forall A B C D : Prop, (A -> C) /\ (B -> D) -> A /\ B -> C /\ D.
Proof.
intros.
split.
apply H.
apply H0.
apply H.
apply H0.
Qed.

Theorem neg_property : forall A : Prop, A -> ~~A.
Proof.
intros.
intro H0.
apply H0.
apply H.
Qed.

Theorem split : forall A B C : Prop, (A -> B -> C) -> (B -> A -> C).
Proof.
intros.
apply H.
apply H1.
apply H0.
Qed.

Theorem pair_intro : forall A B : Prop, (A -> (B -> (A /\ B))).
Proof.
intros.
split.
apply H.
apply H0.
Qed.

Theorem fst : forall A B : Prop, (A /\ B) -> A.
Proof.
intros.
apply H.
Qed.

Theorem snd : forall A B : Prop, (A /\ B) -> B.
Proof.
intros.
apply H.
Qed.

Theorem curry : forall A B C : Prop, (A /\ B) -> C -> (A -> (B -> C)).
Proof.
intros.
apply H0.
Qed.

Theorem uncurry : forall A B C : Prop, (A -> (B -> C)) -> ((A /\ B) -> C).
Proof.
intros.
apply H.
apply H0.
apply H0.
Qed.

Theorem uniProd : forall A B C : Prop, (A -> B) -> (A -> C) -> A -> (B /\ C).
Proof.
intros.
split.
apply H.
apply H1.
apply H0.
apply H1.
Qed.

Theorem prod2 : forall A B C D : Prop, (A -> B) -> (D -> C) -> (A /\ D) -> (B /\ C).
Proof.
intros.
split.
apply H.
apply H1.
apply H0.
apply H1.
Qed.

Theorem trans2 : forall A B C : Prop, (A -> B) /\ (B -> C) -> A -> C.
Proof.
intros.
apply H.
apply H.
apply H0.
Qed.

Theorem con_com : forall A B : Prop, (A /\ B) -> (B /\ A).
Proof.
intros.
split.
apply H.
apply H.
Qed.

Theorem con_assoc : forall A B C: Prop, (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
intros.
split.
apply H.
split.
apply H.
apply H.
Qed.

Theorem con_assoc1 : forall A B C : Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
intros.
split.
split.
apply H.
apply H.
apply H.
Qed.

Theorem con_assoc2 : forall A B C : Prop, A /\ (B /\ C) <-> (A /\ B) /\ C.
Proof.
intros.
split.
apply con_assoc1.
apply con_assoc.
Qed.


Theorem disj_intro_left : forall A B : Prop, A -> A \/ B.
Proof.
intros.
left.
apply H.
Qed.

Theorem disj_intro_right : forall A B : Prop, B -> A \/ B.
Proof.
intros.
right.
apply H.
Qed.

Theorem disj_elim : forall A B C : Prop, (A -> C) -> (B -> C) -> A \/ B -> C.
Proof.
intros.
destruct H1.
apply H.
apply H1.
apply H0.
apply H1.
Qed.

Theorem disj_assoc : forall A B C : Prop, (A \/ B) \/ C -> A \/ (B \/ C).
Proof.
intros.
tauto.
Qed.

Theorem disj_assoc1 : forall A B C : Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
intros.
tauto.
Qed.

Theorem disj_assoc2 : forall A B C : Prop, (A \/ B) \/ C <-> A \/ (B \/C).
Proof.
intros.
split.
apply disj_assoc.
apply disj_assoc1.
Qed.

Theorem monotone : forall A B C : Prop,  (A -> B) -> ((A /\ C) -> (B /\ C)).
Proof.
intros.
split.
apply H.
apply H0.
apply H0.
Qed.


Theorem first_order1: forall (X:Type) (P Q : X -> Prop), (forall x : X, P x /\ Q x) -> (forall x : X, P x) /\ (forall x : X, P x).
Proof.
intros.
split.
intro x.
apply (H x).
apply H.
Qed.

Theorem trans_2 : forall(X:Type) (P Q R: X -> Prop),
(forall x : X, P x -> Q x) /\ (forall x : X, Q x -> R x) -> (forall x : X, P x -> R x).
Proof.
intros.
apply H.
apply H.
apply H0.
Qed.

Inductive ex (X:Type) (P : X -> Prop) : Prop := ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

Theorem dist_exists_or : forall(X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
split.
intros.
inversion H.
inversion H0.
left.
exists witness.
apply H1.
right.
exists witness.
apply H1.
intros.
inversion H.
inversion H0.
exists witness.
left.
apply H1.
inversion H0.
exists witness.
right.
apply H1.
Qed.

Theorem first_order_2 : forall (X: Type) (p q : X -> Prop), (exists x, p x /\ q x) -> exists x, p x.
Proof.
intros.
destruct H as [x B].
destruct B as [C _].
exists x.
apply C.
Qed.

Theorem first_order_3 : forall (P Q : Type -> Prop) (A : Type), P A -> (forall x : Type, P x -> Q x) -> Q A.
Proof.
intros.
apply H0.
apply H.
Qed.

Theorem ex7 : forall (a b : Type) (p : Type -> Prop), p a \/ p b -> exists x : Type, p x.
Proof.
intros.
elim H.
exists a.
apply H0.
exists b.
apply H0.
Qed.

Theorem ex8: forall (A : Set) (R : A -> A -> Prop), (forall x y z : A, R x y /\ R y z -> R x z) ->
(forall x y : A, R x y -> R y x) ->
forall x : A, (exists y : A, R x y) -> R x x.
Proof.
intros A R Trans Sym a h.
elim h.
intros b H.
apply Trans with b.
split.
apply H.
apply Sym.
assumption.
Qed.
