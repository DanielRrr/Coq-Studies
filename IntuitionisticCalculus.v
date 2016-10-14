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

Theorem disj_assoc2 : forall A B C : Prop, (A \/ B) \/ C <-> A \/ (B \/ C).
Proof.
intros.
split.
apply disj_assoc.
apply disj_assoc1.
Qed.
