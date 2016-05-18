Lemma silly_implication : (1 + 1) = 2 -> 0 * 3 = 0.
Proof. intros H. simpl. reflexivity. Qed.


Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem and_example : (0 = 0) /\ (4 = mult 2 2).
Proof.

apply conj.
reflexivity.
simpl.
reflexivity.
Qed.

Theorem proj1 : forall P Q : Prop, P /\ Q -> P.
Proof.
intros.
destruct H.
apply H.
Qed.

Theorem proj2 : forall P Q : Prop, P /\ Q -> Q.
Proof.
intros.
destruct H.
apply H0.
Qed.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
intros.
split.
destruct H.
apply H0.
destruct H.
apply H.
Qed.


Theorem and_assoc : forall P Q R : Prop, P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
intros.
split.
destruct H.
split.
apply H.
destruct H0.
apply H0.
destruct H as [H1 H2].
destruct H2.
apply H0.
Qed.


Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.


Theorem iff_implies : forall P Q : Prop, (P <-> Q) -> P -> Q.
Proof.
intros P Q H.
destruct H.
apply H.
Qed.


Theorem iff_sym : forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
intros.
destruct H.
split.
apply H0.
apply H.
Qed.

Theorem iff_refl : forall P : Prop, P <-> P.
Proof.
intros.
split.
intros H1.
apply H1.
intros H2.
apply H2.
Qed.

Theorem conj_trans : forall P Q R : Prop, P /\ Q -> Q /\ R -> P /\ R.
Proof.
intros.
split.
destruct H.
apply H.
destruct H0.
apply H1.
Qed.

Theorem iff_trans : forall P Q R : Prop, (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
intros P Q R HEPQ HEQR.
inversion  HEPQ as [HPQ HQP].
inversion HEQR as [HQR HRQ].
split.
intros HP. 
apply HQR. 
apply HPQ. 
apply HP.
intros HR. 
apply HQP. 
apply HRQ. 
apply HR.
Qed.

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
intros.
destruct H as [H1 | H2].
apply or_intror.
apply H1.
apply or_introl.
apply H2.
Qed.


Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
intros P Q R H.
inversion H as [ HP | [ HQ HR ] ].
split.
left. apply HP.
left. apply HP.
split.
right.
apply HQ.
right.
apply HR.
Qed.

Theorem or_distributes_over_and_2 : forall P Q R : Prop, (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
intros P Q R H.
inversion H as [HPQ HPR].
inversion HPQ as [ HP | HQ ].
left.
apply HP.
inversion HPR as [HP | HR].
left.
apply HP.
right.
apply conj.
apply HQ.
apply HR.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop, P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
split.
apply or_distributes_over_and_1.
apply or_distributes_over_and_2.
Qed.


Theorem andb_prop : forall b c, andb b c = true -> b = true /\ c = true.
Proof.
intros b c H.
destruct b.
destruct c.
apply conj. reflexivity. reflexivity.
inversion H.
inversion H. 
Qed.


Theorem andb_true_intro : forall b c, b = true /\ c = true -> andb b c = true.
Proof.
intros b c H.
destruct b.
destruct c.
simpl.
reflexivity.
simpl.
inversion H.
apply H1.
destruct c.
simpl.
inversion H.
apply H0.
simpl.
inversion H.
apply H0.
Qed.


Theorem andb_false : forall b c, andb b c = false -> b = false \/ c = false.
Proof.
intros b c H.
destruct b. destruct c.
left.
inversion H.
right.
reflexivity.
left.
reflexivity.
Qed.


Theorem orb_prop : forall b c, orb b c = true -> b = true \/ c = true.
Proof.
intros b c H.
destruct b.
left.
reflexivity.
destruct c.
right.
reflexivity.
simpl.
left.
apply H.
Qed.


Theorem orb_false_elim : forall b c, orb b c = false -> b = false /\ c = false.
Proof.
intros b c H.
destruct b.
split.
apply H.
destruct c.
apply H.
reflexivity.
split.
reflexivity.
destruct c.
apply H.
reflexivity.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense : False -> 2 + 2 = 5.
Proof.
intros.
inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop, (P /\ ~P) -> Q.
Proof.
intros.
destruct H.
unfold not in H0.
apply H0 in H.
inversion H.
Qed.

Theorem double_neg : forall P : Prop, P -> ~~P.
Proof.
intros.
unfold not.
intros.
apply H0 in H.
apply H.
Qed.

Theorem contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
intros P Q H. unfold not. intros notQ Pass.
apply notQ. apply H. apply Pass.
Qed.


Theorem peirce : forall P Q: Prop, 
  ((P -> Q) -> P) -> P.
intros.
apply H.


Theorem first_eq : forall P Q : Prop, ((P -> Q) -> P) -> P -> ~~P -> P.
Proof.
intros.
apply H0.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop), ~~(P \/ ~ P).
Proof.
unfold not.
intros P f.
apply f.
right.
intro p.
apply f.
left.
apply p.
Defined.
