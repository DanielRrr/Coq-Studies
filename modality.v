Parameter world : Type.

Parameter R : world -> world -> Prop.

Definition Proposition : Type := world -> Prop.

Definition holds_in (w : world) (phi : Proposition) : Prop := phi w.

Notation "w ||- phi" := (holds_in w phi) (at level 30).

Definition Top : Proposition := fun w => True.

Definition Bot : Proposition := fun w => False.

Definition Neg (phi : Proposition) : Proposition := fun w => ~ (w ||- phi).

Notation "! phi" := (Neg phi) (at level 16).

Definition And (phi psi : Proposition) : Proposition := fun w => (w ||- phi) /\ (w ||- psi).

Notation "phi && psi"  := (And phi psi).

Definition Or (phi psi : Proposition) : Proposition := fun w => (w ||- phi) \/ (w ||- psi).

Notation "phi || psi"  := (Or phi psi).

Definition Imply (phi psi : Proposition) : Proposition := fun w => (w ||- phi) -> (w ||- psi).

Notation "phi --> psi"  := (Imply phi psi) (at level 20, right associativity).

Definition Box (phi : Proposition) : Proposition := fun w => forall w', R w w' -> (w' ||- phi).

Notation "[] phi" := (Box phi) (at level 15).

Definition Diamond (phi : Proposition) : Proposition := fun w => exists w', R w w' /\ (w' ||- phi).
 
Notation "<> phi" := (Diamond phi) (at level 15).

Section Example.

Parameter p q : Proposition.

Parameter x1 x2 x3 x4 x5 x6 : world.

Hypothesis Kripke_example: 
                                     R x1 x2 /\ R x1 x3 /\ R x2 x3 /\
                                     R x3 x2 /\ R x2 x2 /\ R x4 x5 /\
                                     R x5 x4 /\ R x5 x6 /\
                                      (x1 ||- ! p) /\ (x1 ||- q) /\
                                      (x1 ||- p) /\ (x2 ||- q) /\
                                      (x3 ||- p) /\ (x3 ||- ! q) /\
                                      (x4 ||- ! p) /\ (x4 ||- q) /\
                                      (x5 ||- ! p) /\ (x5 ||- ! q) /\
                                      (x6 ||-  p) /\ (x6 ||- ! q).

Lemma Kripke_ex_2 : x1 ||- <> q.
Proof.
unfold holds_in, Diamond.
exists x2.
tauto.
Qed.

End Example.

Definition valid (phi : Proposition) : Prop := forall w, w ||- phi.
Notation "|= phi" := (valid phi) (at level 30).

Theorem DnnB : forall phi, |= <> (! phi) --> ! ([] phi).
Proof.
intros.
do 3 intro.
destruct H.
unfold holds_in, Box in H0.
simpl.
destruct H.
apply H0 in H.
contradiction H.
Qed.

Lemma boxConj : forall phi psi, |= ([] (phi && psi) --> (([] phi) && ([] psi))).
Proof.
intros.
intro.
intro.
unfold holds_in, And.
split.
intro.
intro.
apply H in H0.
destruct H0.
apply H0.
intro.
intro.
apply H in H0.
destruct H0.
apply H1.
Qed.

Lemma diaDisj : forall phi psi, |= (<> (phi || psi) --> ((<> phi) || (<> psi))).
Proof.
intros.
intro.
intro.
destruct H.
destruct H.
unfold holds_in, Or.
unfold holds_in, Or in H0.
destruct H0.
left.
exists x.
auto.
right.
exists x.
auto.
Qed.

Theorem Kripke_this_charming_man : forall phi psi, |= ([] (phi --> psi)) --> [] phi --> [] psi.
Proof.
intros.
do 5 intro.
apply H.
apply H1.
trivial.
auto.
Qed.

Theorem fst : (forall w, R w w) <-> forall phi, |= [] phi --> phi.
Proof.
intros.
split.
repeat intro.
auto.
repeat intro.
apply H.
intro.
intro.
unfold holds_in.
apply H0.
Qed.

Theorem snd : (forall w1 w2 w3, R w1 w2 -> R w2 w3 -> R w1 w3) <-> forall phi, |= [] phi --> [] [] phi.
Proof.
intros.
split.
repeat intro.
apply H0.
apply H with w'.
apply H1.
apply H2.
intros.
unfold Box in H.
unfold Imply in H.
unfold holds_in in H.
apply H with w1 w2.
intro w'.
auto.
apply H0.
apply H1.
Qed.
