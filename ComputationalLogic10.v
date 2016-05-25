Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Theorem ev_4 : ev 4.
Proof. 
apply ev_SS. 
apply ev_SS. 
apply ev_0. 
Qed.


Theorem ev_4' : ev 4.
Proof. 
apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
intros n.
simpl.
intros Hn.
apply ev_SS.
apply ev_SS.
apply Hn.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition double n := n * 2.

Theorem ev_double : forall n,
  ev (double n).
Proof.
induction n  as [| n'].
apply ev_0.
simpl.
apply ev_SS.
apply IHn'.
Qed.

Theorem evenb_minus2: forall n,
  evenb n = true -> evenb (pred (pred n)) = true.
Proof.
intros [| [| n ]].
reflexivity.
intros H.
inversion H.
simpl.
intros H.
apply H.
Qed.

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
intros n H.
inversion H.
simpl.
apply ev_0.
simpl.
apply H0.
Qed.


Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
intros n H.
inversion H.
apply H1.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
intros H.
inversion H.
Qed.


Theorem SSSSev__even : forall n, ev (S (S (S (S n)))) -> ev n.
Proof.
intros n H.
inversion H.
inversion H1.
apply H3.
Qed.


Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
intros absurd.
inversion absurd.
inversion H0.
inversion H2.
Qed.


Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
    exists 0. reflexivity.
    destruct IH as [k' Hk'].
    rewrite Hk'. exists(S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
intros.
split.
apply ev_even.
intros [k Hk].
rewrite Hk.
apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
intros.
induction H as [| h].
simpl.
apply H0.
simpl.
apply ev_SS.
apply IHev.
Qed.


Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
intros n.
split.
Abort.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
intros n m E En. 
generalize dependent E.
induction En.
simpl. 
intros. 
apply E.
simpl. 
intros.
inversion E.
apply IHEn in H0.
apply H0.
Qed.
