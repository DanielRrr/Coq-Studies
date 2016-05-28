
Require Export Logic.


Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition even (n:nat) : Prop := 
  evenb n = true.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Definition double n := n * 2.

Theorem double_even : forall n,
  ev (double n).
Proof.
induction n.
apply ev_0.
simpl.
apply ev_SS.
apply IHn.
Qed.


Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


Theorem three_is_beautiful: beautiful 3.
Proof.
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   apply b_3.
   apply b_5.
Qed.


Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.

Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
intros.
simpl.
apply b_sum.
apply H.
apply b_sum.
apply H.
apply b_0.
Qed.

Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
intros.
induction m.
simpl.
apply b_0.
apply b_sum.
apply H.
apply IHm.
Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
intros.
apply g_plus5 with (n:= (8 + n)).
apply g_plus3 with (n:= (5 + n)).
apply g_plus5.
apply H.
Qed.

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
intros.
induction H.
apply b_0.
apply b_sum.
apply b_3.
apply IHgorgeous.
apply b_sum.
apply b_5.
apply IHgorgeous.
Qed.


Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
intros.
induction H.
simpl.
apply H0.
apply g_plus3.
apply IHgorgeous.
apply g_plus5.
apply IHgorgeous.
Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
intros.
induction H.
apply g_0.
apply g_plus3 with (n := 0).
apply g_0.
apply g_plus5 with (n := 0).
apply g_0.
apply gorgeous_sum.
apply IHbeautiful1.
apply IHbeautiful2.
Qed.

Lemma plus_0 : forall n : nat, n + 0 = n.
Proof.
induction n.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.


Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
intros n H. 
simpl. 
induction H.
simpl.
apply g_0.
apply g_plus3.
apply gorgeous_sum.
simpl.
apply H.
apply g_plus3 with (n := (n + 0)).
rewrite -> plus_0.
apply H.
apply gorgeous_sum.
apply g_plus5.
apply H.
apply gorgeous_sum.
apply g_plus5.
apply H.
apply g_0.
Qed.


Theorem ev__even : forall n,
  ev n -> even n.
Proof.
intros n E. 
induction E as [| n' E'].
unfold even.
reflexivity.
unfold even. 
apply IHE'.  
Qed.

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
intros.
induction H.
simpl.
apply H0.
simpl.
apply ev_SS.
apply IHev.
Qed.


Theorem ev_minus2: forall n,  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
simpl. apply ev_0. 
simpl. apply E'.  Qed.

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.


Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
intros.
inversion H.
inversion H1.
apply H3.
Qed.

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
intros.
inversion H.
inversion H1.
inversion H3.
Qed.



Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m E En. generalize dependent E.
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

    
Module LeModule.  




Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).


Theorem test_le1 :
  3 <= 3.
Proof.
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof. 
  intros H. inversion H. inversion H2.  Qed.

End LeModule.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).


Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
intros m n o H1 H2.
generalize dependent H1.
generalize dependent m.
induction H2.
intros.
apply H1.
intros.
apply le_S.
apply IHle.
apply H1.
Qed.



Theorem O_le_n : forall n,
  0 <= n.
Proof.
intros.
induction n.
apply le_n.
apply le_S.
apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
intros.
induction H.
apply le_n.
apply le_S.
apply IHle.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
intros.
inversion H.
apply le_n.
apply le_trans with (n:= S n).
Theorem n_le_Sn : forall n, n <= S n.
intros.
apply le_S.
apply le_n.
Qed.
apply n_le_Sn.
apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
intros.
induction a.
simpl.
apply O_le_n.
simpl.
apply n_le_m__Sn_le_Sm.
apply IHa.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
Admitted.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
intros.
induction H.
simpl.
apply le_S.
apply le_n.
inversion H.
apply le_S.
apply le_S.
apply le_n.
apply le_S.
apply le_S.
apply le_S.
apply H0.
Qed.

Fixpoint ble_nat (n m : nat) {struct n} : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
intros.
generalize dependent n.
induction m.
destruct n.
simpl.
intros.
apply le_n.
simpl.
intros.
inversion H.
intros.
destruct n.
apply O_le_n.
apply n_le_m__Sn_le_Sm.
apply IHm.
simpl in H.
apply H.
Qed.

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
intros. 
generalize dependent n. 
induction m.
destruct n.
simpl. 
intros. 
reflexivity.
intros. 
inversion H.
intros. 
destruct n.
simpl. 
reflexivity.
simpl. 
apply IHm.
apply Sn_le_Sm__n_le_m.
apply H.
Qed.

Theorem ble_nat_true_trans : forall n m o,
  ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.                               
Proof.
intros.
apply le_ble_nat.
apply le_trans with ( n:= m ).
apply ble_nat_true.
apply H.
apply ble_nat_true.
apply H0.
Qed.



Module R.


Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

End R.

Theorem plus_2_2_is_4 : 
  2 + 2 = 4.
Proof. simpl. reflexivity.  Qed.


Definition between (n m o: nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.
  
Definition teen : nat->Prop := between 13 19.


Definition true_for_zero (P:nat->Prop) : Prop :=
  P 0.

Definition true_for_all_numbers (P:nat->Prop) : Prop :=
  forall n, P n.

Definition preserved_by_S (P:nat->Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition natural_number_induction_valid : Prop :=
  forall (P:nat->Prop),
    true_for_zero P ->
    preserved_by_S P -> 
    true_for_all_numbers P. 


Inductive ex (X:Type) (P : X -> Prop) : Prop := ex_intro : forall (witness:X), P witness -> ex X P.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.


Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity. Qed.


Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity. Qed.

Theorem exists_example_2 : forall n,(exists m, n = 4 + m) -> (exists o, n = 2 + o).
Proof.
intros.
inversion H as [m Hm].
exists (2 + m).
apply Hm.
Qed.


Lemma exists_example_3 : exists (n:nat), even n /\ beautiful n.
Proof.
exists 8.
split.
unfold even.
simpl.
reflexivity.
apply b_sum with (n := 3) (m := 5).
apply b_3.
apply b_5.
Qed.


Theorem dist_not_exists : forall(X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
intros.
unfold not.
intros.
inversion H0.
apply H1.
apply H with (x := witness).
Qed.

Definition excluded_middle := forall P:Prop, 
  P \/ ~P.

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
unfold not.
intros.
unfold excluded_middle in H.
assert ((P x) \/ (P x -> False)) as HP.
apply H with (P := P x).
inversion HP.
apply H1.
Theorem ex_falso_quodlibet: forall P : Prop, False -> P.
intros.
inversion H.
Qed.
apply ex_falso_quodlibet.
apply H0.
exists x.
apply H1.
Qed.


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


Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.


Theorem eq_nat_dec : forall n m : nat, {n = m} + {~(n = m)}.
Proof.  
  intros n.
  induction n as [|n'].
    intros m.
    destruct m as [|m'].
      left. reflexivity.
      right. intros contra. inversion contra.
    intros m.
    destruct m as [|m'].
      right. intros contra. inversion contra.
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal. apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
