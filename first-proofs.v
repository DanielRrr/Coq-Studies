Theorem a_implies_a : (forall A : Prop, A -> A). 
Proof.
intros A.
intros proof_of_A.
exact proof_of_A.
Print a_implies_a.

(*1 subgoal
______________________________________(1/1)
forall A : Prop, A -> A

1 subgoal
A : Prop
______________________________________(1/1)
A -> A

1 subgoal
A : Prop
proof_of_A : A
______________________________________(1/1)
A

No more subgoals.

a_implies_a is defined

a_implies_a = 
fun (A : Prop) (proof_of_A : A) => proof_of_A
     : forall A : Prop, A -> A

Argument scopes are [type_scope _]*)                                                  


Theorem forward_small : (forall A B : Prop, A -> (A -> B) -> B).
Proof.
intros A.
intros B.
intros proof_of_A.
intros A_implies_B.
pose (proof_of_B := A_implies_B proof_of_A).
exact proof_of_B.
Qed.
Print forward_small.

(*1 subgoal
______________________________________(1/1)
forall A B : Prop,
A -> (A -> B) -> B

1 subgoal
______________________________________(1/1)
forall A B : Prop, A -> (A -> B) -> B

1 subgoal
A : Prop
______________________________________(1/1)
forall B : Prop, A -> (A -> B) -> B

1 subgoal
A, B : Prop
______________________________________(1/1)
A -> (A -> B) -> B

1 subgoal
A, B : Prop
proof_of_A : A
______________________________________(1/1)
(A -> B) -> B

1 subgoal
A, B : Prop
proof_of_A : A
A_implies_B : A -> B
______________________________________(1/1)
B

No more subgoals.

forward_small is defined

*forward_small = 
fun (A B : Prop) (proof_of_A : A)
  (A_implies_B : A -> B) =>
let proof_of_B := A_implies_B proof_of_A in
proof_of_B
     : forall A B : Prop, A -> (A -> B) -> B

Argument scopes are [type_scope type_scope _ _]*)

Theorem backward_large : (forall A B C : Prop, A -> (A -> B) -> (B -> C) -> C).
Proof.
intros A B C.
intros proof_of_A A_implies_B B_implies_C.
refine (B_implies_C _).
refine (A_implies_B _).
exact proof_of_A.
Qed.
Print backward_large.

(*1 subgoal
______________________________________(1/1)
forall A B C : Prop,
A -> (A -> B) -> (B -> C) -> C

1 subgoal
A, B, C : Prop
______________________________________(1/1)
A -> (A -> B) -> (B -> C) -> C

1 subgoal
A, B, C : Prop
proof_of_A : A
A_implies_B : A -> B
B_implies_C : B -> C
______________________________________(1/1)
C

1 subgoal
A, B, C : Prop
proof_of_A : A
A_implies_B : A -> B
B_implies_C : B -> C
______________________________________(1/1)
A

backward_large is defined

backward_large = 
fun (A B C : Prop) (proof_of_A : A)
  (A_implies_B : A -> B) (B_implies_C : B -> C) =>
B_implies_C (A_implies_B proof_of_A)
     : forall A B C : Prop,
       A -> (A -> B) -> (B -> C) -> C

Argument scopes are [type_scope type_scope
  type_scope _ _ _]*)
  

Theorem bigger_than_last : (forall A B C : Prop, A -> (A -> B) -> (A -> B -> C) -> C).
Proof.
intros A B C.
intros proof_of_A A_implies_B A_imp_B_imp_C.
pose (proof_of_B := A_implies_B proof_of_A).
pose (proof_of_C := A_imp_B_imp_C proof_of_A proof_of_B).
exact proof_of_C.
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall A B C : Prop,
A -> (A -> B) -> (A -> B -> C) -> C


1 subgoal
A, B, C : Prop
______________________________________(1/1)
A -> (A -> B) -> (A -> B -> C) -> C


1 subgoal
A, B, C : Prop
proof_of_A : A
A_implies_B : A -> B
A_imp_B_imp_C : A -> B -> C
______________________________________(1/1)
C


1 subgoal
A, B, C : Prop
proof_of_A : A
A_implies_B : A -> B
A_imp_B_imp_C : A -> B -> C
proof_of_B := A_implies_B proof_of_A : B
______________________________________(1/1)
C


1 subgoal
A, B, C : Prop
proof_of_A : A
A_implies_B : A -> B
A_imp_B_imp_C : A -> B -> C
proof_of_B := A_implies_B proof_of_A : B
proof_of_C := A_imp_B_imp_C proof_of_A
                proof_of_B : C
______________________________________(1/1)
C


No more subgoals.


(fun (A B C : Prop) (proof_of_A : A)
   (A_implies_B : A -> B)
   (A_imp_B_imp_C : A -> B -> C) =>
 let proof_of_B := A_implies_B proof_of_A in
 let proof_of_C :=
   A_imp_B_imp_C proof_of_A proof_of_B in
 proof_of_C)
 

bigger_than_last is defined

*)



Theorem inl : (forall A B : Prop, A -> A \/ B).
Proof.
intros A B.
intros proof_of_A.
pose (proof_of_A_or_B := or_introl proof_of_A : A \/ B).
exact proof_of_A_or_B.
Show Proof.
Qed.
(*
1 subgoal
______________________________________(1/1)
forall A B : Prop, A -> A \/ B


1 subgoal
A, B : Prop
______________________________________(1/1)
A -> A \/ B


1 subgoal
A, B : Prop
proof_of_A : A
______________________________________(1/1)
A \/ B


1 subgoal
A, B : Prop
proof_of_A : A
proof_of_A_or_B := (or_introl proof_of_A
                    :
                    A \/ B) : A \/ B
______________________________________(1/1)
A \/ B


No more subgoals.

(fun (A B : Prop) (proof_of_A : A) =>
 let proof_of_A_or_B :=
   or_introl proof_of_A : A \/ B in
 proof_of_A_or_B)

inl is defined

*)


Theorem inr : (forall A B : Prop, B -> A \/ B).
Proof.
intros A B.
intros proof_of_B.
refine (or_intror _).
exact proof_of_B.
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall A B : Prop, B -> A \/ B

1 subgoal
A, B : Prop
______________________________________(1/1)
B -> A \/ B


1 subgoal
A, B : Prop
proof_of_B : B
______________________________________(1/1)
A \/ B


1 subgoal
A, B : Prop
proof_of_B : B
______________________________________(1/1)
B

No more subgoals.

(fun (A B : Prop) (proof_of_B : B) =>
 or_intror proof_of_B)

inr is defined
*)


Theorem or_commutes : (forall A B, A \/ B -> B \/ A).
Proof.
intros A B.
intros A_or_B.
case A_or_B.
intros proof_of_A.
refine (or_intror _).
exact proof_of_A.
intros proof_of_B.
refine (or_introl _).
exact proof_of_B.
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall A B : Prop, A \/ B -> B \/ A


1 subgoal
A, B : Prop
______________________________________(1/1)
A \/ B -> B \/ A

1 subgoal
A, B : Prop
A_or_B : A \/ B
______________________________________(1/1)
B \/ A

2 subgoals
A, B : Prop
A_or_B : A \/ B
______________________________________(1/2)
A -> B \/ A
______________________________________(2/2)
B -> B \/ A


2 subgoals
A, B : Prop
A_or_B : A \/ B
proof_of_A : A
______________________________________(1/2)
B \/ A
______________________________________(2/2)
B -> B \/ A


2 subgoals
A, B : Prop
A_or_B : A \/ B
proof_of_A : A
______________________________________(1/2)
A
______________________________________(2/2)
B -> B \/ A


1 subgoal
A, B : Prop
A_or_B : A \/ B
______________________________________(1/1)
B -> B \/ A


1 subgoal
A, B : Prop
A_or_B : A \/ B
proof_of_B : B
______________________________________(1/1)
B \/ A


1 subgoal
A, B : Prop
A_or_B : A \/ B
proof_of_B : B
______________________________________(1/1)
B

No more subgoals.

(fun (A B : Prop) (A_or_B : A \/ B) =>
 match A_or_B with
 | or_introl proof_of_A => or_intror proof_of_A
 | or_intror proof_of_B => or_introl proof_of_B
 end)

*)


Theorem conj_intr : (forall A B : Prop, A -> B -> A /\ B).
Proof.
intros A B.
intros proof_of_A proof_of_B.
refine (conj _ _).
exact proof_of_A.
exact proof_of_B.
Show Proof.
Qed.


(*
1 subgoal
______________________________________(1/1)
forall A B : Prop, A -> B -> A /\ B

1 subgoal
A, B : Prop
______________________________________(1/1)
A -> B -> A /\ B

1 subgoal
A, B : Prop
proof_of_A : A
proof_of_B : B
______________________________________(1/1)
A /\ B


2 subgoals
A, B : Prop
proof_of_A : A
proof_of_B : B
______________________________________(1/2)
A
______________________________________(2/2)
B

1 subgoal
A, B : Prop
proof_of_A : A
proof_of_B : B
______________________________________(1/1)
B

No more subgoals.

(fun (A B : Prop) (proof_of_A : A) (proof_of_B : B) =>
 conj proof_of_A proof_of_B)
*)


Theorem conj_commutes : (forall A B, A /\ B -> B /\ A).
Proof.
intros A B.
intros A_and_B.
case A_and_B.
intros proof_of_A proof_of_B.
refine (conj _ _).
exact proof_of_B.
exact proof_of_A.
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall A B : Prop,
A /\ B -> B /\ A

1 subgoal
A, B : Prop
______________________________________(1/1)
A /\ B -> B /\ A

1 subgoal
A, B : Prop
A_and_B : A /\ B
______________________________________(1/1)
B /\ A


1 subgoal
A, B : Prop
A_and_B : A /\ B
______________________________________(1/1)
A -> B -> B /\ A

1 subgoal
A, B : Prop
A_and_B : A /\ B
proof_of_A : A
proof_of_B : B
______________________________________(1/1)
B /\ A


2 subgoals
A, B : Prop
A_and_B : A /\ B
proof_of_A : A
proof_of_B : B
______________________________________(1/2)
B
______________________________________(2/2)
A


1 subgoal
A, B : Prop
A_and_B : A /\ B
proof_of_A : A
proof_of_B : B
______________________________________(1/1)
A

No more subgoals.

(fun (A B : Prop) (A_and_B : A /\ B) =>
 match A_and_B with
 | conj proof_of_A proof_of_B =>
     conj proof_of_B proof_of_A
 end)

*)


Theorem exists_forall : (forall P : Set -> Prop, ~(exists x, P x) -> (forall x, ~(P x))).
Proof.
intros P.
intros not_exists_x_Px.
intros x.
unfold not.
intros P_x.
unfold not in not_exists_x_Px.
refine (not_exists_x_Px _).
exact (ex_intro P x P_x).
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall P : Set -> Prop,
~ (exists x : Set, P x) ->
forall x : Set, ~ P x

1 subgoal
P : Set -> Prop
______________________________________(1/1)
~ (exists x : Set, P x) -> forall x : Set, ~ P x

1 subgoal
P : Set -> Prop
not_exists_x_Px : ~ (exists x : Set, P x)
______________________________________(1/1)
forall x : Set, ~ P x

1 subgoal
P : Set -> Prop
not_exists_x_Px : ~ (exists x : Set, P x)
x : Set
______________________________________(1/1)
~ P x

1 subgoal
P : Set -> Prop
not_exists_x_Px : ~ (exists x : Set, P x)
x : Set
______________________________________(1/1)
P x -> False

1 subgoal
P : Set -> Prop
not_exists_x_Px : ~ (exists x : Set, P x)
x : Set
P_x : P x
______________________________________(1/1)
False

1 subgoal
P : Set -> Prop
not_exists_x_Px : (exists x : Set, P x) -> False
x : Set
P_x : P x
______________________________________(1/1)
False


1 subgoal
P : Set -> Prop
not_exists_x_Px : (exists x : Set, P x) -> False
x : Set
P_x : P x
______________________________________(1/1)
exists x0 : Set, P x0


No more subgoals.

(fun (P : Set -> Prop)
   (not_exists_x_Px : ~ (exists x : Set, P x))
   (x : Set) (P_x : P x) =>
 not_exists_x_Px (ex_intro P x P_x))

*)


Theorem eq_sym : (forall x y : Set, x = y -> y = x).
Proof.
intros x y.
intros x_y.
destruct x_y as [].
exact (eq_refl x).
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall x y : Set, x = y -> y = x


1 subgoal
x, y : Set
______________________________________(1/1)
x = y -> y = x

1 subgoal
x, y : Set
x_y : x = y
______________________________________(1/1)
y = x

1 subgoal
x : Set
______________________________________(1/1)
x = x


No more subgoals.


(fun (x y : Set) (x_y : x = y) =>
 match x_y in (_ = y0) return (y0 = x) with
 | eq_refl => eq_refl
 end)

*)


Theorem eq_trans : (forall x y z : Set, x = y -> y = z -> x = z).
Proof.
intros x y z.
intros x_y y_z.
destruct x_y as [].
destruct y_z as [].
exact (eq_refl x).
Show Proof.
Qed.

(*
1 subgoal
______________________________________(1/1)
forall x y z : Set, x = y -> y = z -> x = z

1 subgoal
x, y, z : Set
______________________________________(1/1)
x = y -> y = z -> x = z

1 subgoal
x, y, z : Set
x_y : x = y
y_z : y = z
______________________________________(1/1)
x = z

1 subgoal
x, z : Set
y_z : x = z
______________________________________(1/1)
x = z

1 subgoal
x : Set
______________________________________(1/1)
x = x

(fun (x y z : Set) (x_y : x = y) (y_z : y = z) =>
 match x_y in (_ = y0) return (y0 = z -> x = z) with
 | eq_refl =>
     fun y_z0 : x = z =>
     match y_z0 in (_ = y0) return (x = y0) with
     | eq_refl => eq_refl
     end
 end y_z)
*)

Theorem plus_sym : (forall n m, n + m = m + n).
Proof.
intros n m.
elim n.
elim m.
exact (eq_refl (0 + 0)).
  intros m'.
  intros inductive_hyp_m.
  simpl.
  rewrite <- inductive_hyp_m.
  simpl.
  exact (eq_refl (S m')).
intros n'.
intros inductive_hyp_n.
simpl.
rewrite inductive_hyp_n.
elim m.
  simpl.
  exact (eq_refl (S n')).
  intros m'.
  intros inductive_hyp_m.
  simpl.
  rewrite inductive_hyp_m.
  simpl.
  exact (eq_refl (S (m' + S n'))).
Show Proof.



(*
1 subgoal
______________________________________(1/1)
forall n m : nat, n + m = m + n

1 subgoal
n, m : nat
______________________________________(1/1)
n + m = m + n

2 subgoals
n, m : nat
______________________________________(1/2)
0 + m = m + 0
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0


3 subgoals
n, m : nat
______________________________________(1/3)
0 + 0 = 0 + 0
______________________________________(2/3)
forall n0 : nat,
0 + n0 = n0 + 0 -> 0 + S n0 = S n0 + 0
______________________________________(3/3)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0


2 subgoals
n, m : nat
______________________________________(1/2)
forall n0 : nat,
0 + n0 = n0 + 0 -> 0 + S n0 = S n0 + 0
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0


2 subgoals
n, m, m' : nat
______________________________________(1/2)
0 + m' = m' + 0 -> 0 + S m' = S m' + 0
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0


2 subgoals
n, m, m' : nat
inductive_hyp_m : 0 + m' = m' + 0
______________________________________(1/2)
0 + S m' = S m' + 0
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0

2 subgoals
n, m, m' : nat
inductive_hyp_m : 0 + m' = m' + 0
______________________________________(1/2)
S m' = S (m' + 0)
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0

2 subgoals
n, m, m' : nat
inductive_hyp_m : 0 + m' = m' + 0
______________________________________(1/2)
S m' = S (0 + m')
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0

2 subgoals
n, m, m' : nat
inductive_hyp_m : 0 + m' = m' + 0
______________________________________(1/2)
S m' = S m'
______________________________________(2/2)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0


1 subgoal
n, m : nat
______________________________________(1/1)
forall n0 : nat,
n0 + m = m + n0 -> S n0 + m = m + S n0


1 subgoal
n, m, n' : nat
______________________________________(1/1)
n' + m = m + n' -> S n' + m = m + S n'

1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
______________________________________(1/1)
S n' + m = m + S n'


1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
______________________________________(1/1)
S (n' + m) = m + S n'

1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
______________________________________(1/1)
S (m + n') = m + S n'

2 subgoals
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
______________________________________(1/2)
S (0 + n') = 0 + S n'
______________________________________(2/2)
forall n0 : nat,
S (n0 + n') = n0 + S n' -> S (S n0 + n') = S n0 + S n'

2 subgoals
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
______________________________________(1/2)
S n' = S n'
______________________________________(2/2)
forall n0 : nat,
S (n0 + n') = n0 + S n' -> S (S n0 + n') = S n0 + S n'

1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
______________________________________(1/1)
forall n0 : nat,
S (n0 + n') = n0 + S n' -> S (S n0 + n') = S n0 + S n'

1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
m' : nat
______________________________________(1/1)
S (m' + n') = m' + S n' -> S (S m' + n') = S m' + S n'


1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
m' : nat
inductive_hyp_m : S (m' + n') = m' + S n'
______________________________________(1/1)
S (S m' + n') = S m' + S n'


1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
m' : nat
inductive_hyp_m : S (m' + n') = m' + S n'
______________________________________(1/1)
S (S (m' + n')) = S (m' + S n')

1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
m' : nat
inductive_hyp_m : S (m' + n') = m' + S n'
______________________________________(1/1)
S (m' + S n') = S (m' + S n')

1 subgoal
n, m, n' : nat
inductive_hyp_n : n' + m = m + n'
m' : nat
inductive_hyp_m : S (m' + n') = m' + S n'
______________________________________(1/1)
S (m' + S n') = S (m' + S n')

No more subgoals.

(fun n m : nat =>
 nat_ind (fun n0 : nat => n0 + m = m + n0)
   (nat_ind (fun m0 : nat => 0 + m0 = m0 + 0) eq_refl
      (fun (m' : nat)
         (inductive_hyp_m : 0 + m' = m' + 0) =>
       eq_ind (0 + m') (fun n0 : nat => S m' = S n0)
         eq_refl (m' + 0) inductive_hyp_m) m)
   (fun (n' : nat) (inductive_hyp_n : n' + m = m + n')
    =>
    eq_ind_r (fun n0 : nat => S n0 = m + S n')
      (nat_ind
         (fun m0 : nat => S (m0 + n') = m0 + S n')
         eq_refl
         (fun (m' : nat)
            (inductive_hyp_m : S (m' + n') = m' + S n')
          =>
          eq_ind_r
            (fun n0 : nat => S n0 = S (m' + S n'))
            eq_refl inductive_hyp_m) m)
      inductive_hyp_n) n)

*)
