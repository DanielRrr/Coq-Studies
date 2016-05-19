Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.


Class PreOrder {A} (R : relation A) :=
  { PreOrder_Reflexive : Reflexive R | 2 ;
    PreOrder_Transitive : Transitive R | 2 }.

Global Existing Instance PreOrder_Reflexive.
Global Existing Instance PreOrder_Transitive.

Arguments reflexivity {A R _} / _.
Arguments symmetry {A R _} / _ _ _.
Arguments transitivity {A R _} / {_ _ _} _ _.


Ltac symmetry :=
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let x := match goal with |- ?R ?x ?y => constr:(x) end in
  let y := match goal with |- ?R ?x ?y => constr:(y) end in
  let pre_proof_term_head := constr:(@symmetry _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head y x _); change (R y x).

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Tactic Notation "etransitivity" := etransitivity _.

Ltac transitivity x := etransitivity x.


Notation Type0 := Set.


Notation idmap := (fun x => x).

Delimit Scope equiv_scope with equiv.
Delimit Scope function_scope with function.
Delimit Scope path_scope with path.
Delimit Scope fibration_scope with fibration.
Delimit Scope trunc_scope with trunc.

Open Scope trunc_scope.
Open Scope equiv_scope.
Open Scope path_scope.
Open Scope fibration_scope.
Open Scope nat_scope.
Open Scope function_scope.
Open Scope type_scope.
Open Scope core_scope.


Definition const {A B} (b : B) := fun x : A => b.


Notation "( x ; y )" := (existT _ x y) : fibration_scope.


Bind Scope fibration_scope with sigT.


Notation pr1 := projT1.
Notation pr2 := projT2.

Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.

Scheme sig_rect := Induction for sig Sort Type.
Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.


Arguments exist {A}%type P%type _ _.
Arguments proj1_sig {A P} _ / .
Arguments proj2_sig {A P} _ / .

Inductive sig2 (A:Type) (P Q:A -> Type) : Type :=
    exist2 (x : A) (_ : P x) (_ : Q x).


Notation sigT := sig (only parsing).
Notation existT := exist (only parsing).
Notation sigT_rect := sig_rect (only parsing).
Notation sigT_rec := sig_rect (only parsing).
Notation sigT_ind := sig_rect (only parsing).
Notation sigT2 := sig2 (only parsing).
Notation existT2 := exist2 (only parsing).
Notation sigT2_rect := sig2_rect (only parsing).
Notation sigT2_rec := sig2_rect (only parsing).
Notation sigT2_ind := sig2_rect (only parsing).

Notation ex_intro := existT (only parsing).

Notation "{ x | P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x | P & Q }" := (sigT2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A | P }" := (sigT (A := A) (fun x => P)) : type_scope.
Notation "{ x : A | P & Q }" := (sigT2 (fun x : A => P) (fun x : A => Q)) :
  type_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (sigT2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (sigT2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2' '/ ' x : t , '/ ' '[' p & '/' q ']' ']'")
  : type_scope.


Notation "{ x : A & P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A & P & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.

Add Printing Let sig.
Add Printing Let sig2.

Arguments sig (A P)%type.
Arguments sig2 (A P Q)%type.

Notation compose := (fun g f x => g (f x)).

Notation "g 'o' f" := (compose g%function f%function) (at level 40, left associativity) : function_scope.


Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Arguments None [A].


Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.


Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Notation "A \/ B" := (A + B)%type (only parsing) : type_scope.
Notation or := sum (only parsing).


Record prod (A B : Type) := pair { fst : A ; snd : B }.

Scheme prod_rect := Induction for prod Sort Type.

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (prod A B) (only parsing) : type_scope.
Notation and := prod (only parsing).
Notation conj := pair (only parsing).

Hint Resolve pair inl inr : core.

Definition prod_curry (A B C : Type) (f : A -> B -> C)
  (p : prod A B) : C := f (fst p) (snd p).


Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.


Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.


Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.
Arguments S _.

Open Scope nat_scope.


Definition iff_compose {A B C : Type} (g : B <-> C) (f : A <-> B): A <-> C := (fst g o fst f , snd f o snd g).


Definition iff_inverse {A B : Type} : (A <-> B) -> (B <-> A) := fun f => (snd f , fst f).


Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).

Global Arguments composeD {A B C}%type_scope (g f)%function_scope x.

Hint Unfold composeD.

Notation "g 'oD' f" := (composeD g f) (at level 40, left associativity) : function_scope.


(*The groupoid structure of identity types.*)

Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.

Arguments paths_ind [A] a P f y p.
Arguments paths_rec [A] a P f y p.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.

Lemma paths_rew A a y P (X : P a) (H : a = y :> A) : P y.
Proof.
rewrite <- H.
apply X.
Qed.


Lemma paths_rew_r A a y P (X : P y) (H : a = y :> A) : P a.
Proof.
rewrite -> H.
apply X.
Qed.


Global Instance reflexive_paths {A} : Reflexive (@paths A) | 0 := @idpath A.
Arguments reflexive_paths / .

Bind Scope path_scope with paths.

Local Open Scope path_scope.

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x.
rewrite -> p.
reflexivity.
Qed.

Arguments inverse {A x y} p : simpl nomatch.

Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0 := @inverse A.
Arguments symmetric_paths / .


Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
Proof.
induction p.
rewrite q.
reflexivity.
Qed.


Arguments concat {A x y z} p q : simpl nomatch.

Global Instance transitive_paths {A} : Transitive (@paths A) | 0 := @concat A.
Arguments transitive_paths / .


Notation "1" := idpath : path_scope.


Notation "p @ q" := (concat p%path q%path) (at level 20) : path_scope.

Notation "p ^" := (inverse p%path) (at level 3, format "p '^'") : path_scope.


Notation "p @' q" := (concat p q) (at level 21, left associativity,
  format "'[v' p '/' '@'' q ']'") : long_path_scope.


Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y.
Proof.
rewrite <- p.
apply u.
Qed.

Arguments transport {A}%type_scope P%function_scope {x y} p%path_scope u : simpl nomatch.


Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.

Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y.
Proof.
rewrite <- p.
reflexivity.
Qed.

Global Arguments ap {A B}%type_scope f%function_scope {x y} p%path_scope.


Definition pointwise_paths {A} {P:A -> Type} (f g : forall x : A, P x) := forall x:A, f x = g x.

Global Arguments pointwise_paths {A}%type_scope {P} (f g)%function_scope.

Hint Unfold pointwise_paths : typeclass_instances.

Definition pointwise_paths_refl {A} {P:A -> Type} (f : forall x : A, P x) := forall x:A, f x = f x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Require Import Setoid.

Definition apD10 {A} {B:A -> Type} {f g : forall x, B x} (h:f=g)
  : f == g.
Proof.
rewrite <- h.
intros x.
reflexivity.
Qed.

Global Arguments apD10 {A%type_scope B} {f g}%function_scope h%path_scope _.

Definition ap10 {A B} {f g:A -> B} (h:f=g) : f == g
  := apD10 h.

Global Arguments ap10 {A B}%type_scope {f g}%function_scope h%path_scope _.


Notation happly := ap10 (only parsing).

Definition ap11 {A B} {f g:A -> B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.

Global Arguments ap11 {A B}%type_scope {f g}%function_scope h%path_scope {x y} p%path_scope.

Arguments ap {A B} f {x y} p : simpl nomatch.

Ltac path_induction :=
intros; repeat progress (
match goal with
 | [p: _ = _ |-_] => induction p
 | _ => idtac
 end
); auto.

Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Global Arguments Sect {A B}%type_scope (s r)%function_scope.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B}%type_scope f%function_scope {_} _.
Arguments eissect {A B}%type_scope f%function_scope {_} _.
Arguments eisadj {A B}%type_scope f%function_scope {_} _.
Arguments IsEquiv {A B}%type_scope f%function_scope.


Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Arguments equiv_fun {A B} _ _.
Arguments equiv_isequiv {A B} _.

Bind Scope equiv_scope with Equiv.

Notation "A <~> B" := (Equiv A B) (at level 85) : type_scope.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : function_scope.


Definition ap10_equiv {A B : Type} {f g : A <~> B} (h : f = g) : f == g.
Proof.
path_induction.
intros x.
reflexivity.
Qed.


Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.


Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.


Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Notation "n .+1" := (S n) (at level 2, left associativity, format "n .+1") : nat_scope.
Notation "n .+2" := (n.+1.+1)%trunc (at level 2, left associativity, format "n .+2") : trunc_scope.
Notation "n .+2" := (n.+1.+1)%nat (at level 2, left associativity, format "n .+2") : nat_scope.
Notation "n .+3" := (n.+1.+2)%trunc (at level 2, left associativity, format "n .+3") : trunc_scope.
Notation "n .+3" := (n.+1.+2)%nat (at level 2, left associativity, format "n .+3") : nat_scope.
Notation "n .+4" := (n.+1.+3)%trunc (at level 2, left associativity, format "n .+4") : trunc_scope.
Notation "n .+4" := (n.+1.+3)%nat (at level 2, left associativity, format "n .+4") : nat_scope.
Notation "n .+5" := (n.+1.+4)%trunc (at level 2, left associativity, format "n .+5") : trunc_scope.
Notation "n .+5" := (n.+1.+4)%nat (at level 2, left associativity, format "n .+5") : nat_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.
Notation "0" := (-1.+1) : trunc_scope.
Notation "1" := (0.+1) : trunc_scope.
Notation "2" := (1.+1) : trunc_scope.



Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.


Typeclasses Opaque IsTrunc. 
Arguments IsTrunc : simpl never. 
Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
: IsTrunc n (x = y)
  := H x y. 


Notation Contr := (IsTrunc -2).
Notation IsHProp := (IsTrunc -1).
Notation IsHSet := (IsTrunc 0).

Ltac simple_induction n n' IH :=
  generalize dependent n;
  fix IH 1;
  intros [| n'];
  [ clear IH | specialize (IH n') ].


Notation is_mere_relation A R := (forall (x y : A), IsHProp (R x y)).


Monomorphic Axiom dummy_funext_type : Type0.
Monomorphic Class Funext := { dummy_funext_value : dummy_funext_type }.
Axiom isequiv_apD10 : forall `{Funext} (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Global Existing Instance isequiv_apD10.

Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g
  :=
  (@apD10 A P f g)^-1.

Global Arguments path_forall {_ A%type_scope P} (f g)%function_scope _.

Definition path_forall2 `{Funext} {A B : Type} {P : A -> B -> Type} (f g : forall x y, P x y) :
  (forall x y, f x y = g x y) -> f = g
  :=
  (fun E => path_forall f g (fun x => path_forall (f x) (g x) (E x))).

Global Arguments path_forall2 {_} {A B}%type_scope {P} (f g)%function_scope _.


Hint Resolve
  @idpath @inverse
 : path_hints.

Hint Resolve @idpath : core.

Ltac path_via mid := apply @concat with (y := mid); auto with path_hints.

Definition Type1 := Type.

Inductive Empty : Type1 := .


Definition not (A:Type) : Type := A -> Empty.
Notation "~ x" := (not x) : type_scope.
Hint Unfold not: core.
Notation "x <> y :> T" := (not (x = y :> T))
(at level 70, y at next level, no associativity) : type_scope.
Notation "x <> y" := (not(x = y :> _)) (at level 70, no associativity) : type_scope.

Definition symmetric_neq {A} {x y : A} : x <> y -> y <> x
  := fun np p => np (p^).
Typeclasses Opaque complement.

Definition complement {A} (x y : A) (R : relation A) := ~ (R x y).

Definition irreflexive {A} (x : A) (R : relation A) := ~ (R x x).

Definition Asymmetric {A} (x y : A) (R : relation A) := ~ (R x y -> R y x).

Class IsPointed (A : Type) := point : A.

Arguments point A {_}.

Record pType :=
  { pointed_type : Type ;
    ispointed_type : IsPointed pointed_type }.

Coercion pointed_type : pType >-> Sortclass.

Global Existing Instance ispointed_type.


Inductive Unit : Type1 :=
    tt : Unit.


Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.

Ltac rapply p :=
  refine p ||
  refine (p _) ||
  refine (p _ _) ||
  refine (p _ _ _) ||
  refine (p _ _ _ _) ||
  refine (p _ _ _ _ _) ||
  refine (p _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).


Ltac rapply' p :=
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _ _) ||
  refine (p _ _ _ _ _ _) ||
  refine (p _ _ _ _ _) ||
  refine (p _ _ _ _) ||
  refine (p _ _ _) ||
  refine (p _ _) ||
  refine (p _) ||
  refine p.


Tactic Notation "erapply" open_constr(term) := rapply term.

Tactic Notation "erapply'" open_constr(term) := rapply' term.


Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
      | reflexivity
      
      
      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.


Ltac by_extensionality x :=
  intros;
  match goal with
  | [ |- ?f = ?g ] => eapply path_forall; intro x;
      match goal with
        | [ |- forall (_ : prod _ _), _ ] => intros [? ?]
        | [ |- forall (_ : sigT _ _), _ ] => intros [? ?]
        | _ => intros
    end;
    simpl; auto with path_hints
  end.

Ltac f_ap :=
  idtac;
  lazymatch goal with
    | [ |- ?f ?x = ?g ?x ] => apply (@apD10 _ _ f g);
                             try (done || f_ap)
    | _ => apply ap11;
          [ done || f_ap
          | trivial ]
  end.


Ltac expand :=
  idtac;
  match goal with
    | [ |- ?X = ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' = Y')
    | [ |- ?X == ?Y ] =>
      let X' := eval hnf in X in let Y' := eval hnf in Y in change (X' == Y')
  end; simpl.




Ltac revert_opaque x :=
  revert x;
  match goal with
    | [ |- forall _, _ ] => idtac
    | _ => fail 1 "Reverted constant is not an opaque variable"
  end.


Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let __transparent_assert_hypothesis := (_ : type) in _);
  [
  | (
    let H := match goal with H := _ |- _ => constr:(H) end in
    rename H into name) ].


Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" "by" tactic3(tac) := let name := fresh "H" in transparent assert (name : type); [ solve [ tac ] | ].
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" := transparent assert (name : type).
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" "by" tactic3(tac) := transparent assert (name : type) by tac.


Ltac remember_as term name eqname :=
  set (name := term) in *;
  pose (eqname := idpath : term = name);
  clearbody eqname name.

Tactic Notation "remember" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  remember_as term name eqname.


Ltac recall_as term name eqname :=
  pose (name := term);
  pose (eqname := idpath : term = name);
  clearbody eqname name.

Tactic Notation "recall" constr(term) "as" ident(name) "eqn:" ident(eqname) :=
  recall_as term name eqname.


Ltac rel_hnf :=
  idtac;
  match goal with
    | [ |- ?R ?x ?y ] => let x' := (eval hnf in x) in
                         let y' := (eval hnf in y) in
                         change (R x' y')
  end.

Inductive Pos : Type1 :=
| one : Pos
| succ_pos : Pos -> Pos.

Definition one_neq_succ_pos (z : Pos) : ~ (one = succ_pos z).
Proof.
intros x.
inversion x.
Qed.


Definition succ_pos_injective {z w : Pos} (p : succ_pos z = succ_pos w) : z = w.
Proof.
inversion p.
reflexivity.
Qed.


Inductive Int : Type1 :=
| neg : Pos -> Int
| zero : Int
| pos : Pos -> Int.

Definition neg_injective {z w : Pos} (p : neg z = neg w) : z = w.
Proof.
inversion p.
reflexivity.
Qed.

Definition pos_injective {z w : Pos} (p : pos z = pos w) : z = w.
Proof.
inversion p.
reflexivity.
Qed.

Definition neg_neq_zero {z : Pos} : ~ (neg z = zero).
Proof.
intros H.
inversion H.
Qed.

Definition pos_neq_zero {z : Pos} : ~ (pos z = zero).
Proof.
intros H.
inversion H.
Qed.

Print pos_neq_zero.

Definition neg_neq_pos {z w : Pos} : ~ (neg z = pos w).
Proof.
intros H.
inversion H.
Qed.
