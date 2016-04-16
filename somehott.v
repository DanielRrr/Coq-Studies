Definition idmap A := fun x : A => x.

Definition compose {A B C} (g : B -> C) (f : A -> B)(x : A) := g (f x).

Notation "g 'o' f" := (compose g f) (left associativity, at level 37).

Inductive paths {A} : A -> A -> Type := idpath : forall x, paths x x.

Notation "x ~~> y" := (paths x y) (at level 70).

Inductive total {B : Type} (A : B -> Type) : Type := pair (x : B)(y : A x).

Definition dirprod {A B : Type} : Type := total (fun x : A => B).


Definition concat {A} {x y z : A} : (x ~~> y) -> (y ~~> z) -> (x ~~> z).
Proof.
intros p q.
induction p.
induction q.
apply idpath.
Defined.

Notation "p @ q" := (concat p q) (at level 60).

Definition opposite {A} {x y : A} : (x ~~> y) -> (y ~~> x).
intros p.
induction p.
apply idpath.
Defined.

Notation "! p" := (opposite p) (at level 50).

Ltac path_induction :=
intros; repeat progress (
match goal with
 | [p: _ ~~> _ |-_] => induction p
 | _ => idtac
 end
); auto.


Lemma idpath_left_unit A (x y : A) (p : x ~~> y) : (idpath x @ p) ~~> p.
Proof.
path_induction.
apply idpath.
Defined.

Lemma idpath_right_unit A (x y : A) (p : x ~~> y) : (p @ idpath y) ~~> p.
Proof.
path_induction.
apply idpath.
Defined.

Lemma opposite_right_inverse A (x y : A) (p : x ~~> y) : (p @ !p) ~~> idpath x.
Proof.
path_induction.
apply idpath.
Defined.

Lemma opposite_left_inverse A (x y : A) (p : x ~~> y) : (!p @ p) ~~> idpath y.
Proof.
path_induction.
apply idpath.
Defined.

Lemma opposite_concat A (x y z : A) (p : x ~~> y) (q : y ~~> z) : !(p @ q) ~~> !q @ !p.
Proof.
path_induction.
apply idpath.
Defined.

Lemma opposite_opposite A (x y : A) (p : x ~~> y) : !(!p) ~~> p.
Proof.
path_induction.
apply idpath.
Defined.

Hint Resolve 
idpath_left_unit idpath_right_unit
opposite_right_inverse opposite_left_inverse.

Lemma concat_associativity A (w x y z : A) (p : w ~~> x) (q : x ~~> y) (r : y ~~> z) : (p @ q) @ r ~~> p @ (q @ r).
Proof.
path_induction.
Defined.

Definition homotopy_concat A (x y z : A)(p p': x ~~> y)(q q': y ~~> z) : (p ~~> p') -> (q ~~> q') -> (p @ q ~~> p' @ q').
Proof.
path_induction.
Defined.

Lemma map {A B} {x y : A} (f : A -> B) (p : x ~~> y) : f x ~~> f y.
Proof.
path_induction.
apply idpath.
Defined.

Lemma idpath_map A B (x : A)(f : A -> B) : map f (idpath x) ~~> idpath (f x).
Proof.
path_induction.
apply idpath.
Defined.

Lemma concat_map A B (x y z : A)(f : A -> B)(p : x ~~> y)(q : y ~~> z): map f (p @ q) ~~> (map f p) @ (map f q).
Proof.
path_induction.
apply idpath.
Defined.

Lemma idmap_map A (x y : A)(p : x ~~> y) : map (idmap A) p ~~> p.
Proof.
path_induction.
apply idpath.
Defined.

Lemma composition_map A B C (f : A -> B)(g : B -> C)(x y : A)(p : x ~~> y) : map (compose g f) p ~~> map g (map f p).
Proof.
path_induction.
apply idpath.
Defined.

Lemma opposite_map A B (f : A -> B)(x y : A)(p : x ~~> y) : !(map f p) ~~> map f(!p).
Proof.
path_induction.
apply idpath.
Defined.

Lemma map_cancel A B (f : A -> B)(x y : A)(p q : x ~~> y) : p ~~> q -> (map f p ~~> map f q).
Proof.
intros g.
path_induction.
apply idpath.
Defined.

Hint Resolve
concat_map
opposite_map map_cancel
opposite_concat opposite_opposite
homotopy_concat : path_hints.

Ltac path_tricks := 
first
[apply homotopy_concat
| apply opposite_map
| apply opposite_opposite
| apply opposite_concat
| apply map_cancel
| idtac] ; auto with path_hints.

Ltac path_via x := apply @ concat with (y := x); path_tricks.

Lemma map_naturality A (f : A -> A)(p : forall x, f x ~~> x)(x y : A)(q : x ~~> y) : map f q @ p y ~~> p x @ q.
Proof.
induction q.
path_via (p x).
apply idpath_left_unit.
apply opposite; apply idpath_right_unit.
Defined.

Hint Resolve map_naturality : path_hints.

Lemma homotopy_naturality A B (f g : A -> B) (p : forall x, f x ~~> g x)(x y : A)(q : x ~~> y) : map f q @ p y ~~> p x @ map g q.
Proof.
induction q.
path_via (p x).
path_via (idpath (f x) @ p x).
apply opposite; auto.
apply idpath.
apply idpath.
path_via (p x @ idpath (g x)).
apply opposite; auto.
apply idpath.
apply idpath.
Defined.

Lemma concat_cancel_right A (x y z : A)(p q : x ~~> y)(r : y ~~> z) : p @ r ~~> q @ r -> p ~~> q.
Proof.
intro a.
induction p.
induction r.
path_via (q @ idpath x).
Defined.

Lemma concat_cancel_left A (x y z : A)(p : x ~~> y)(q r : y ~~> z) : p @ q ~~> p @ r -> q ~~> r.
Proof.
intro a.
induction p.
induction r.
path_via (idpath x @ q).
apply opposite; auto.
Defined.

Lemma concat_move_over_left A (x y z : A)(p : x ~~> z)(q : x ~~> y)(r : y ~~> z): p ~~> q @ r -> p @ !r ~~> q.
Proof.
intro a.
apply concat_cancel_right with (r := r).
path_via (p @ (!r @ r)).
apply concat_associativity.
path_via (p @ idpath z).
path_via p.
apply idpath.
apply idpath.
path_induction.
Defined.

Definition contractible A := {x : A & forall y : A, y ~~> x}.


Lemma happly {A B}{f g : A -> B}: (f ~~> g) -> (forall x, f x ~~> g x).
Proof.
path_induction.
apply idpath.
Defined.

Theorem transport {A} {P : A -> Type} {x y : A}(p : x ~~> y) : P x -> P y.
Proof.
path_induction.
Defined.

Lemma total_paths (A : Type)(P : A -> Type)(x y : sigT P)(p : projT1 x ~~> projT1 y): (transport p (projT2 x) ~~> projT2 y) -> (x ~~> y).
Proof.
intros q.
destruct x as [x H].
destruct y as [y G].
simpl in * |- *.
induction p.
simpl in q.
path_induction.
apply idpath.
Defined.

Definition base_path {A}{P : A -> Type}{u v : sigT P}: (u ~~> v) -> (projT1 u ~~> projT1 v).
path_induction.
apply idpath.
Defined.

Definition hfiber {A B}(f : A -> B)(y : B) := {x : A & f x ~~> y}.


Ltac contract_hfiber y p :=
match goal with
| [|- contractible (@hfiber _ _ ?f ?x )] =>
  eexists (existT (fun z => f z ~~> x) y p);
    let z := fresh "z" in
    let q := fresh "q" in
      intros [z q]
end.

Lemma transport_hfiber A B (f : A -> B)(x y : A)(z : B)(p : x ~~> y)(q : f x ~~> z) : transport (P := fun x => f x ~~> z)p q ~~> !(map f p) @ q.
Proof.
induction p.
path_via q.
path_via (!(idpath (f x)) @ q).
path_via (idpath (f x) @ q).
apply opposite; auto.
apply idpath.
apply idpath.
path_induction.
apply opposite.
apply idmap_map.
Defined.

Definition isweq {A B}(f : A -> B) := forall y : B, contractible (hfiber f y).

Definition weq A B := {w : A -> B & isweq w}.

Definition idweq A : weq A A.
Proof.
exists (idmap A).
intros x.
contract_hfiber x (idpath x).
apply total_paths with (p:=q).
simpl.
compute in q.
path_induction.
apply idpath.
Qed.

Definition path_to_weq {U V} : U ~~> V -> weq U V.
Proof.
intro p.
induction p as [S].
exact (idweq S).
Qed.

Axiom univalence : forall U V, isweq (@path_to_weq U V).

Definition weq_to_path {U V} : weq U V -> U ~~> V.
Proof.
apply univalence.
Qed.

Definition pred_weq_to_path U V : (weq U V -> Type) -> (U ~~> V -> Type).
Proof.
intros Q p.
apply Q.
apply path_to_weq.
exact p.
Qed.
