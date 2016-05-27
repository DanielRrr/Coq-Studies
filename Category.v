Require Export Coq.Classes.Morphisms.
Export Coq.Classes.Morphisms.ProperNotations.
Require Export Coq.Classes.SetoidClass.
Generalizable All Variables.
Open Scope signature.

Class Arrows (X: Type) : Type := Hom : X -> X -> Type.
Infix "~~>" := Hom (at level 90, right associativity).

 Class Category Obj `{Arrows Obj} := 
  { 
     arrows_setoid :> forall x y, Setoid (x ~~> y)
   ; comp : forall {x y z}, `(y ~~> z) -> `(x ~~> y) -> (x ~~> z)
   ; comp_assoc : forall `(f : a ~~> b) `(g : b ~~> c) `(h : c ~~> d),
     comp h (comp g f) == comp (comp h g) f
   ; comp_proper :> forall a b c, Proper (equiv ==> equiv ==> equiv) (@comp a b c)
   ; cat_id : forall {a}, a ~~> a
   ; id_l : forall `(f : a ~~> b), comp f cat_id == f
   ; id_r : forall `(f : a ~~> b), comp cat_id f == f
   }.
 
 Notation " x 'o' y " := (comp x y) (at level 40, left associativity).

Section Functor.

Context `{Category C} `{Category D}.

Class Functor (F: C -> D) 
   (fmap : forall {a b: C}, (a ~~> b) -> (F a ~~> F b)) :=
   { 
    fmap_preserve_id : forall {a}, 
     fmap (cat_id : a ~~> a) == (cat_id : (F a ~~> F a))
   ; fmap_respects_comp : forall `(f: a ~~> b) `(g : b ~~> c),
     fmap (g o f) == fmap g o fmap f
   ; fmap_proper :> forall {a b : C} , Proper (equiv ==> equiv) (@fmap a b)
   }.
 
 End Functor.
