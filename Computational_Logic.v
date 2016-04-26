Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (x : bool) : bool :=
match x with
| true => false
| false => true
end.

Check negb.

Lemma L1 : negb true = false.
Proof.
simpl.
reflexivity.
Qed.

Lemma negb_negb (x:bool) : negb (negb x) = x.
Proof.
destruct x.
reflexivity.
reflexivity.
Qed.

Definition andb (x y : bool) : bool :=
match x with
| true => y
| false => false
end.

Lemma andb_com x y : andb x y = andb y x.
Proof.
destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Defined.

Definition orb (x y : bool) : bool :=
match x with
| true => true
| false => y
end.

Check orb.

Lemma orb_com x y : orb x y = orb y x.
Proof.
destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Qed.

Lemma demorgan x y : negb (orb x y) = andb (negb x) (negb y).
Proof.
destruct x.
destruct y.
reflexivity.
reflexivity.
destruct y.
reflexivity.
reflexivity.
Qed.

Check fun x : bool => x.

Compute (fun x : bool => x) true.

Check andb true.

Compute andb true.

Definition andb' : bool -> bool -> bool :=
 fun x : bool =>
   fun y : bool =>
     match x with
      | true => y
      | false => false
end.

Print negb.

Print andb.
Print andb'.
