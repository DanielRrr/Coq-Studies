Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst' (p : natprod) : nat := 
  match p with
  | pair x y => x
  end.
Definition snd' (p : natprod) : nat := 
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat := 
  match p with
  | (x,y) => x
  end.
Definition snd (p : natprod) : nat := 
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod := 
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),(n,m) = (fst (n,m), snd (n,m)).
Proof.
reflexivity. 
Qed.

Theorem surjective_pairing : forall (p : natprod), p = (fst p, snd p).
Proof.
intros p.
destruct p as [m n].
simpl.
reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),(snd p, fst p) = swap_pair p.
Proof.
intros p.
destruct p as [m n].
simpl.
reflexivity.
Qed.


Theorem fst_swap_is_snd : forall (p : natprod), fst (swap_pair p) = snd p.
Proof.
intros p.
destruct p as [m n].
simpl.
reflexivity.
Qed.


Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.


Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x + y" := (plus x y)  
                    (at level 50, left associativity).


Fixpoint repeat (n count : nat) : natlist := 
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat := 
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist := 
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).


Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil 
  | h :: t => t
  end.


Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t =>
      match h with
        | 0 => nonzeros t
        | _ => h :: (nonzeros t)
      end
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
simpl.
reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
   | nil => nil
   | h :: t => 
   match evenb h with
    | true => oddmembers t
    | false => h :: (oddmembers t)
   end
end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
simpl.
reflexivity.
Qed.


Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
   | nil => 0
   | h :: t =>
    match evenb h with
     | true => countoddmembers t
     | false => 1 + (countoddmembers t)
end
end.


Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof.
simpl.
reflexivity.
Qed.


Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof.
simpl.
reflexivity.
Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof.
simpl.
reflexivity.
Qed.


Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
   | nil => l2
   | h :: t =>
    match l2 with
     | nil => l1
     | h' :: t' => h :: h' :: (alternate t t')
end
end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
simpl.
reflexivity.
Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof.
simpl.
reflexivity.
Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof.
simpl.
reflexivity.
Qed.

Example test_alternate4: alternate [] [20;30] = [20;30].
Proof.
simpl.
reflexivity.
Qed.

Definition bag := natlist.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Fixpoint count (v:nat) (s:bag) : nat := 
  match s with
   | nil => 0
   | x :: xs =>
   match beq_nat v x with
    | true => 1 + (count v xs)
    | false => count v xs
end
end.


Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.
reflexivity.
Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof.
simpl.
reflexivity.
Qed.

Definition sum (x : bag) (y : bag) : bag := app x y.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof.
simpl.
reflexivity.
Qed.

Definition add (v:nat) (s:bag) : bag := app [v] s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof.
simpl.
reflexivity.
Qed.


Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof.
simpl.
reflexivity.
Qed.


Definition member (v:nat) (s:bag) : bool := 
  match count v s with
  | 0 => false
  | _ => true
end.


Example test_member1: member 1 [1;4;1] = true.
Proof.
simpl.
reflexivity.
Admitted.


Example test_member2: member 2 [1;4;1] = false.
Proof.
reflexivity.
Admitted.


Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | x :: xs =>
      match (beq_nat v x) with
        | true => xs
        | false => add x (remove_one v xs)
      end
  end.


Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | x :: xs =>
      match (beq_nat v x) with
        | true => (remove_all v xs)
        | false => add x (remove_all v xs)
      end
  end.


Theorem nil_app : forall l : natlist, [] ++ l = l.
Proof.
intros l.
simpl.
reflexivity.
Qed.

Theorem tl_length_pred : forall l:natlist, pred (length l) = length (tl l).
Proof.
intros l.
destruct l.
simpl.
reflexivity.
reflexivity.
Qed.


Theorem app_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
intros l1 l2 l3.
induction l1.
simpl.
reflexivity.
simpl.
rewrite <- IHl1.
reflexivity.
Qed.


Theorem app_length : forall l1 l2 : natlist, length (l1 ++ l2) = (length l1) + (length l2).
Proof.
intros l1 l2.
induction l1.
simpl.
reflexivity.
simpl.
rewrite -> IHl1.
reflexivity.
Qed.


Fixpoint snoc (l:natlist) (v:nat) : natlist := 
  match l with
  | nil => [v]
  | h :: t => h :: (snoc t v)

  end.


Fixpoint rev (l:natlist) : natlist := 
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. 
simpl.
reflexivity. 
Qed.


Example test_rev2: rev nil = nil.
Proof.
simpl. 
reflexivity. Qed.


Theorem length_snoc : forall n : nat, forall l : natlist, length (snoc l n) = S (length l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> IHl.
reflexivity.
Qed.

Theorem rev_length : forall l : natlist, length (rev l) = length l.
Proof.
intros.
induction l.
reflexivity.
simpl.
rewrite -> length_snoc.
rewrite -> IHl.
reflexivity.
Qed.


Theorem app_nil_end : forall l : natlist, l ++ [] = l.
Proof.
intros l.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> IHl.
reflexivity.
Qed.

Theorem rev_snoc : forall (n:nat) (l:natlist), rev (snoc l n) = n :: (rev l).
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> IHl.
reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
intros l.
induction l.
simpl.
reflexivity.
simpl.
rewrite -> rev_snoc.
rewrite -> IHl.
reflexivity.
Qed.


Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
intros.
rewrite -> app_assoc.
rewrite -> app_assoc.
reflexivity.
Qed.


Theorem snoc_append : forall (l:natlist) (n:nat), snoc l n = l ++ [n].
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
rewrite IHl.
reflexivity.
Qed.


Theorem distr_rev : forall l1 l2 : natlist, rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
intros.
induction l1.
simpl.
rewrite -> app_nil_end.
reflexivity.
simpl.
rewrite -> IHl1.
Lemma snoc_app: forall (l1 l2:natlist) (n:nat), snoc (l1 ++ l2) n = l1 ++ snoc l2 n.
Proof.
intros.
induction l1.
simpl.
reflexivity.
simpl.
rewrite -> IHl1.
reflexivity.
Qed.
rewrite -> snoc_app.
reflexivity.
Qed.


Lemma nonzeros_app : forall l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
intros l1 l2.
induction l1.
simpl.
reflexivity.
simpl.
rewrite -> IHl1.
destruct n.
reflexivity.
simpl.
reflexivity.
Qed.


Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1 with
| nil => match l2 with
| nil => true
| _ => false
end
| v1 :: r1 => match l2 with
| nil => false
| v2 :: r2 => if beq_nat v1 v2 then beq_natlist r1 r2
else false
end
end.


Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof.
simpl.
reflexivity.
Qed.

Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof.
simpl.
reflexivity.
Qed.


Theorem beq_nat_refl : forall n : nat, true = beq_nat n n.
Proof.
intros n.
induction n.
simpl.
reflexivity.
rewrite IHn.
reflexivity.
Qed.

Theorem beq_natlist_refl : forall l:natlist, true = beq_natlist l l.
Proof.
intros l.
induction l.
reflexivity.
simpl.
rewrite <- beq_nat_refl.
rewrite IHl.
reflexivity.
Qed.


Theorem count_member_nonzero : forall (s : bag), ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
intros.
induction s.
simpl.
reflexivity.
reflexivity.
Qed.


Theorem ble_n_Sn : forall n, ble_nat n (S n) = true.
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
rewrite IHn.
reflexivity.
Qed.


Theorem remove_decreases_count: forall (s : bag), ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
intros.
induction s.
simpl.
reflexivity.
simpl.
destruct n.
rewrite -> ble_n_Sn.
reflexivity.
simpl.
rewrite IHs.
reflexivity.
Qed.


Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
Lemma rev_fun : forall (l1 l2 : natlist), l1 = l2 -> rev l1 = rev l2.
Proof.
intros.
rewrite -> H.
reflexivity.
Qed.
intros.
rewrite <- rev_involutive with (l := l1).
rewrite <- rev_involutive with (l := l2).
apply rev_fun.
apply H.
Qed.
