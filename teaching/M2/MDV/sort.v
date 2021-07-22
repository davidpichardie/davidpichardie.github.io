Require Export Arith.
Require Export Omega.
Require Export List.

Fixpoint test_eq_nat (n m:nat) {struct n} : bool :=
  match n,m with
    O,O => true
  | S n0,S m0 => test_eq_nat n0 m0
  | _,_ => false
  end.

Fixpoint test_le (n m:nat) {struct n} : bool :=
  match n with
    O => true
  | S n0 => match m with
              O => false
            | S m0 => test_le n0 m0
            end
  end.

Definition correct_test (A:Set) (R:A->A->Prop) (test:A->A->bool) : Prop :=
  forall x y, if (test x y) then R x y else ~ R x y.

Lemma test_eq_nat_correct : correct_test nat (@eq nat)  test_eq_nat.
Proof.
  unfold correct_test.
  induction x; destruct y; simpl; auto.
  assert (if test_eq_nat x y then x = y else x <> y).
  apply IHx.
  destruct (test_eq_nat x y); auto with arith.
Qed.
    
Lemma test_le_correct : correct_test nat le  test_le.
Proof.
  unfold correct_test.
  induction x; destruct y; simpl; auto with arith.
  assert (H:=IHx y).
  destruct (test_le x y); auto with arith.
Qed.
    
Fixpoint insert (a:nat) (l:list nat) {struct l} : list nat :=
  match l with
    nil => a::nil
  | x::q => if test_le a x then a::l else x::(insert a q) 
  end.

Inductive sorted : list nat -> Prop :=
  | sorted0 : sorted nil
  | sorted1 : forall x, sorted (x::nil) 
  | sorted2 : forall x y l,
    le x y -> sorted (y::l) -> sorted (x::y::l).

Lemma insert_keep_sorted : forall a l,
  sorted l -> sorted (insert a l).
Proof.
  (* exercice *)
Admitted.

Fixpoint insert_sort (l:list nat) : list nat :=
  match l with
    nil => nil
  | a::q => insert a (insert_sort q)
  end.

Lemma insert_sort_sorted : forall l, sorted (insert_sort l).
Proof.
  (* exercice *)
Admitted.

Eval compute in (insert_sort (4::2::6::3::8::1::9::7::5::nil)).

Definition efficient_sort (l:list nat) : list nat := nil.

Lemma efficient_sort_sorted : forall l, sorted (efficient_sort l).
Proof.
  constructor.
Qed.

(* So, sorted was maybe too weak to specify a sorting procedure... *)

Inductive occur (a:nat) : list nat -> nat -> Prop :=
  occur_nil : occur a nil O
| occur_cons1 : forall l n,
    occur a l n -> occur a (a::l) (S n)
| occur_cons2 : forall x l n,
    a<>x ->
    occur a l n -> occur a (x::l) n.
Hint Constructors occur : sort.

Lemma insert_occur1 : forall a l n,
  occur a l n -> occur a (insert a l) (S n).
Proof.
  (* exercice *)
Admitted.

Lemma insert_occur2 : forall a l x n,
  a<>x -> occur x l n -> occur x (insert a l) n.
Proof.
  (* exercice *)
Admitted.

Lemma insert_sort_same_occur1 : forall x n l, 
  occur x l n -> occur x (insert_sort l) n.
Proof.
  (* exercice *)
  (* you may need some intermediates lemmas *)
Admitted.

Lemma insert_sort_same_occur2 : forall x l n, 
  occur x (insert_sort l) n -> occur x l n.
Proof.
  (* exercice *)
Admitted.

Definition permut (l1 l2:list nat) : Prop :=
  forall x n, occur x l1 n <-> occur x l2 n.

Lemma insert_sort_permut : forall l, permut l (insert_sort l).
Proof.
  (* exercice *)
Admitted.
