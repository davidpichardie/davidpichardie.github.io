Require Export Arith.

Section A.

Variable A:Set.

(* A type list exists in the Coq library List but we use our own here *)
Inductive list : Set :=
  nil : list
| cons : A -> list -> list.

(* Useful notations *)
Notation "[]" := nil.
Notation "a :: q" := (cons a q) (at level 40).
Notation "[ a ]" := (a::[]).

Fixpoint length (l:list) : nat :=
  match l with
    [] => O
  | x::q => S (length q)
  end.

Fixpoint app (l1 l2:list) {struct l1} : list :=
  match l1 with
    [] => l2
  | x::q => x::(app q l2)
  end.

Notation "l1 ++ l2" := (app l1 l2) (at level 60).

Fixpoint rev (l:list) : list :=
  match l with
    [] => []
  | x::q => rev q ++ [x]
  end.

Fixpoint rev_app (l1 l2:list) {struct l1} : list :=
  match l1 with
    [] => l2
  | x::q => rev_app q (x::l2)
  end.

Lemma length_app : forall l1 l2, 
  length (l1 ++ l2) = plus (length l1) (length l2).
Proof.
Qed.

Lemma app_assoc : forall l1 l2 l3,
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.

Qed.

Lemma rev_app_is_rev_acc : forall l acc,
  (rev l)++acc = rev_app l acc.
Proof.

Qed.

Lemma rev_app_is_rev : forall l,
  rev l = rev_app l [].
Proof.

Qed.

Lemma rev_app_prop : forall l1 l2,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
Admitted.

Theorem rev_rev_id : forall l:list, rev (rev l) = l.
Proof.
Admitted.

End A.




