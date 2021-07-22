Require Export Arith. (** Charge le type [nat] des entiers de Péano *)

Lemma tout_entier_est_soit_0_soit_a_un_predecesseur :
 forall n : nat, n = O \/ (exists m : nat, n = S m).
Proof.
  intros.
  destruct n.
  left.
  reflexivity.
  right.
  exists n.
  reflexivity.
Qed.


Section induction.
  Variable double : nat -> nat.
  Hypothesis double_O : double O = O.
  Hypothesis double_S : forall n, double (S n) = S (S (double n)).

  Variable pair : nat -> Prop.
  Hypothesis pair_O : pair O.
  Hypothesis pair_S : forall n, pair n -> pair (S (S n)).

  Lemma double_pair : forall n, pair (double n).
  Proof.
    induction n.
    rewrite double_O.
    apply pair_O.
    rewrite double_S.
    apply pair_S.
    assumption.
  Qed.
End induction.


Definition is_zero (n:nat) :=
  match n with
    O => true
  | S p => false
  end.


Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n1 => S (S (double n1))
  end.

(* essayer [simpl] ... *)

Lemma double_prop1 : forall n : nat, double (S n) = S (S (double n)).
Proof.

Qed.

Fixpoint plus (n m : nat) {struct m} : nat :=
  match m with
  | O => n
  | S m1 => S (plus n m1)
  end.

Lemma plus_o_neutre_a_droite : forall n : nat, plus n O = n.
Proof.

Qed.
	
(* essayer [induction n] *)

Lemma plus_o_neutre_a_gauche : forall n : nat, plus O n = n.
Proof.

Qed.
	
Lemma plus_sn_m : forall n m : nat, plus (S n) m = S (plus n m).
Proof.

Qed.

Lemma double_plus : forall n : nat, double n = plus n n.
Proof.

Qed.

Lemma plus_commutative : forall n m : nat, plus n m = plus m n.
Proof.

Qed.

Lemma plus_associative : forall a b c : nat, plus a (plus b c) = plus (plus a b) c.
Proof.

Qed.

Lemma plus_associative' : forall a b c : nat, plus a (plus b c) = plus (plus a b) c.
Proof.

Qed.

(* 
Définir une version récursive terminale de plus.

Montrer son équivalence avec plus.

*)

Fixpoint tl_plus (n m:nat) {struct m} : nat :=
  match m with
    O => n
  | S p => tl_plus (S n) p
  end.

Lemma equiv_tl_plus : forall m n, tl_plus n m = plus n m.
Proof.

Qed.

(* Exercices facultatifs *)

Lemma n_non_S_n : forall n, n <> S n.
Proof.
Admitted.

Fixpoint mul (n m : nat) {struct m} : nat :=
  match m with
  | O => O
  | S m1 => plus (mul n m1) n
  end.

Lemma mul_assoc : forall a b c, mul a (mul b c) = mul (mul a b) c.
Proof.
Admitted.

Lemma mul_commut : forall a b, mul a b = mul b a.
Admitted.
