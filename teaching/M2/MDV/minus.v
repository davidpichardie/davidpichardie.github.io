Require Export Arith.

Lemma le_n_plus_n_O : forall n, n <= O -> n + O = O.
Proof.
  intros n H; inversion H; auto.
Qed.

Lemma n_eq_Sm_plus_n_O : forall m n, n = S m -> n + O = S m.
Proof.
  intros n m H; rewrite H; auto.
Qed.

Definition nat_dec : forall n m:nat, {n=m}+{n<>m} := eq_nat_dec.

Lemma le_n_Sm_diff : forall m n, n <= S m -> n <> S m -> n <= m.
Proof.
  intros n m H Heq; inversion H; intuition.
Qed.

Lemma plus_n_Sm : forall m n, n + S m = S (n + m).
Proof.
  induction n; simpl; auto.
Qed.

Lemma plus_Sp_Sm : forall m p n, n + p = m -> n + S p = S m.
Proof.
  intros n m p H; rewrite <- H; apply plus_n_Sm.
Qed.

Hint Resolve le_n_plus_n_O n_eq_Sm_plus_n_O le_n_Sm_diff plus_n_Sm plus_Sp_Sm.

Fixpoint minus (m n:nat) {struct m} : nat :=
  match m with
    | O => O
    | S p  => 
      if nat_dec n (S p)
        then O
        else S (minus p n) (* (1+p)-n=1+(p-n) *)
   end.

Eval compute in (minus (4) (2)).
Eval compute in (minus (4) (6)).
Eval compute in (plus (6) (minus (4) (6))).

Theorem minus_OK : forall m n, n <= m -> n + (minus m n) = m.
Proof.
  induction m; intros; simpl; auto.
  destruct nat_dec; auto.
Qed.

Fixpoint minus1 (m n:nat) {struct m} : n <= m -> nat :=
  match m return n<=m -> nat with
    | O => fun H: n <= O => O
    | S p => fun H: n <= S p =>
      match nat_dec n (S p) with
        | left _ => O
        | right heq =>
          S (minus1 p n (le_n_Sm_diff p n H heq))
      end
   end.

Extraction minus1.

Theorem minus1_OK : forall m n (H:n<=m), n + (minus1 m n H) = m.
Proof.
  induction m; intros; simpl; auto.
  destruct nat_dec; auto.
Qed.












Theorem minus2 : forall m n, n <= m -> { p:nat | n + p = m}.
Proof.
  induction m; intros.
  exists O; auto.
  destruct (nat_dec n (S m)).
  exists O; auto.
  destruct (IHm n) as [p Hp].
  auto.
  exists (S p); auto.
Qed.

Extraction minus2.










Definition type_minus m n := n <= m -> { p:nat | n + p = m }.

Definition minus3 :  forall m n, type_minus m n.
Proof.
Print minus1.
refine (
fix f (m n:nat) {struct m} : type_minus m n :=
  match m return type_minus m n with
    | O => fun H => exist _ O _
    | S p => fun H =>
      match nat_dec n (S p) with
        | left Heq => exist _ O _
        | right Heq => let (x,Hx) := (f p n _) in exist _ (S x) _
      end
  end
).
auto.
auto.
auto.
auto.
Qed.

Extraction minus3.



Fixpoint minus4 (m n:nat) {struct m} : type_minus m n :=
  match m return type_minus m n with
    | O => fun H => exist (fun p => n + p = 0) O (le_n_plus_n_O n H)
    | S p => fun H =>
      match nat_dec n (S p) with
        | left Heq => exist (fun x => n + x = S p) O (n_eq_Sm_plus_n_O p n Heq)
        | right Heq => let (x,Hx) := minus4 p n (le_n_Sm_diff p n H Heq) in
          exist (fun x => n + x = S p) (S x) (plus_Sp_Sm p x n Hx)
      end
  end.


