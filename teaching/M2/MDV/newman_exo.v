Require Export Wf.

Section A.

Variable A : Set.
Variable R : A -> A -> Prop.

Inductive star : A -> A -> Prop :=
| star_refl : forall x, star x x
| star_trans1 : forall x y z,
    R x y -> star y z -> star x z.

Definition confluence : Prop :=
  forall x y z,
    star x y -> star x z ->
    exists u, star y u /\ star z u.

Definition local_confluence : Prop :=
  forall x y z,
    R x y -> R x z ->
    exists u, star y u /\ star z u.

Definition terminant := well_founded (fun x y => R y x).

Theorem induction_bien_fonde : terminant ->
  forall P : A -> Prop,
  (forall x : A, (forall x' : A, R x x' -> P x') -> P x) ->
  forall a : A, P a.
Proof.
  apply well_founded_ind with (R:=fun x y => R y x).
Qed.

Hint Constructors star.

(** A completer ˆ partir d'ici **)

Lemma star_trans : forall x y, star x y -> forall z, star y z -> star  x z.
Proof.
Admitted.

Theorem newman : terminant -> local_confluence -> confluence.
Proof.
  unfold local_confluence, confluence.
 intros Ht Hl.
  intros x.
  elim x using induction_bien_fonde;clear x.  
Admitted.

End A. 