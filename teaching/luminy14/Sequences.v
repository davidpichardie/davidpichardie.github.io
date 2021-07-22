(** Sequences of transitions. *)
Require Import MSMLib.

Set Implicit Arguments.

Section SEQUENCES.

Variable A: Type.
Variable R: A -> A -> Prop.

(** Zero, one or several transitions: reflexive, transitive closure of [R]. *)

Inductive star: A -> A -> Prop :=
  | star_refl: forall a,
      star a a
  | star_step: forall a b c,
      R a b -> star b c -> star a c.

Lemma star_one:
  forall (a b: A), R a b -> star a b.
Proof.
  (* TODO *)
Admitted.

Lemma star_trans:
  forall (a b: A), star a b -> forall c, star b c -> star a c.
Proof.
(* TODO *)
Admitted.


End SEQUENCES.


  


