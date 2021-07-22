Section Predicat_calculus.

  (** [exist] *)

Variable A : Set.
Variable P : A -> Prop. (* unary predicat *)
Variable Q Q' : A -> A -> Prop. (* binary predicat *)

Lemma ex11 : (exists y, forall x, Q x y) -> (forall x, exists y, Q x y).
firstorder.
Qed.

Lemma ex12 : (forall x, ~ P x) -> ~ (exists x, P x).
firstorder.
Qed.

Lemma ex13 : (exists x, P x) -> ~ (forall x, ~ P x).
firstorder.
Qed.

End Predicat_calculus.

Section order.

Variable A:Set.
Variable eq R S:A->A->Prop.

Definition reflexive (R:A->A->Prop) := forall x y, eq x y -> R x y.
Definition irreflexive (R:A->A->Prop) := forall x y, R x y -> ~ eq x y.
Definition symmetric (R:A->A->Prop) := forall x y, R x y -> R y x.
Definition antisymmetric (R:A->A->Prop) := forall x y, R x y -> R y x -> eq x y.
Definition transitive (R:A->A->Prop) := forall x y z, R x y -> R y z -> R x z.

Definition equiv (R:A->A->Prop) := reflexive R /\ transitive R /\ symmetric R.
Definition partial_order (R:A->A->Prop) := reflexive R /\ transitive R /\ antisymmetric R.

Definition lexico_combi (R1 R2:A->A->Prop) (x y:A) :=
  R1 x y \/ (eq x y /\ R2 x y).

Theorem partial_order_lexico : 
  equiv eq -> 
  partial_order R -> 
  partial_order S -> 
  partial_order (lexico_combi R S).
Proof.
  unfold equiv, partial_order; intros.

Qed.

End order.

(******* Exercice bonus ********)
(* Formaliser et prouver (avec le tiers exclu):
  Dans tout bar non vide, on peut trouver au moins une personne telle
  que si elle boit, alors tous les autres boivent. *)



