Section Propositional_Logic.

Variable A B C D E F : Prop.

  (** Solve them using only [intros] and [apply] *)

Lemma exo1 : (A -> B -> C) -> (A -> B) -> A -> C.
tauto.
Qed.

Lemma exo2: ((A -> B) -> C) -> (D -> B) -> (A -> D) -> C.
tauto.
Qed.

Lemma exo2bis: (A->B->(C->D)->E)->((A->D)->F)->(A->(B->E)->C)->(C->D)->F.
tauto.
Qed.

  (** [split] [destruct] *)

Lemma ex3 : A /\ B -> B /\ A.
tauto.
Qed.

Lemma ex4 : A /\ (B /\ C) -> (A /\ B) /\ C.
tauto.
Qed.

  (** [left] [right] *)

Lemma ex5 : A \/ B -> B \/ A.
tauto.
Qed.

Lemma ex6 : A /\ (B \/ C) <-> (A /\ B) \/ (A /\ C).
tauto.
Qed.

(* remember that the "absurd" command is useless *)

Lemma ex7 : ~A -> A -> False.
tauto.
Qed.

Lemma ex8 : A \/ ~A -> (~~A -> A).
tauto.
Qed.

Lemma ex9 : (~ A \/ ~ B) -> ~ (A /\ B).
tauto.
Qed.

(* A <-> B is sugar for (A->B)/\(B->A) *)
Lemma ex10 : (~ A /\ ~ B) <-> ~ (A \/ B).
tauto.
Qed.

Lemma ex10bis : A -> ~~A.
tauto.
Qed.

Lemma peirce_nj : ~~ (((A -> B) -> A) -> A).
tauto.
Qed.

(* For the last we need excluded middle axiom *)
Variable em : forall P:Prop, P \/ ~P.

Lemma peirce : ((A -> B) -> A) -> A.
Admitted.

End Propositional_Logic.





