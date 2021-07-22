(** Reflexive proofs **)
(** A demo by Frederic Besson **)

Module Basic.

  Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

  Fixpoint add (n:nat) (m:nat) {struct n}: nat :=
    match n with
      | O => m
      | S n' =>  add n' (S m)
    end.

  Eval compute in (add (S (S O)) (S (S O))).

  Lemma refl_2_add_2_eq_4 : add (S (S O)) (S (S O)) = (S (S (S (S  O)))).
  Proof.
    compute.
    reflexivity.
  Qed.

End Basic.

Module NotSoBasic.

  Require Import ZArith.  (* Arithmetique sur Z *)
  Require Import List.    (* Definition des list *)

  (* Sucre syntaxique *)
  Open Scope Z_scope.
  Open Scope list_scope.

  (* Zmult_plus_distr_l: forall n m p, ((n + m) * p) = (n * p + m *  p) *)

  Lemma naiv_proof : forall x, 4* x + (8* x + (15* x + (16* x + (23*  x + 42* x)))) = 108* x.
  Proof.
  Admitted.

  Print naiv_proof.

  (* La syntaxe des formules *)
  Definition F :=  (list Z * Z)%type.
 
  (* listExpr [e1;e2;e3;..;en] x ----> (e1 * x) + ( (e2 * x) + ((e3  * x) .... + (en * x))) *)
  Definition listExpr  (l:list Z) (x:Z) : Z := 0. (* A REMPLACER*)


 (* sem x ([4;8;15;16;23;42],108) ---> (4* x + (8* x + (15* x +  (16* x + (23* x + 42* x)))) = 108* x) *)


  Definition sem (x:Z) (t:F) : Prop := 
    let (l,c) := t in
        listExpr l x = c * x.

  Lemma sem_test : forall x, sem x (4::8::15::16::23::42::nil,108) =  (4* x + (8* x + (15* x + (16* x + (23* x + 42* x)))) = 108* x).
  Proof.
  Admitted.


Definition sum (l:list Z) : Z := 0. (* A REMPLACER *)


Definition prover (t:F) : bool :=
  let (l,c) := t in
    Zeq_bool (sum l) c.


Lemma sum_listExpr : forall x l, (sum l)*x = listExpr l x.
Proof.
Admitted.

Lemma Zeq_bool_ok : forall (a b : Z), Zeq_bool a b = true -> a = b.
Proof.
intros.
unfold Zeq_bool in H.
apply Zcompare_Eq_eq.
destruct (a?=b).
trivial.
discriminate.
discriminate.
Admitted.



Lemma  prover_sound : forall t, prover t = true -> forall x, sem x t.
Proof.
Admitted.

Lemma example : forall x, 4* x + (8* x + (15* x + (16* x + (23* x +  42* x)))) = 108* x.
Proof.
  intro.
  assert (sem x (4::8::15::16::23::42::nil,108)).
  apply prover_sound.
  compute.
  reflexivity.
  assumption.
Qed.

Print example.

Lemma example2 : forall x, 5* x + (8* x + (12* x + (17* x + (4* x)))) = 46* x.
Proof.
Admitted.
