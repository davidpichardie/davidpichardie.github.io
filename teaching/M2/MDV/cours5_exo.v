Require Export Arith.
Require Export ZArith.

Section A.

Theorem eq_sym' : forall (A:Type)(a b:A), a=b->b=a.
Proof.
 intros A a b e.
 rewrite e.
 reflexivity.
Qed.

End A.

Section B.
Open Scope Z_scope.

Check Zmult_plus_distr_l.

Lemma Zmult_distr_1 : forall n x:Z, n*x+x = (n+1)*x.
Proof.
 intros.
 rewrite Zmult_plus_distr_l.
 rewrite  Zmult_1_l.
 trivial.
Qed.

Lemma regroup : forall x:Z, x+x+x+x+x = 5*x.
Proof.
 intro x; pattern x at 1.
 rewrite <- Zmult_1_l.
 repeat rewrite Zmult_distr_1.
 auto with zarith.
Qed.

End B.


Section condrew.

Open Scope nat_scope.

Theorem le_lt_S_eq : forall n p:nat, n <= p -> p < S n -> n = p.
Proof.
Admitted.

Check plus_lt_reg_l.
Check plus_le_reg_l.


Lemma cond_rewrite_example : forall n:nat,
   8 < n+6 ->  3+n < 6 -> n*n = n+n.
Proof.
 intros n  H H0.
 rewrite <- (le_lt_S_eq 2 n).
 simpl.
 auto.
 apply  plus_le_reg_l with (p := 6). 
 rewrite plus_comm in H.
 auto with arith.
 apply   plus_lt_reg_l with (p:= 3).
 auto with arith.
Qed.


Section exo.

Open Scope nat_scope.

Check plus_comm.
Check plus_assoc.

Theorem plus_permute2 : forall n m p:nat, n+m+p=n+p+m.
Proof.
Admitted.

Theorem eq_trans :
   forall (A:Type)(x y z:A), x = y -> y = z -> x = z. 
Proof.
Admitted.

End exo.
