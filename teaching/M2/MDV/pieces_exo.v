Require Export Arith.
Require Export Omega.

(*
le_lt_dec : forall n m : nat, {n <= m} + {m < n}

"destruct (le_lt_dec a b)" permet de faire deux cas : a<=b et b<a.
*)

Lemma exo : forall n, exists i, exists j, n + 8 = 5*i + 3*j.
Proof.
Admitted.