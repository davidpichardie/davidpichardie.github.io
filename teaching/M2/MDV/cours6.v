Require Export ZArith.
Require Export List.
Require Export Arith.
Open Scope Z_scope.

Section Ex.

Theorem ring_example1 : forall x y:Z, (x+y)*(x+y)=x*x + 2*x*y + y*y.
Proof.
 intros x y; ring.
Qed.

Definition square (z:Z) := z*z.

Theorem ring_example2 :
  forall x y:Z, square (x+y) = square x + 2*x*y + square y.
Proof.
 intros x y; ring.
 unfold square; ring.
Qed.

Theorem ring_example3 : 
  (forall x y:nat, (x+y)*(x+y) = x*x + 2*x*y + y*y)%nat.
Proof.
 intros x y; ring.
Qed.

Theorem ring_example4 :
 (forall x:nat, (S x)*(x+1) = x*x + (x+x+1))%nat.
Proof.
 intro x; ring.
 ring_nat.
Qed.

Require Omega.

Theorem omega_example1 :
 forall x y z t:Z, x <= y <= z /\  z <= t <= x -> x = t.
Proof.
 intros x y z t H; omega.
Qed.

Theorem omega_example2 :
 forall x y:Z,
    0 <= square x -> 3*(square x) <= 2*y -> square x <= y.
Proof.
 intros x y H H0; omega.
Qed.

Theorem omega_example3 :
 forall x y:Z,
   0 <= x*x -> 3*(x*x) <= 2*y -> x*x <= y.
Proof.
 intros x y H H0; omega.
Qed.

Check (fun (X y:Z) => 0 <= X -> 3*X <= 2*y  ->  X < y).
Require Export Reals.

Open Scope R_scope.

Theorem example_for_field : forall x y:R, y <> 0 ->(x+y)/y = 1+(x/y).
Proof.
  intros x y H; field.
  trivial.
Qed.
Require Import Fourier.

Theorem example_for_Fourier : forall x y:R, x-y>1->x-2*y<0->x>1.
Proof.
  intros x y H H0.
  fourier.
Qed.

End Ex.


