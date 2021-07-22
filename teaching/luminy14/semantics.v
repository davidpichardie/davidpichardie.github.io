(***********************************
     Program semantics
***********************************) 
Require Import MSMLib.

Open Scope Z_scope.
(* To interpret [+], [-], etc, as operations on [Z] *)


(* We open a module to make experiments without incurring name conflicts *)
Module Exp1.

(* Numerical expressions (without symbolic variables) *)
Inductive aexp : Type :=
  | Econst (n:Z)                  (**r constante *)
  | Eplus (a1 a2: aexp)           (**r somme [a1 + a2] *)
  | Eminus (a1 a2: aexp).         (**r difference [a1 - a2] *)

(* What is the semantics of such an expression?
   -> expression evaluation *)
Fixpoint aeval (a : aexp) : Z :=
  match a with
  | Econst n => ???
  | Eplus a1 a2 => ???
  | Eminus a1 a2 => ???
  end.

(* We can test, inside Coq, this function *)
Compute (aeval (Eplus (Econst 4) (Econst 10))).

(* We can perform symbolic optimisation on expressions.
   Note: at this point, this a bit artificial because we don't have
         symbolic variables yet. *)
Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | Econst n => Econst n
  | Eplus (Econst 0) e2 => optimize_0plus e2
  | Eplus e1 e2 => ???
  | Eminus e1 e2 => ???
  end.

(* Semantics is needed to state the correctness theorem of
   [optimize_0plus]. *)
Lemma optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.

Qed.

(***** More Tactics *****)

(** go **)
(* This 'big hammer' tactics tries to kill the current subgoal, with
  a combination of omega, congruence, basic rewriting, uses of
  inductive predicate constructors and function simplifications.
  It leaves the subgoal untouched if it can't kill it. *)
(* Example: use [go] to shorten the previous proof. *)

Lemma optimize_0plus_sound_go: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  induction a; go.
  simpl.
  destruct a1; go.
  destruct n; go.
Qed.

(** flatten, flatten hyp_name **)
(* This tactic can be used on a subgoal or an hypothesis that contains
  a [match ... with ... end] construction. It will make a flattening of 
  the matching tree and create as many subgoals as paths in the tree. Some
  of these subgoals may be obvious and then automatically discharged by
  the tactic.
  *)

Lemma optimize_0plus_sound_go_flatten: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  induction a; go.
  simpl.
  flatten; go.
Qed.

End Exp1.

(* We now want to add variables in expressions *)

(* Identifiers will be simple integers. *)
Definition ident : Type := Z.

(* A useful equality test on identifiers. *)
Definition eq_ident: forall (x y: ident), {x=y}+{x<>y} := Z_eq_dec.

Inductive aexp : Type :=
  | Econst (z:Z) : aexp
  | Evar (v:ident) : aexp                    (* We add symbolic variables *)
  | Eplus (a1:aexp) (a2:aexp) : aexp
  | Eminus (a1:aexp) (a2:aexp) : aexp.

(* To evaluate an expression, we need to know the value of each
    symbolic variables. *)
Definition env := ident -> Z.

Fixpoint aeval (e:env) (a : aexp) : Z :=
  match a with
  | Econst n => n
  | Evar x => e x
  | Eplus a1 a2 => (aeval e a1) + (aeval e a2)
  | Eminus a1 a2 => (aeval e a1) - (aeval e a2)
  end.

(* But semantics of program is not always easily defined with functions.
   Relations are useful too. *)
Inductive aeval_rel : env -> aexp -> Z -> Prop :=
  | Econst_rel e n 
   :(* ==================== *)
    aeval_rel e (Econst n) n

  | Evar_rel e x
   :(* ==================== *)
   aeval_rel e (Evar x) (e x)

  | Eplus_rel e a1 a2 v1 v2  
   (EVAL1: aeval_rel e a1 v1)
   (EVAL2: aeval_rel e a2 v2)
   :(* ==================== *)
    aeval_rel e (Eplus a1 a2) (v1 + v2)

  | Eminus_rel e a1 a2 v1 v2  
   (EVAL1: aeval_rel e a1 v1)
   (EVAL2: aeval_rel e a2 v2)
   :(* ==================== *)
   aeval_rel e (Eminus a1 a2) (v1 - v2).

Lemma aeval_rel_equiv_aeval : forall e a v,
  aeval_rel e a v <-> aeval e a = v.                                  
Proof.
  split.
  - intros H; induction H; go.
  - intros; induction a; go.
Qed.


(* We also need some boolean expressions *)
Inductive bexp : Type :=
  | Eq (a1:aexp) (a2:aexp) : bexp     (**r equality test [a1 == a2] *)
  | Le (a1:aexp) (a2:aexp) : bexp.    (**r lesser or equal [a1 <= a2] *)

(** statement syntax *)
Inductive command : Type :=
  | Skip : command                         (**r nothing to do *)
  | Assign (x:ident) (a:aexp) : command    (**r assignment [x = a;] *)
  | Seq (c1:command) (c2:command) : command  (**r sequence [c1; c2] *)
  | If (b:bexp) (c1:command) (c2:command) : command 
                        (**r conditionnelle [if (b) { c1 } else {c2}] *)
  | While (b:bexp) (c:command) : command.  (**r loop [while (b) { c }] *)

(* We add some handy notation to write programs.
   (You don't need to understand the command we use here). *)
Notation "'SKIP'" :=
  Skip.
Notation "x '::=' a" :=
  (Assign x a) (at level 60).
Notation "c1 ;; c2" :=
  (Seq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (While b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (If c1 c2 c3) (at level 80, right associativity).

(** example: euclidian division
<<
                      r = x;
                      q = 0;
                      while (y <= r) {
                          r = r - y;
                          q = q + 1;
                      }
>>
*)
Definition vx : ident := 25.
Definition vy : ident := 3.
Definition vq : ident := 2.
Definition vr : ident := 4.

Definition euclidean_division : command :=
  Seq (Assign vr (Evar vx))
   (Seq (Assign vq (Econst 0))
     (While (Le (Evar vy) (Evar vr))
       (Seq (Assign vr (Eminus (Evar vr) (Evar vy)))
            (Assign vq (Eplus (Evar vq) (Econst 1)))))).

Definition euclidean_division' : command :=
  vr ::= Evar vx;;
  vq ::= Econst 0;;
  WHILE Le (Evar vy) (Evar vr) DO
     vr ::= Eminus (Evar vr) (Evar vy);; 
     vq ::= Eplus (Evar vq) (Econst 1) 
  END.



(* boolean expression evaluation *)
Fixpoint beval (e: env) (b: bexp) : bool :=
  match b with
    | Eq e1 e2 => 
      if Z_eq_dec (aeval e e1) (aeval e e2) then true else false
    | Le e1 e2 =>
      if Z_le_dec (aeval e e1) (aeval e e2) then true else false 
  end.

(* We now want to give a semantic to our programs *)
Definition update (e: env) (x: ident) (n: Z) : env :=
   fun y => if Z_eq_dec x y then n else e y.
Notation "e +{ x ↦ n }" := (update e x n) (at level 20).
Notation "{}" := (fun x:ident => 0) (at level 20). (* initial state *)



(*******************************)
(** Semantics 1 = Interpreter  *)
(*******************************)

Fixpoint interpreter_v0 (e:env) (c:command) : env :=
  match c with
  | Skip => e
  | Assign x a => update e x (aeval e a)
  | If b ifso ifnot =>
    if beval e b
    then interpreter_v0 e ifso
    else interpreter_v0 e ifnot
  | Seq c1 c2 => ???
  | While b body => e (* wrong *)
  end.

(* The interpreter must be a terminating function, for every inputs!! *)


(* We give 'fuel' to the interpreter. When we don't have enough fuel, we 
  stop the execution. *)
Fixpoint interpreter (e:env) (c:command) (fuel:nat) : option env :=
  match fuel with
    | O => None
    | S p =>
      match c with
        | Skip => Some e
        | Assign x a => Some (update e x (aeval e a))
        | Seq c1 c2 => ???
        | If b ifso ifnot =>
          if beval e b
          then interpreter e ifso p
          else interpreter e ifnot p
        | While b body => 
          if beval e b
          then match interpreter e body p with
                 | Some e' => interpreter e' (While b body) p
                 | None => None
               end
          else Some e
      end
  end.

Definition test_euclidean_division (x y:Z) :=
  match (interpreter 
           ({}+{vx ↦ x}+{vy ↦ y})
           euclidean_division
           50%nat) with
    | None => None
    | Some e => Some (e vq, e vr)
  end.

Compute (test_euclidean_division 13 3).


(*************************************)
(** Semantics 2 = Big-step semantics  *)
(*************************************)

(* (bigstep s1 c s2) holds if the execution of command c
   from a state s1 terminates in a state s2 *)
Inductive bigstep: env -> command -> env -> Prop :=
  | bigstep_skip e
    :(* ============= *)
     bigstep e Skip e

  | bigstep_assign e x a
    :(* ======================== *)
     bigstep e (Assign x a) (e+{x ↦ aeval e a})

  | bigstep_seq e c1 c2 e' e''
     (STEP1: bigstep e c1 e')
     (STEP2: bigstep e' c2 e'')
    :(* ======================== *)
     bigstep e (Seq c1 c2) e''

  | bigstep_if_true e b ifso ifnot e'
     (BEVAL: beval e b = true)
     (STEP: bigstep e ifso e')
    :(* ======================== *)
     bigstep e (If b ifso ifnot) e'

  | bigstep_if_false e b ifso ifnot e'
     (BEVAL: beval e b = false)
     (STEP: bigstep e ifnot e')
    :(* ======================== *)
     bigstep e (If b ifso ifnot) e'

  | bigstep_while_false e b body
     ???

  | bigstep_while_true e b body e' e''
     ??? 

Lemma bigstep_example:
  bigstep
    ({})
    (vx ::= Econst 2;;
     IFB Le (Evar vx) (Econst 1)
       THEN vy ::= Econst 3
       ELSE vy ::= Econst 4
     FI)
    ({}+{vx ↦ 2}+{vy ↦ 4}).
Proof.
  apply bigstep_seq with ({}+{vx ↦ 2}).
  - apply bigstep_assign.
  - apply bigstep_if_false.
    * simpl. auto.
    * apply bigstep_assign.
Qed.



(* A technical lemma used in the next proof *)
Open Scope nat_scope.
Lemma interpreter_step_more : forall n1 n2 e1 c e2,
  n1 <= n2 ->                            
  interpreter e1 c n1 = Some e2 ->
  interpreter e1 c n2 = Some e2.
Proof.
  induction n1; intros n2 e1 c e2 Hl.
  - simpl. congruence.
  - simpl. intros He.
    assert (Hn2: exists n3, n2 = S n3).
      inv Hl; eauto.
    destruct Hn2 as [n3 Hn3]; subst.
    flatten He; go.
    + simpl.
      rewrite (IHn1 n3 e1 c0_1 e); go.
    + simpl.
      rewrite (IHn1 n3 e1 c0 e); go.
Qed.

Theorem equiv_interpreter_bigstep : forall e1 c e2,
  bigstep e1 c e2 <-> exists n, interpreter e1 c n = Some e2.
Proof.
  intros e1 c e2; split.
  - intros H; induction H.
    + exists 1%nat; go.
    + exists 1%nat; go.
    + destruct IHbigstep1 as [n1 IHbigstep1].
      destruct IHbigstep2 as [n2 IHbigstep2].
      assert (Hmax: exists n, n1 <= n /\ n2 <= n).
        exists (max n1 n2); split.
        apply Max.le_max_l.
        apply Max.le_max_r.
      destruct Hmax as [n [Hmax1 Hmax2]].  
      exists (S n); simpl.
      rewrite (interpreter_step_more n1 n e c1 e'); go.
      apply (interpreter_step_more n2 n e' c2 e''); go.
    + destruct IHbigstep as [n IHbigstep].
      exists (S n); go.
    + destruct IHbigstep as [n IHbigstep].
      exists (S n); go.
    + exists 1; go.
    + destruct IHbigstep1 as [n1 IHbigstep1].
      destruct IHbigstep2 as [n2 IHbigstep2].
      assert (Hmax: exists n, n1 <= n /\ n2 <= n).
        exists (max n1 n2); split.
        apply Max.le_max_l.
        apply Max.le_max_r.
      destruct Hmax as [n [Hmax1 Hmax2]].  
      exists (S n).
      simpl.
      rewrite (interpreter_step_more n1 n e body e'); go.
      rewrite (interpreter_step_more n2 n e' (WHILE b DO body END) e''); go.
  - intros [n H].
    revert e1 c e2 H.
    induction n; go.
    destruct c; intros; go.
    + simpl in H. flatten H; go.
    + simpl in H. flatten H; go.
    + simpl in H. flatten H; go.
Qed.



(****************************************)
(** Semantics 3 = Small-step semantics  *)
(****************************************)

(* [step (c,s) (c',s')] holds if, in one elementary step, we evaluate
   the command [c] in the state [s] and it leads to a state [s'] and
   a remaining command [c'] that will be evaluated later. *)
Inductive step: command * env -> command * env -> Prop :=
  | step_assign x e s
    :(* ======================== *)
    step (Assign x e, s) (Skip, s+{x ↦ aeval s e})

  | step_seq_left c1 c2 s c1' s'
     (STEP: step (c1, s) (c1', s'))
    :(* ======================== *)
    step (Seq c1 c2, s) (Seq c1' c2, s')

  | step_seq_skip c s
    :(* ======================== *)
    step (Seq Skip c, s) (c, s)

  | step_if_true s b c1 c2
     (EVAL: beval s b = true)
    :(* ======================== *)
     step (If b c1 c2, s) (c1, s)

  | step_if_false s b c1 c2
     (EVAL: beval s b = false)
    :(* ======================== *)
     step (If b c1 c2, s) (c2, s)

  | step_while_true s b c
     ???

  | step_while_false b c s
     ???

