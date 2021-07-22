(** You need Coq 8.4 and a Coq IDE like CoqIDE or the 
  Proof General emacs-mode *)

(** Our first Coq programs *)

(** In this tutorial will implements simple maps *)
Module Type MAP.
  (** the type of map keys *)
  Parameter key : Type.
  (** the type of map elements *)
  Parameter elt : Type.
  (** the type of maps *)
  Parameter t : Type.

  (** [default] is the default element in a map *)
  Parameter default: elt.

  (** [get m k] returns the elements that is binded with key [k] *)
  Parameter get: t -> key -> elt.

  (** [empty] is a map that binds every keys to [default] *)
  Parameter empty: t.

  (** [set m k e] returns a new map that contains the same
      bindings as map [m] except for key [k] that is now binded with 
      the element [e] *)
  Parameter set: t -> key -> elt -> t.
End MAP.
(** Observe that we use the same keyword for types and operators.
    What we think as types here, are term of type [Type]. *)

(** To implement this interface, we will need some basic data structures *)

(** Peano natural numbers *)
Inductive nat :=
 | O            (* zero is a nat *)
 | S (n:nat)    (* a successor of a nat is a nat *)
.

(** In Ocaml we would have written [type nat = | O | S of nat] *)

(** [nat] is a type. It is inhabited by terms 
    like O, (S O), (S (S O)), ... *)

(** The command [Check] gives the type of a term. *)

Check O.
Check (S (S (S (S O)))).

(** Coq already provides this basic data structure in its
    library. We will remove our version and load Coq's
     version instead. *)

Reset nat.
Require Import Arith.

Check O.
Check (S (S (S (S O)))).
(** Observe that Coq now pretty-prints our terms in 
    the *response* window *)

(** We will also use other data structures like list and string.
    We load the corresponding libraries but we do not detail their
    content here *)
Require Import String.
Require Import List.
Open Scope string_scope. (* Will facilitate string input *)


(** We now begin the implementation of a MAP interface for the
  special case were keys are natural numbers and elements are string *)
Module NatStringMap <: MAP 
                 with Definition key := nat
                 with Definition elt := string.

 Definition key := nat.
 Definition elt := string.

 (** A map will be a list of string [s_0 :: ... :: s_n]  where
   a number [i] is binded with [s_i] if [i <= n] or with the 
   default element otherwise *)  
 Definition t := list string.

 (** Note: a list is either the empty list [nil]
    or a non-empty list of the form [x :: q] with 
      [x] the head of the list and
      [q] the queue of the list
 *)

 (* We arbitrarily choose the empty string as the default element *)
 Definition default := "".

 Fixpoint get (l:list string) (n:nat) : string :=
   match l, n with
     | nil, _ => (* TODO *)
     | x::_, O => (* TODO *)
     | _::q, S m => (* TODO *)
    end.

 Definition empty : t := nil.

 Fixpoint set (l:list string) (n:nat) (s:string) : list string :=
   match l, n with
     | nil, O => (* TODO *)
     | nil, S m => (* TODO *)
     | _ :: q, O => (* TODO *)
     | x :: q, S m => (* TODO *)
    end.
End NatStringMap.


Notation "m [ k ]" := (NatStringMap.get m k) (at level 20).
Notation "m +{ k ↦ e }" := (NatStringMap.set m k e) (at level 20).
Notation "{}" := (NatStringMap.empty) (at level 20).


Compute ({} +{0 ↦ "zero" } +{2 ↦ "two" } +{3 ↦ "three" } [4]).
Compute ({} +{0 ↦ "zero" } +{2 ↦ "two" } +{3 ↦ "three" } [3]).
Compute ({} +{0 ↦ "zero" } +{2 ↦ "two" } +{3 ↦ "three" } [2]).
Compute ({} +{0 ↦ "zero" } +{2 ↦ "two" } +{3 ↦ "three" } [1]).
Compute ({} +{0 ↦ "zero" } +{2 ↦ "two" } +{3 ↦ "three" } [0]).

(** That's a good start but, since we are in Coq, and not in OCaml, we can
  actually make our comments be formal statements *)
Reset MAP.
Require Import Arith.
Require Import String.
Require Import List.
Open Scope string_scope. (* Will facilitate string input *)

Module Type MAP.
  (** the type of map keys *)
  Parameter key : Type.
  (** the type of map elements *)
  Parameter elt : Type.
  (** the type of maps *)
  Parameter t : Type.

  (** [default] is the default element in a map *)
  Parameter default: elt.

  (** [get m k] returns the elements that is binded with key [k] *)
  Parameter get: t -> key -> elt.

  (** the map that binds every keys to [default] *)
  Parameter empty: t.
  Parameter empty_spec: (* TODO *)

  (** [set m k e] returns the a new map that contains the same
      bindings as map [m] except for key [k] that is now binded with 
      the element [e] *)
  Parameter set: t -> key -> elt -> t.
  Parameter get_set_new: forall k m e, 
    get (set m k e) k = (* TODO *)
  Parameter get_set_old: forall k m e k', 
    k'<>k -> get (set m k e) k' = (* TODO *)
  (** Note that [->] means "implies" and [<>] means "different" here. *)
End MAP.

Module NatStringMap <: MAP 
                 with Definition key := nat
                 with Definition elt := string.

 Definition key := nat.
 Definition elt := string.
 Definition t := list string.
 Definition default := "".
 Fixpoint get (l:list string) (n:nat) : string :=
   match l, n with
     | nil, _ => default
     | x::_, O => x
     | _::q, S m => get q m
    end.

 Definition empty : t := nil.

 Fixpoint set (l:list string) (n:nat) (s:string) : list string :=
   match l, n with
     | nil, O => s :: nil
     | nil, S m => default :: set nil m s
     | _ :: q, O => s :: q
     | x :: q, S m => x :: set q m s
    end.

  (** This time we can't end the module so easily because we have proof
   to do ! *)

  (** The command we use to build an interactive proof are called tactics.
    The set of Coq tactics is rather large. We will only expose a limited number
    of them in this tutorial. When the remaining proof is easy we will use
    a custom tactic that force Coq to search alone the proof *)
  (** We call this tactic [go] and we do not explain its content *)
  Ltac go := try congruence; eauto; try econstructor (solve[go]).

  Lemma empty_spec: forall k, get empty k = default.
  Proof.

  Qed. (* [Qed] only succeeds if the system accept our proof *)


  Lemma get_set_new: forall k m e, 
    get (set m k e) k = e.
  Proof.

  Qed.

  Lemma get_set_old: forall k m e k', 
    k'<>k -> get (set m k e) k' = get m k'.
  Proof.

  Qed.
 
End NatStringMap.
  
(* We may have a look at the OCaml extracted version *)
Extraction NatStringMap.

(** In the previous implementation [get] and [set] have a linear 
    complexity (both in time and space) with respect to the size
    of the biggest inserted key. We now seek for an implementation 
    with a logarithmic complexity *)

(* The custom tactic [go] was not exported outside the Module when we 
   closed it. We nos redefine it here. *)
Ltac go := try congruence; eauto; try econstructor (solve[go]).

                                       
(** We need first to build some data structures. The first one is a 
    functional representation of non nul binary numbers *)

Inductive positive :=
  | xH               (* 1 *)
  | xO (p:positive)  (* 2 p *)
  | xI (p:positive)  (* 2 p +1 *)
.

Check xI (xI (xO xH)).
(** represents 1 + 2 * (1 + 2 *  (2 * 1)) = 11 = Ox1011 *)

Module PosStringMap <: MAP 
                 with Definition key := positive
                 with Definition elt := string.

 Definition key := positive.
 Definition elt := string.

 (** We now want do define a tree structure. *)
 Inductive tree :=
 | Leaf
 | Node (a:string) (l r:tree).

 Definition t := tree.

 Definition default := "".

 Fixpoint get (t: tree) (p:positive) :=
   match t, p with
     | Leaf, _ => (* TODO *)
     | Node a l r, xH => (* TODO *)
     | Node a l r, xO p => (* TODO *)
     | Node a l r, xI p => (* TODO *)
   end.

 Definition empty : t := Leaf.

  Fixpoint set (t:tree) (p:positive) (s:string) :=
  match t, p with
    | Leaf, xH => (* TODO *) 
    | Leaf, xO p => (* TODO *) 
    | Leaf, xI p => (* TODO *) 
    | Node a l r, xH => (* TODO *) 
    | Node a l r, xO p => (* TODO *) 
    | Node a l r, xI p => (* TODO *) 
  end.

  Lemma empty_spec: forall k, get empty k = default.
  Proof.
    go.
  Qed. 

  Lemma get_set_new: forall k m e, 
    get (set m k e) k = e.
  Proof.
    induction k; destruct m; simpl; go.
  Qed.

  Lemma get_set_old: forall k m e k', 
    k'<>k -> get (set m k e) k' = get m k'.
  Proof.
    induction k; destruct m; destruct k'; simpl; go;
    intros; rewrite IHk; go.
  Qed.
 
End PosStringMap.

Notation "m [ k ]" := (PosStringMap.get m k) (at level 20).
Notation "m +{ k ↦ e }" := (PosStringMap.set m k e) (at level 20).
Notation "{}" := (PosStringMap.empty) (at level 20).

Definition p1 := xH.
Definition p2 := xO xH.
Definition p3 := xI xH.
Definition p4 := xO (xO xH).
Definition p6 := xO (xI xH).

Compute ({} +{p2 ↦ "two" } +{p3 ↦ "three" } +{p6 ↦ "six" } [p6]).
Compute ({} +{p2 ↦ "two" } +{p3 ↦ "three" } +{p6 ↦ "six" } [p4]).
Compute ({} +{p2 ↦ "two" } +{p3 ↦ "three" } +{p6 ↦ "six" } [p3]).
Compute ({} +{p2 ↦ "two" } +{p3 ↦ "three" } +{p6 ↦ "six" } [p2]).
Compute ({} +{p2 ↦ "two" } +{p3 ↦ "three" } +{p6 ↦ "six" } [p1]).


(** Inductive predicates *)

(** [inf_log p n] holds iff p holds less then n bits *)
Inductive inf_log : positive -> nat -> Prop :=
| Inf_log_xH: forall n, inf_log xH (S n)
| Inf_log_xO: forall p n, inf_log p n -> inf_log (xO p) (S n)
| Inf_log_xI: forall p n, inf_log p n -> inf_log (xI p) (S n).

Lemma inf_log_10_4: inf_log (xO (xI (xO xH))) 4.
Proof.

Qed.


(** The corresponding proof tree:

------------------------------[Inf_log_xH]
         inf_log xH 1
------------------------------[Inf_log_xO]
     inf_log (xO xH)) 2
------------------------------[Inf_log_xI]
   inf_log (xI (xO xH)) 3
------------------------------[Inf_log_xO]
 inf_log (xO (xI (xO xH))) 4
*)


(** A custom tactic to inversion an inductive hypothesis *)
Ltac inv H := inversion H; subst; clear H.

Lemma not_inf_log_8_3: inf_log (xO (xO (xO xH))) 3 -> False.
Proof.

Qed.


(** Dependent types *)
Inductive bin (n:nat) :=
| Bin (p:positive) (h:inf_log p n).

Check Bin. 
(** [Bin] takes three arguments but the first one can always be inferred from
  the others. *)
Arguments Bin {n} p h.
(** Now Coq will automatically provide the first argument *)

(** 10 can be given the type [(bin 4)] *)
Definition bin_10_4 : bin 4 := Bin (xO (xI (xO xH))) inf_log_10_4.

(** 10 can also be given the type [(bin 5)] but we need a new proof *)
Lemma inf_log_10_5: inf_log (xO (xI (xO xH))) 5.
Proof.

Qed.

Definition bin_10_5 : bin 5 := Bin (xO (xI (xO xH))) inf_log_10_5.


(** We want now to defined the successor of a binary number *)

(** We need to do it first on positives numbers *)
Fixpoint psucc (p:positive) : positive :=
  match p with
    | xH => xO xH
    | xO p => xI p
    | xI p => xO (psucc p)
  end.

(** Some auxiliaries lemmas are requires *)
Lemma inf_log_S: forall p n,
  inf_log p n ->
  inf_log p (S n).
Proof.

Qed.
Hint Resolve inf_log_S. 
(* we add this new lemma to the automation knowledge base *)

Lemma inf_log_psucc: forall p n,
  inf_log p n ->
  inf_log (psucc p) (S n).
Proof.

Qed.
Hint Resolve inf_log_psucc.

Definition bsucc (n:nat) (b:bin n) : bin (S n) :=
  match b with
    | Bin p h => Bin (psucc p) (inf_log_psucc p n h)
  end.

(** After extraction, proofs disappear *)
Recursive Extraction bsucc.


(** Proof scripts give just a convenient way to build proof term.
  Here is a direct proof term for the previous lemma [inf_log_S].
  Note: very few Coq users have to do that... *)
Fixpoint inf_log_S' (p:positive) (n:nat) (h:inf_log p n) : inf_log p (S n) :=
  match h in (inf_log p1 n1) return inf_log p1 (S n1)  with
    | Inf_log_xH n0 => Inf_log_xH (S n0)
    | Inf_log_xO p0 n0 h0 => Inf_log_xO p0 (S n0) (inf_log_S' p0 n0 h0)
    | Inf_log_xI p0 n0 h0 => Inf_log_xI p0 (S n0) (inf_log_S' p0 n0 h0)
  end.

Lemma inf_log_S'': forall p n,
  inf_log p n ->
  inf_log p (S n).
Proof.
  induction 1; go.
Defined. (** Small trick: we have to build a 'transparent' proof *)

Lemma inf_log_S_same: inf_log_S' = inf_log_S''.
Proof.
  go.
Qed.

(** On the contrary, we can also program every function using a
  proof script!
  Note: be careful with proof automation then... *)
Definition bsucc' (n:nat) (b:bin n) : bin (S n).
Proof.

Defined.

Lemma bsucc_same: forall n b, bsucc n b = bsucc' n b.
Proof.
  go.
Qed.

(** In Coq every term has a type *)
Check (O : nat).
Check (nat : Set).
Check (Set : Type).
Check (Type : Type). 

Check (inf_log (xO (xI (xO xH))) 5 : Prop).
Check (Prop : Type).
Check (Type : Type). 

(** We finish with a few examples of CIC term to illustrate the various kind
  of type dependency the system allows. 
  [fun x:T => t] is the lambda abstraction to build function. *)

Check ((fun n:nat => bin n) : (nat -> Set)).
(** [->] is just syntactic sugar! *) 
Check ((fun n:nat => bin n) : (forall _:nat, Set)).

Check ((fun n:nat => n<>n) : (forall _:nat, Prop)).

Check ((fun P:Prop => (P -> False)) : (forall _:Prop, Prop)).

Check ((fun (n:nat) (h:n<>O) => pred n) : (forall (n:nat) (h:n<>O), nat)).

Check ((fun (T:Type) => list T) : (forall _:Type, Type)).

Check ((fun (T:Type) (x:T) => x) : (forall (T:Type) (x:T), T)).

Check ((fun (n:nat) => Bin xH (Inf_log_xH n)) : (forall (n:nat), bin (S n))).

Check ((fun (n:nat) => Inf_log_xH n) : (forall (n:nat), inf_log xH (S n))).