(** Ce module definit un compilateur pour le langage IMP.  Il produit
  du code pour une machine virtuelle (un petit sous-ensemble de la
  machine virtuelle Java JVM).  Nous prouvons que ce compilateur
  est correct car il preserve la semantique des programmes source. *)
Require Import MSMLib.
Require Import Bool.             (**r La theorie des booleens *)
Require Import List.             (**r La theorie des listes *)
Require Import Arith.            (**r La theorie des entiers naturels (type [nat]) *)
Require Import ZArith.           (**r La theorie des entiers relatifs (type [Z]) *)
Require Import Sequences.        (**r Une theorie des suites de transitions *)
Require Import semantics.        (**r Notre travail précdent sur la sémantique d'un
                                      petit langage impératif *)

(** * 1. La machine virtuelle. *)

(** La machine opere sur un code [c] (une liste fixee d'instructions) et
  trois composants qui varient au cours du temps:
- un compteur de programme (PC), denotant une position dans le code [c]
- un etat memoire qui donne les valeurs entieres des variables
- une pile d'evaluation, contenant des valeurs entieres.
*)

Inductive instruction: Type :=
  | Iconst: Z -> instruction       (**r empiler l'entier [n] sur la pile *)
  | Ivar: ident -> instruction     (**r empiler la valeur de la variable [x] *)
  | Isetvar: ident -> instruction  (**r depiler un entier et l'affecter a la variable [x] *)
  | Iadd: instruction              (**r depiler [n2], depiler [n1], empiler [n1+n2] *)
  | Isub: instruction              (**r depiler [n2], depiler [n1], empiler [n1-n2] *)
  | Imul: instruction              (**r depiler [n2], depiler [n1], empiler [n1*n2] *)
  | Idiv: instruction              (**r depiler [n2], depiler [n1], empiler [n1/n2] *)
  | Ibranch_forward: nat -> instruction   (**r sauter [ofs] instructions en avant *)
  | Ibranch_backward: nat -> instruction  (**r sauter [ofs] instructions en arriere *)
  | Ibeq: nat -> instruction       (**r depiler [n2], depiler [n1], sauter [ofs] en avant si [n1=n2] *)
  | Ibne: nat -> instruction       (**r depiler [n2], depiler [n1], sauter [ofs] en avant si [n1<>n2] *)
  | Ible: nat -> instruction       (**r depiler [n2], depiler [n1], sauter [ofs] en avant si [n1<=n2] *)
  | Ibgt: nat -> instruction       (**r depiler [n2], depiler [n1], sauter [ofs] en avant si [n1>n2] *)
  | Ihalt: instruction.            (**r arreter la machine *)

Definition code := list instruction.

(** [code_at C pc = Some i] si [i] est l'instruction a la position [pc]
dans la liste d'instructions [C]. *)

Fixpoint code_at (C: code) (pc: nat) : option instruction :=
  match C, pc with
  | nil, _ => None
  | i :: C', O => Some i
  | i :: C', S pc' => code_at C' pc'
  end.

(** Une pile de la machine est une liste de valeurs entieres.
    [n :: s] est la pile obtenue en empilant [n] au sommet de la pile [s]. *)

Definition stack := list Z.

(** L'etat de la machine est un triplet (PC, pile, etat memoire). *)
Definition machine_state := (nat * stack * env)%type.

Definition initial_state : machine_state :=
  (0, nil, {}).

(** Interpréteur *)

Open Scope nat_scope.
Definition next (ins:instruction) (i:nat) (s:stack) (m:env) : option machine_state := 
  match ins, s with 
    | Iconst n, _ => Some (i+1,n::s,m)
    | Ivar x, _ => Some (i+1,(m x)::s,m) 
    | Isetvar x, n::s => Some (i+1,s,m +{ x ↦ n }) 
    | Iadd, n2::n1::s => Some (i+1,(n1+n2)%Z::s,m) 
    | Isub, n2::n1::s => Some (i+1,(n1-n2)%Z::s,m) 
    | Imul, n2::n1::s => Some (i+1,(n1*n2)%Z::s,m) 
    | Idiv, n2::n1::s => Some (i+1,(n1/n2)%Z::s,m)
    | Ibranch_forward ofs, _ => Some ((i+ofs+1)%nat,s,m) 
    | Ibranch_backward ofs, _ => Some ((i-ofs)%nat,s,m) 
    | Ibeq ofs, n2::n1::s => 
      if Z_eq_dec n1 n2 
      then Some ((i+ofs+1)%nat,s,m)
      else Some (i+1,s,m) 
    | Ibne ofs, n2::n1::s => 
      if Z_eq_dec n1 n2 
      then Some (i+1,s,m) 
      else Some ((i+ofs+1)%nat,s,m) 
    | Ible ofs, n2::n1::s =>
      if Z_le_dec n1 n2 
      then Some ((i+ofs+1)%nat,s,m) 
      else Some (i+1,s,m) 
    | Ibgt ofs, n2::n1::s => 
      if Z_le_dec n1 n2 
      then Some (i+1,s,m) 
      else Some ((i+ofs+1)%nat,s,m) 
    | _, _ => None 
  end.

Fixpoint interpreter (c:code) (st:machine_state) (fuel:nat) : option env :=
  match fuel with
    | O => None
    | S p =>
      let '(i,s,m) := st in
      match code_at c i with
        | Some ins =>
          match ins, s with
            | Ihalt, nil => Some m
            | _, _ => 
              match next ins i s m with
                | Some st' => interpreter c st' p
                | None => None
              end
          end
        | None => None
      end
  end.


(** La semantique de la machine est donnee en style "petits pas",
comme une relation de transition entre deux etats machine.  On a une
regle de transition pour chaque sorte d'instruction, a l'exception de
[Ihalt] qui ne fait pas de transition.  *)


Open Scope nat_scope.
          (**r Interpreter [+], [-], etc, comme les operations du type [nat] *)






Inductive step (c:code) : machine_state -> machine_state -> Prop :=
| step_Iconst i s m n
  (INS: code_at c i = Some (Iconst n))
  :(* =============================== *)
  step c (i,s,m) (i+1,n::s,m)
| ???



Inductive iterstep (c:code) : machine_state -> env -> Prop :=
| iterstep_def st i m
  (HALT: code_at c i = Some Ihalt)
  (STAR: star (step c) st (i,nil,m))
  :(* =============================== *)
  iterstep c st m.

(* [star R] ( ou R* ) représente la fermeture transitive reflexive d'une relation R

                R x y         (R* x y)   (R* y z)
  --------     --------      -------------------
   R* x x       R* x y            R* x z

*)
  

(* State and prove the equivalence between both semantics *)

Lemma step_equiv_next: forall c i s m st',
  step c (i,s,m) st' <-> 
    (exists ins, code_at c i = Some ins /\
                 next ins i s m = Some st').
Proof.
  split.
  - intros H.
    inv H; go.
    + exists (Ibeq ofs); split; auto.
      simpl; flatten; go.
    + exists (Ibeq ofs); split; auto.
      simpl; flatten; go.
    + exists (Ibne ofs); split; auto.
      simpl; flatten; go.
    + exists (Ibne ofs); split; auto.
      simpl; flatten; go.
    + exists (Ible ofs); split; auto.
      simpl; flatten; go.
    + exists (Ible ofs); split; auto.
      simpl; flatten; go.
    + exists (Ibgt ofs); split; auto.
      simpl; flatten; go.
    + exists (Ibgt ofs); split; auto.
      simpl; flatten; go.
  - intros H.
    destruct H as [ins [Hc Hn]].
    unfold next in Hn; flatten Hn; go.
Qed.

Lemma step_iterstep_implies_iterstep: forall c st1 st2 m,
  step c st1 st2 ->
  iterstep c st2 m -> 
  iterstep c st1 m.
Proof.
  intros c st1 st2 m H H0.
  inv H0; go.
Qed.

Lemma interpreter_equiv_iterstep: forall c st m,
  iterstep c st m <-> exists fuel, interpreter c st fuel = Some m.
Proof.
  split.
  - intros H; inv H.
    induction STAR.
    + exists 1%nat; simpl; go.
    + assert (IH: exists fuel, interpreter c b fuel = Some m).
        apply IHSTAR with i; auto.
      destruct IH as [fuel IH].
      destruct a as [[i1 s1] m1].
      rewrite step_equiv_next in H; auto.
      destruct H as [ins [Hc Hn]].      
      exists (S fuel); simpl.
      rewrite Hc.
      rewrite Hn.
      rewrite IH.
      flatten.
      simpl in Hn.
      congruence.
  - intros H; destruct H as [fuel H].
    revert st m H.
    induction fuel; go.
    intros st m H.
    simpl in H.
    destruct st as [[i1 s1] m1].
    destruct (code_at c i1) eqn:Hc; try congruence.
    destruct (next i i1 s1 m1) eqn:Hn.
    + assert (Hs: step c (i1,s1,m1) m0).
        rewrite step_equiv_next; go.
      assert (Hi: iterstep c m0 m).
        apply IHfuel.
        flatten H.
        simpl in Hn.
        congruence.
      apply step_iterstep_implies_iterstep with m0; auto.  
    + flatten H.
      go.
Qed.

(** Il y a plusieurs situation ou la machine se bloque (erreur a
l'execution) et ou aucune transition ne peut s'effectuer.  Par
exemple:
- Si le PC sort du code [pc >= length C], on a [code_at C pc = None]
  et aucune regle de transition ne s'applique
- S'il n'y a pas assez de valeurs sur la pile pour les instructions qui
  depilent une ou deux valeurs.  Exemple: [Iadd] sur une pile vide.

Cependant, il y a un cas ou la machine est plus tolerante que le
langage IMP: l'instruction [Idiv] ne plante pas si le diviseur est
[0].  Dans ce cas, le resultat est [0] car c'est ainsi que Coq definit
la division par zero.
*)

(** Comme toujours en semantique "petits pas", nous formons des suites
de transitions de la machine pour definir le comportement d'un code.
Toutes les executions commencent avec [pc = 0] et une pile vide.  La
machine s'arrete sans erreur lorsque [pc] pointe vers une instruction
[Ihalt] et la pile est vide. *)

Definition mach_terminates (C: code) (final: env) :=
  exists pc,
  code_at C pc = Some Ihalt /\
  star (step C) initial_state (pc, nil, final).


(** * 2. Le compilateur *)

(** Le code engendre pour une expression arithmetique [a]
- s'execute en sequence (pas de branchements)
- depose la valeur de [a] au sommet de la pile
- preserve l'etat memoire.

C'est la traduction bien connue en "notation polonaise inverse" (RPN).

Note: [::] est le "cons" des listes et [++] est la concatenation de listes.
*)

Fixpoint compile_aexp (a: aexp) : code :=
  match a with
  | Econst n => Iconst n :: nil
  | Evar v => Ivar v :: nil
  | Eplus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Iadd :: nil
  | Eminus a1 a2 => compile_aexp a1 ++ compile_aexp a2 ++ Isub :: nil
  end.

(** Exemples de compilations. *)

Compute (compile_aexp (Eplus (Evar vx) (Econst 1))).

Compute (compile_aexp (Eminus (Econst 3) (Econst 1))).

(** Le code [compile_bexp b cond ofs] engendre pour une expression booleenne [b]
- saute par dessus les [ofs] instructions qui le suivent si [b] s'evalue en le booleen [cond]
- s'execute en sequence si [b] s'evalue en la negation de [cond]
- preserve la pile et l'etat memoire.
*)
Fixpoint compile_bexp (b: bexp) (cond: bool) (ofs: nat) : code :=
  match b with
  | Eq a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ibeq ofs :: nil else Ibne ofs :: nil)
  | Le a1 a2 =>
      compile_aexp a1 ++ compile_aexp a2 ++
      (if cond then Ible ofs :: nil else Ibgt ofs :: nil)
  end.

(** Exemples. *)
Compute (compile_bexp (Eq (Evar vx) (Econst 1)) true 42).

(** Le code produit pour une commande [c]
- modifie l'etat memoire comme prescrit par la semantique de [c]
- preserve la pile
- peut contenir des branchements, mais termine toujours sur l'instruction
  qui suit immediatement le code engendre.

A nouveau, on se reportera aux transparents pour une explication des
offsets de branchements.
*)

Fixpoint compile_com (c: command) : code :=
  match c with
  | Skip =>
      nil
  | Assign id a =>
      compile_aexp a ++ Isetvar id :: nil
  | Seq c1 c2 =>
      compile_com c1 ++ compile_com c2
  | If b ifso ifnot =>
      let code_ifso := compile_com ifso in
      let code_ifnot := compile_com ifnot in
      compile_bexp b false (length code_ifso + 1)
      ++ code_ifso
      ++ Ibranch_forward (length code_ifnot)
      :: code_ifnot
  | While b body =>
      ???
  end.

(** Le code compile pour un programme complet [p] (une commande) est
similaire, mais termine proprement sur une instruction [Ihalt]. *)

Definition compile_program (p: command) : code :=
  compile_com p ++ Ihalt :: nil.

(** Exemples de compilations: *)

Compute (compile_program (Assign vx (Eplus (Evar vx) (Econst 1)))).

Compute (compile_program (While (Eq (Econst 0) (Econst 0)) Skip)).

Compute (compile_program (If (Eq (Evar vx) (Econst 1)) (Assign vx (Econst 0)) Skip)).

Compute (compile_program euclidean_division).

Definition test_compiled_euclidean_division (x y:Z) :=
  match (interpreter 
           (compile_program euclidean_division)
           (0,nil,{}+{vx ↦ 13}+{vy ↦ 3}) 100) with
    | None => None
    | Some e => Some (e vq, e vr)
  end.

Compute (test_compiled_euclidean_division 13 3).

(** * 3. Preuve de preservation semantique utilisant la semantique naturelle *)

(** ** Resultats auxiliaires sur les suites d'instructions. *)

(** Pour raisonner sur l'execution du code produit par le compilateur,
nous avons besoin d'examiner des morceaux de code [C2] qui sont a la
position [pc] dans un code plus grand [C = C1 ++ C2 ++ C3].  Cette
situation est capturee par le predicat [codeseq_at C pc C2]
ci-dessous. *)

Inductive codeseq_at: code -> nat -> code -> Prop :=
  | codeseq_at_intro: forall C1 C2 C3 pc,
      pc = length C1 ->
      codeseq_at (C1 ++ C2 ++ C3) pc C2.

(** Nous montrons un ensemble de proprietes evidentes de [code_at] et
de [codeseq_at], que nous mettons dans une "hint database" pour que
Coq puisse les utiliser automatiquement. *)

Lemma code_at_app:
  forall i c2 c1 pc,
  pc = length c1 ->
  code_at (c1 ++ i :: c2) pc = Some i.
Proof.
  induction c1; simpl; intros; subst pc; auto.
Qed.

Lemma codeseq_at_head:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  code_at C pc = Some i.
Proof.
  intros. inv H. simpl. apply code_at_app. auto.
Qed.

Lemma codeseq_at_tail:
  forall C pc i C',
  codeseq_at C pc (i :: C') ->
  codeseq_at C (pc + 1) C'.
Proof.
  intros. inv H. 
  assert (EQ: C1 ++ (i :: C') ++ C3 =  C1 ++ (i :: nil) ++ C' ++ C3) by auto.
  rewrite EQ.
  rewrite <- app_ass. 
  apply codeseq_at_intro.
  rewrite app_length. auto.
Qed. 

Lemma codeseq_at_app_left:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C pc C1.
Proof.
  intros. inv H. rewrite app_ass. 
  go.
Qed.

Lemma codeseq_at_app_right:
  forall C pc C1 C2,
  codeseq_at C pc (C1 ++ C2) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inv H. rewrite app_ass. rewrite <- app_ass. 
  apply codeseq_at_intro.
  rewrite app_length. auto.
Qed.

Lemma codeseq_at_app_right2:
  forall C pc C1 C2 C3,
  codeseq_at C pc (C1 ++ C2 ++ C3) ->
  codeseq_at C (pc + length C1) C2.
Proof.
  intros. inv H. repeat rewrite app_ass. rewrite <- app_ass. 
  apply codeseq_at_intro.
  rewrite app_length. auto.
Qed.

(* Un peu d'automatisation pour la suite *)
Hint Resolve codeseq_at_head codeseq_at_tail codeseq_at_app_left 
    codeseq_at_app_right codeseq_at_app_right2.

Ltac normalize :=
  repeat rewrite app_length; repeat rewrite plus_assoc; simpl.

(** ** Correction du code produit pour les expressions *)

(** Rappelons-nous la specification informelle que nous avions donnee
pour le code engendre pour une expression arithmetique [a].  Il est
cense:
- s'executer en sequence (pas de branchements)
- deposer la valeur de [a] au sommet de la pile
- preserver l'etat memoire.

Nous prouvons maintenant que le code [compile_aexp a] remplit ce contrat.
La preuve est une recurrence elegante sur la derivation d'evaluation
[eval m a n]. *)

Open Scope nat_scope.          (**r Interpreter [+], [-], etc, comme les operations du type [nat] *)

Lemma compile_aexp_correct:
  forall C m a n, aeval_rel m a n ->
  forall pc stk,
  codeseq_at C pc (compile_aexp a) ->
  star (step C)
       (pc, stk, m)
       (pc + length (compile_aexp a), n :: stk, m).
Proof.
  intros C m a n H; induction H; intros.
  - (* const *)
    go.
  - (* var *)
    simpl in *.
    apply star_one. 
    eapply step_Ivar; eauto.
  - (* plus *)
    simpl in *.
    eapply star_trans.
    apply IHaeval_rel1; eauto. 
    eapply star_trans.
    apply IHaeval_rel2; eauto. 
    apply star_one. 
    normalize. 
    apply step_Iadd. eauto. 
  - (* minus *)
    eapply star_trans.
    apply IHaeval_rel1; eauto. 
    eapply star_trans.
    apply IHaeval_rel2; eauto. 
    apply star_one. simpl; normalize. 
    apply step_Isub. eauto. 
Qed.


Lemma compile_aexp_correct_fun:
  forall C m a n, aeval m a = n ->
  forall pc stk,
  codeseq_at C pc (compile_aexp a) ->
  star (step C)
       (pc, stk, m)
       (pc + length (compile_aexp a), n :: stk, m).
Proof.
  intros.
  apply aeval_rel_equiv_aeval in H.
  apply compile_aexp_correct; auto.
Qed.

(** Voici la preuve correspondante pour la compilation des expressions
booleennes. *)

Lemma compile_bexp_correct:
  forall C m b v, beval m b = v ->
  forall cond ofs pc stk,
  codeseq_at C pc (compile_bexp b cond ofs) ->
  star (step C)
       (pc, stk, m)
       (pc + length (compile_bexp b cond ofs)
        + if bool_dec v cond then ofs else 0, stk, m).
Proof.
  induction b; intros v H; simpl in H; flatten H; intros.
  - (* Eq true *)
    eapply star_trans. 
    apply compile_aexp_correct_fun with (a := a1); eauto.     
    eapply star_trans.
    apply compile_aexp_correct_fun with (a := a2); eauto. 
    apply star_one. normalize.
    destruct cond.
    + simpl in *.
      flatten.
      apply step_Ibeq_true with ofs; eauto. 
      normalize.
      go.
    + simpl in *.
      flatten.
      normalize.
      apply step_Ibne_false with ofs; eauto. 
  - (* Eq false *)
    eapply star_trans. 
    apply compile_aexp_correct_fun with (a := a1); eauto. 
    eapply star_trans.
    apply compile_aexp_correct_fun with (a := a2); eauto. 
    apply star_one. normalize.
    destruct cond.
    + simpl in *.
      apply step_Ibeq_false with ofs; eauto. 
      flatten. normalize. go.
    + simpl in *.
      apply step_Ibne_true with ofs; eauto. 
      flatten. normalize. go.
  - (* Le true *)
    eapply star_trans. 
    apply compile_aexp_correct_fun with (a := a1); eauto. 
    eapply star_trans.
    apply compile_aexp_correct_fun with (a := a2); eauto. 
    apply star_one. normalize.
    destruct cond.
    + simpl in *.
      apply step_Ible_true with ofs; eauto. 
      flatten; normalize; go.
    + simpl in *.
      apply step_Ibgt_false with ofs; eauto. 
      flatten; normalize; go.
  - (* Le false *)
    eapply star_trans. 
    apply compile_aexp_correct_fun with (a := a1); eauto. 
    eapply star_trans.
    apply compile_aexp_correct_fun with (a := a2); eauto. 
    apply star_one. normalize.
    destruct cond.
    + simpl in *.
      apply step_Ible_false with ofs; eauto. 
      flatten; normalize; go.
    + simpl in *.
      apply step_Ibgt_true with ofs; eauto. 
      omega.
      flatten; normalize; go.
Qed.
 

(** ** Correction du code compile pour une commande qui termine *)

Lemma compile_com_correct_terminating:
  forall C m c m',
  bigstep m c m' ->
  forall stk pc,
  codeseq_at C pc (compile_com c) ->
  star (step C)
       (pc, stk, m)
       (pc + length (compile_com c), stk, m').
Proof.
  intros C m c m' H; induction H; intros stk pc AT.
  - (* Skip *)
    simpl in *. 
    replace (pc+0) with pc by go.
    apply star_refl.
  - (* Assign *)
    simpl in *.
    eapply star_trans.
    apply compile_aexp_correct_fun with (a:=a); eauto.
    apply star_one. 
    normalize. 
    go.
  - (* Seq *)
    simpl in *.
    eapply star_trans. 
    + apply IHbigstep1. eauto. 
    + normalize. apply IHbigstep2. eauto. 
  - (* If true *)
    simpl in *.
    set (code1 := compile_com ifso) in *.
    set (codeb := compile_bexp b false (length code1 + 1)) in *.
    set (code2 := compile_com ifnot) in *.
    eapply star_trans. 
    apply compile_bexp_correct 
    with (b := b) (v := true) (cond := false) (ofs := length code1 + 1);
      eauto. 
    simpl. rewrite plus_0_r. normalize.
    eapply star_trans. apply IHbigstep. eauto. 
    apply star_one. 
    apply step_Ibranch_forward with (length code2). 
    simpl. 
    fold codeb; omega.
    eauto. 
  - (* If false *)
    simpl in *.
    set (code1 := compile_com ifso) in *.
    set (codeb := compile_bexp b false (length code1 + 1)) in *.
    set (code2 := compile_com ifnot) in *.
    eapply star_trans. 
    apply compile_bexp_correct
    with (b := b) (v := false) (cond := false) (ofs := length code1 + 1);
      eauto. 
    simpl. normalize.
    replace (pc + length codeb + length code1 + S(length code2))
    with (pc + length codeb + length code1 + 1 + length code2).
    apply IHbigstep. eauto. omega. 
  - (* While false *)
    simpl in *. 
    eapply star_trans.
    apply compile_bexp_correct
    with (b := b) (v := false) (cond := false) (ofs := length (compile_com body) + 1);
      eauto.
    simpl. normalize. apply star_refl.
  - (* While true *)
    apply star_trans with (pc, stk, e').
    simpl in *.
    eapply star_trans.
    apply compile_bexp_correct
    with (b := b) (v := true) (cond := false) (ofs := length (compile_com body) + 1);
      eauto. 
    simpl. rewrite plus_0_r.
    eapply star_trans. apply IHbigstep1. eauto. 
    apply star_one.
    apply step_Ibranch_backward with
     (length (compile_bexp b false (length (compile_com body) + 1)) +
      length (compile_com body)). omega.
    simpl. eauto.
    apply IHbigstep2. auto.
Qed.

Theorem compile_program_correct_terminating:
  forall c final_store,
  bigstep ({}) c final_store ->
  mach_terminates (compile_program c) final_store.
Proof.
  intros. unfold compile_program, mach_terminates.   
  exists (length (compile_com c)); split.
  apply code_at_app. auto.
  apply compile_com_correct_terminating with (pc := 0). auto. 
  apply codeseq_at_intro with (C1 := nil). auto.
Qed.

(** Exercice pour les rapides. 

On souhaite étendre le langage des expressions booléennes avec
  la négation et la conjonction booléenne. 

    Inductive bexp : Type :=
    | Eq: aexp -> aexp -> bexp
    | Le: aexp -> aexp -> bexp 
    | Neg : bexp -> bexp            (* nouveau ! *)
    | And : bexp -> bexp -> bexp.  (* nouveau ! *)
  
 1) Modifiez en conséquence la fonction [beval] du fichier précédent,
    en vous appuyant sur les fonctions prédéfinies:
     negb : bool -> bool := ... (* negation booleenne *)
     andb : bool -> bool -> bool := ... (* conjonction booleenne *)


 2) Modifiez en conséquence la fonction [compile_bexp] précédente,
    sans étendre le langage cible avec de nouvelles instructions.

 3) Complétez les preuves ?

*)


