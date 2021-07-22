Require Export List.

Ltac caseeq t := generalize (refl_equal t); pattern t at -1; case t.

Inductive comp : Set :=
  | Lt : comp
  | Eq : comp
  | Gt : comp.

Module Type OrderedType.

  Parameter t : Set.
  Parameter compare : t -> t -> comp.

  Parameter compare_eq_prop1 : forall x y, compare x y = Eq -> x = y.
  Parameter compare_eq_prop2 : forall x y, x = y -> compare x y = Eq.

  Definition lt (x y:t) : Prop := compare x y = Lt.
  Parameter lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y, lt x y -> x<>y.

  Hint Resolve lt_trans lt_not_eq compare_eq_prop1 compare_eq_prop2.

End OrderedType.

Module NatOrderedType <: OrderedType.

  Definition t := nat.
  Fixpoint compare (n m:nat) {struct n} : comp :=
    match n,m with
      | O,O => Eq
      | O,_ => Lt
      | S _,O => Gt
      | S p,S q => compare p q 
  end.

  Definition lt (x y:t) : Prop := compare x y = Lt.

  Lemma compare_eq_prop1 : forall x y, compare x y = Eq -> x = y.
  Proof.
    induction x; destruct y; simpl; intros; auto.
    discriminate.
    discriminate.
  Qed.

  Lemma compare_eq_prop2 : forall x y, x = y -> compare x y = Eq.
  Proof.
    induction x; destruct y; simpl; intros; auto.
    discriminate.
    discriminate.
  Qed.

  Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt; induction x; destruct y; destruct z; simpl; auto; intros.
    discriminate.
    discriminate.
    eauto.
  Qed.

  Lemma lt_not_eq : forall x y, lt x y -> x<>y.
  Proof.
    unfold lt; induction x; destruct y; simpl; auto; intros.
    discriminate.
  Qed.

End NatOrderedType.


Module Type FSet.

  Parameter elt : Set.
  Parameter t : Set.
  Parameter empty : t.
  Parameter mem : elt -> t -> bool.
  Parameter elements : t -> list elt.
  Parameter add : elt -> t -> t.
  Parameter remove : elt -> t -> t.
  Parameter union : t -> t -> t.
  Parameter inter : t -> t -> t.

  Definition In_set : elt -> t -> Prop := fun x s => In x (elements s).

  Parameter empty_prop : forall x, ~ In_set x empty.
  Parameter mem_prop : forall x s, In_set x s <-> mem x s = true.
  Parameter add_prop : forall a s x, In_set x (add a s) <-> (x=a \/ In_set x s).
  Parameter remove_prop : forall a s x, In_set x (remove a s) <-> (x<>a /\ In_set x s).
  Parameter union_prop : forall s1 s2 x, 
    In_set x (union s1 s2) <-> (In_set x s1 \/ In_set x s2).
  Parameter inter_prop : forall s1 s2 x, 
    In_set x (inter s1 s2) <-> (In_set x s1 /\ In_set x s2).

End FSet.

Module Make (O:OrderedType) : FSet with Definition elt := O.t.

  Definition elt : Set := O.t.

  Definition Inf x l : Prop := forall y, In y l -> O.lt x y.

  Inductive sorted : list elt -> Prop :=
  | sorted_nil : sorted nil
  | sorted_cons : forall a l, 
    Inf a l -> sorted l -> sorted (a::l).
  Hint Constructors sorted.

  Record sorted_list : Set := sl { 
    content :> list elt;
    content_sorted : sorted content
  }.

  Definition t := sorted_list.

  Definition elements (l:t) : list elt := l.(content).
  Definition In_set : elt -> t -> Prop := fun x s => In x (elements s).

  Fixpoint mem_aux (x:elt) (l:list elt) {struct l} : bool :=
    match l with
      | nil => false
      | y::q =>
        match O.compare y x with
          | Lt => mem_aux x q
          | Eq => true
          | Gt => false
        end
    end.

  Lemma mem_aux_prop1 : forall x l,
    mem_aux x l = true -> In x l.
  Proof.
    induction l; simpl.
    discriminate.
    caseeq (O.compare a x); intros; auto.
    discriminate.
  Qed.

  Lemma mem_aux_prop2 : forall x l,
    sorted l -> In x l -> mem_aux x l = true.
  Proof.
    induction 1; simpl; intros; auto.
    elim H.
    destruct H1; subst.
    rewrite O.compare_eq_prop2; auto.
    caseeq (O.compare a x); auto; intros.
    assert (HH:=H x H1).
    unfold O.lt in HH.
    rewrite H2 in HH.
    discriminate.
  Qed.

  Definition mem (x:elt) (l:t) : bool := mem_aux x l.

  Lemma mem_prop : forall x s, In_set x s <-> mem x s = true.
  Proof.
    intros; unfold mem, In_set, elements.
    destruct s as [l l_sorted].
    simpl.
    split.
    apply mem_aux_prop2; auto.
    apply mem_aux_prop1.
  Qed.

  (*
  Definition empty : t := ...
  Definition elements : t -> list elt := ...
  Definition add : elt -> t -> t := ...
  Definition remove : elt -> t -> t := ...
  Definition union : t -> t -> t := ...
  Definition inter : t -> t -> t := ...

  Lemma empty_prop : forall x, ~ In_set x empty.
  Proof.
    
  Qed.

  Lemma mem_prop : forall x s, In_set x s <-> mem x s = true.
  Proof.
    
  Qed.

  Lemma add_prop : forall a s x, In_set x (add a s) <-> (x=a \/ In_set x s).
  Proof.
    
  Qed.

  Lemma remove_prop : forall a s x, In_set x (remove a s) <-> (x<>a /\ In_set x s).
  Proof.
    
  Qed.

  Lemma union_prop : forall s1 s2 x, 
    In_set x (union s1 s2) <-> (In_set x s1 \/ In_set x s2).
  Proof.
    
  Qed.

  Lemma inter_prop : forall s1 s2 x, 
    In_set x (inter s1 s2) <-> (In_set x s1 /\ In_set x s2).
  Proof.
    
  Qed.

*)

End Make.

Module S := Make NatOrderedType.

(* faire quelque tests *)



