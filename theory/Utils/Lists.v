Require Import POram.Utils.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Definition disjoint_list {A} (l1 l2 : list A) :=
  forall a, ~ (In a l1 /\ In a l2).

Fixpoint takeL {A} n (l : list A) : list A :=
  match n with
  | O => []
  | S m => match l with
          | [] => []
          | h :: t => h :: takeL m t 
          end
  end.

Fixpoint remove_list {A : Type} (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => [] 
  | x' :: xs' =>
      if p x'
      then remove_list p xs'
      else
        x' :: remove_list p xs'
  end.

Lemma takeL_in : forall {X} (x : X) n l,
   In x (takeL n l) -> In x l. 
Proof.
  induction n; intros; simpl in *.
  - exfalso; auto.
  - destruct l.
    + auto.
    + destruct H.
      * rewrite H. left; auto.
      * right. apply IHn. auto.
Qed.

Lemma In_remove_list_In {A} (p : A -> bool) (xs : list A) : forall x,
    In x (remove_list p xs) -> In x xs.
Proof.
  intros x Hx.
  induction xs as [|y xs].
  - destruct Hx.
  - simpl in Hx.
    destruct (p y).
    + right; auto.
    + simpl in *; tauto.
Qed.

Lemma In_remove_list_p {A} (p : A -> bool) (xs : list A) : forall x,
    In x (remove_list p xs) -> p x = false.
Proof.
  intros x Hx.
  induction xs as [|y xs].
  - destruct Hx.
  - simpl in Hx.
    destruct (p y) eqn:Hy; auto.
    destruct Hx; auto.
    congruence.
Qed.

Lemma In_remove_list {A} (p : A -> bool) (xs : list A) : forall x,
    In x xs -> p x = false -> In x (remove_list p xs).
Proof.
  intros x Hx1 Hx2.
  induction xs as [|y xs].
  - destruct Hx1.
  - simpl.
    destruct Hx1; subst.
    + rewrite Hx2.
      left; auto.
    + destruct (p y); auto.
      right; auto.
Qed.

Lemma In_remove_list_iff {A} (p : A -> bool) (xs : list A) : forall x,
    In x (remove_list p xs) <-> In x xs /\ p x = false.
Proof.
  intros; split; intros.
  - split.
    + eapply In_remove_list_In; eauto.
    + eapply In_remove_list_p; eauto.
  - destruct H; eapply In_remove_list; eauto.
Qed.

Fixpoint remove_aux {A} (A_eqb : A -> A -> bool) (lst : list A) (x : A) : list A :=
  match lst with
  | [] => []
  | h :: t => 
      if A_eqb h x then t else h :: remove_aux A_eqb t x
  end.

Fixpoint remove_list_sub {A} (A_eqb : A -> A -> bool) (sublist : list A) (lst : list A) : list A :=
  match sublist with
  | [] => lst
  | h :: t => remove_list_sub A_eqb t (remove_aux A_eqb lst h)
  end.

Lemma remove_aux_lemma {A} `{EqDec A} : forall (lst : list A) (a a' : A),
    In a' lst ->
    In a' (remove_aux eqb lst a) \/ a = a'.
Proof.
  intros.
  induction lst; intuition.
  simpl.
  destruct eqb eqn: eq_cond; simpl.
  - destruct H0.
    + right.
      rewrite (eqb_true_iff a0 a) in eq_cond; congruence.
    + tauto.
  - destruct H0.
    + do 2 left; auto.
    + apply IHlst in H0. tauto.
Qed.

Lemma remove_list_sub_lemma {A} `{EqDec A} : forall (a : A) (sub : list A) (lst : list A),
      In a lst ->
      In a (remove_list_sub eqb sub lst) \/ In a sub.
Proof.
  intros a sub.
  induction sub. 
  - simpl.  intros. left; auto.
  - intros. simpl remove_list_sub.
    pose proof (IHsub (remove_aux eqb lst a0))%list.
    destruct (remove_aux_lemma _ a0 _ H0).
    + apply H1 in H2. destruct H2.
      * left. auto.
      * right. right; auto.
    + right. left; auto.
Qed.

Lemma In_remove_aux {A} `{EqDec A} :
  forall (lst : list A) (x a : A),
    In x (remove_aux eqb lst a) ->
    In x lst.
Proof.
  induction lst; simpl; intros; auto.
  destruct eqb eqn: eq_cond; simpl.
  - right; auto.
  - destruct H0; auto. right.
    apply IHlst with (a := a0). auto.
Qed.

Lemma remove_list_sub_weaken {A} `{EqDec A} : forall dlt lst b,
    In b (remove_list_sub eqb dlt lst) -> In b lst.
Proof.
  induction dlt; simpl; intros; auto.
  apply IHdlt in H0.
  apply In_remove_aux in H0; auto.
Qed.

Lemma map_takeL {A B} (f : A -> B) : forall n l,
    List.map f (takeL n l) = takeL n (List.map f l).
Proof.
  induction n; auto.
  intro.
  destruct l; simpl; try reflexivity.
  rewrite IHn. reflexivity.
Qed.

Fixpoint filter_Some {X} (l : list (option X)) : list X :=
  match l with
  | [] => []
  | Some x :: l' => x :: filter_Some l'
  | None :: l' => filter_Some l'
  end.

Lemma filter_Some_correct {X} (l : list (option X)) : forall x,
  In x (filter_Some l) <-> In (Some x) l.
Proof.
  intro x; split; intro pf.
  - induction l as [|o l'].
    + destruct pf.
    + destruct o as [x'|].
      * destruct pf.
        -- left; congruence.
        -- right; auto.
      * right; auto.
- induction l as [|o l'].
  + destruct pf.
  + destruct pf.
    * subst.
      left; reflexivity.
    * destruct o.
      -- right; auto.
      -- auto.
Qed.

Lemma in_dec {A} `{EqDec A} : forall (x : A) (l : list A),
  In x l \/ ~ In x l.
Proof.
  intros x l.
  induction l.
  - now right.
  - destruct (eq_dec a x).
    + subst; left; now left.
    + destruct IHl.
      * left; now right.
      * right; simpl; tauto.
Qed.
