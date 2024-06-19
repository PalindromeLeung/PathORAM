Require Import Coq.Lists.List.
Import ListNotations.
Require Import POram.Utils.Lists.

Definition disjoint_list {A} (l1 l2 : list A) :=
  forall a, ~ (In a l1 /\ In a l2).

Definition inj_on_list {A B} (l : list A) (f : A -> B) :=
  forall x y, In x l -> In y l -> f x = f y -> x = y.

Lemma NoDup_disjointness: forall {A B} (l1 : list A) (l2 : list A) (f : A -> B) ,
    NoDup (List.map f l1) ->
    NoDup (List.map f l2) ->
    disjoint_list (List.map f l1) (List.map f l2) ->
    NoDup (List.map f (l1 ++ l2)).
Proof.
  induction l1; intros; simpl; auto.
  apply NoDup_cons.
  - intro. rewrite map_app in H2.
    apply in_app_or in H2.
    destruct H2.
    + inversion H. contradiction.
    + apply (H1 (f a)). split; auto. left. reflexivity.
  - apply IHl1; auto.
    + inversion H. auto.
    + intro. intro. unfold disjoint_list in H1.
      apply (H1 a0).
      destruct H2.
      split; auto.
      right. auto.
Qed. 

Lemma NoDup_app_disj : forall {A} (l1 l2 : list A),
    NoDup (l1 ++ l2) ->
    disjoint_list l1 l2.
Proof.
  induction l1; intros; simpl in *.
  -  unfold disjoint_list.
     intro. intro.
     destruct H0.
     contradiction.
  - intro. intro.
    destruct H0.
    destruct H0.
    + rewrite H0 in H.
      inversion H.
      apply H4.
      apply in_or_app.
      right; auto.
    + unfold disjoint_list in IHl1.
      unfold not in IHl1.
      apply IHl1 with (a := a0)(l2 := l2).
      inversion H; auto.
      split; auto.
Qed.

Lemma NoDup_app_remove_mid : forall (A : Type) (l2 l1 l3 : list A) ,
    NoDup (l1 ++ l2 ++ l3) -> NoDup (l1 ++ l3).
Proof.
  induction l2; intros.
  - exact H.
  - apply IHl2.
    eapply NoDup_remove_1.
    exact H.
Qed.    

Lemma NoDup_takeL {A} : forall n (l : list A),
    NoDup l -> NoDup (takeL n l).
Proof.
  induction n; simpl; intros; try contradiction.
  apply NoDup_nil.
  destruct l; simpl.
  - apply NoDup_nil.
  - simpl; apply NoDup_cons_iff; split.
    + intro pf.
      apply takeL_in in pf. inversion H. contradiction.
    + apply IHn. inversion H; auto.
Qed.

Lemma NoDup_map_inj {A B} : forall (f : A -> B) l,
  NoDup (List.map f l) ->
  inj_on_list l f.
Proof.
  unfold inj_on_list.
  induction l; intros nd_fl x y Hx Hy Hxy.
  - destruct Hx.
  - destruct Hx.
    + destruct Hy; try congruence.
      simpl in nd_fl.
      rewrite NoDup_cons_iff in nd_fl.
      destruct nd_fl as [Hfa nd].
      elim Hfa.
      rewrite H.
      rewrite Hxy.
      now apply in_map.
    + destruct Hy.
      * simpl in nd_fl; inversion nd_fl.
        elim H3.
        rewrite H0.
        rewrite <- Hxy.
        now apply in_map.
      * eapply IHl; eauto.
        now inversion nd_fl.
Qed.
