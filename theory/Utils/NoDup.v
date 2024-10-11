Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Import ListNotations.
Require Import POram.Utils.Lists.
Require Import POram.System.PathORAMDef.
Require Import POram.Utils.Classes.

Definition inj_on_list {A B} (l : list A) (f : A -> B) :=
  forall x y, In x l -> In y l -> f x = f y -> x = y.

Definition subset_rel {X} (sub lst : list X) : Prop :=
  forall x,
    In x sub ->
    In x lst.

(*** NoDup general lemmas ***)

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

  Lemma remove_aux_removed {A} `{EqDec A} :
    forall (lst : list A) (a : A),
      NoDup lst ->
      ~ In a (remove_aux eqb lst a).
  Proof.
    induction lst as [|a' lst]; simpl; intros; auto.
    destruct eqb eqn: eq_cond.
    - intro bp.
      rewrite (eqb_true_iff a' a) in eq_cond.
      subst.
      inversion H0; auto.
    - intros [| in_cond]; subst.
      + rewrite eqb_refl in eq_cond.
        discriminate.
      + eapply IHlst; eauto.
        inversion H0; auto.
  Qed.

  Lemma NoDup_remove_aux_general {A} `{EqDec A} : forall lst b,
      NoDup lst ->
      NoDup (remove_aux eqb lst b).
  Proof.
    induction lst; simpl; intros; auto.
    destruct eqb eqn: eq_cond.
    - inversion H0; auto.
    - constructor.
      + intro pf.
        apply In_remove_aux in pf.
        inversion H0; auto.
      + apply IHlst.
        inversion H0; auto.
  Qed.

Lemma remove_list_sub_removed {A} `{EqDec A} : forall dlt lst b,
    NoDup lst ->
    In b (remove_list_sub eqb dlt lst) ->
    ~ In b dlt.
Proof.
  induction dlt; intros; simpl in *; auto.
  intros [ | in_cond]; subst.
  - apply remove_list_sub_weaken in H1.
    apply remove_aux_removed in H1; auto.
  - apply IHdlt in H1; auto.
    apply NoDup_remove_aux_general; auto.
Qed.

  (* TODO: make this generic and move elsewhere *)
  Lemma NoDup_remove_aux : forall lst x,
    NoDup (List.map block_blockid lst) ->
    NoDup (List.map block_blockid (remove_aux eqb lst x)).
  Proof.
    induction lst; simpl; intros; auto.
    destruct eqb eqn: eq_cond; simpl.
    - inversion H; auto.
    - apply NoDup_cons_iff. split.
      + intro.
        rewrite in_map_iff in H0.
        destruct H0 as [b [Hb1 Hb2]].
        apply In_remove_aux in Hb2.
        inversion H.
        apply H2.
        rewrite <- Hb1.
        apply in_map; auto.
      + apply IHlst.
        inversion H; auto.
  Qed.

  Lemma up_oram_tr_tree_or_delta o : forall id lvl dlt p,
      In id (List.map block_blockid (get_all_blks_tree
                                       (up_oram_tr o lvl dlt p))) ->
      In id (List.map block_blockid (get_all_blks_tree o)) \/
        In id (List.map block_blockid dlt).
  Proof.
    induction o; simpl; intros; auto.
    destruct data; simpl.
    - destruct lvl; simpl in *.
      + repeat rewrite map_app in *.
        repeat rewrite in_app_iff in *.
        tauto.
      + destruct p; simpl in *.
        * repeat rewrite map_app in *.
          left. auto.
        * destruct b0; simpl in *; try repeat rewrite map_app in *;
            try repeat rewrite in_app_iff in *; try repeat destruct H; auto.
          -- edestruct IHo1; eauto.
          -- edestruct IHo2; eauto.
    - destruct lvl; simpl in *.
      + repeat rewrite map_app in *.
        repeat rewrite in_app_iff in *.
        tauto.
      + destruct p; simpl in *.
        * repeat rewrite map_app in *.
          left. auto.
        * destruct b; simpl in *; try repeat rewrite map_app in *;
            try repeat rewrite in_app_iff in *; try repeat destruct H; auto.
          -- edestruct IHo1; eauto.
          -- edestruct IHo2; eauto.
  Qed.

  Lemma NoDup_up_oram_tree : forall o dlt lvl p,
      NoDup (List.map block_blockid dlt) ->
      NoDup (List.map block_blockid (get_all_blks_tree o)) -> 
      disjoint_list (List.map block_blockid (get_all_blks_tree o))
        (List.map block_blockid dlt) -> 
      NoDup
        (List.map block_blockid
           (get_all_blks_tree (up_oram_tr o lvl dlt p))).
  Proof.
    induction o; simpl; intros; auto.
    destruct lvl; simpl; auto.
    - destruct data; simpl; auto.
      + apply NoDup_disjointness; auto.
        * repeat rewrite map_app in *.
          apply NoDup_app_remove_l in H0; auto.
        * intros id [Hid1 Hid2].
          apply (H1 id); split; auto.
          rewrite map_app.
          apply in_or_app; auto.
      + apply NoDup_disjointness; auto.
        * repeat rewrite map_app in *.
          intros id [Hid1 Hid2].
          apply (H1 id); split; auto.
    - destruct p; simpl; auto.
      destruct b; simpl; auto.
      destruct data; simpl; auto.
      + apply NoDup_disjointness; auto.
        * repeat rewrite map_app in H0.
          apply NoDup_app_remove_r in H0; auto.
        * apply NoDup_disjointness.
          -- apply IHo1; auto.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H0; auto.
                apply NoDup_app_remove_r in H0; auto.
             ++ intros id [Hid1 Hid2].
                apply (H1 id); split; auto.
                repeat rewrite map_app.
                apply in_or_app; right.
                apply in_or_app; auto.
          -- repeat rewrite map_app in H0.
             do 2 apply NoDup_app_remove_l in H0; auto.
          -- intros id [Hid1 Hid2].
             apply up_oram_tr_tree_or_delta in Hid1.
             destruct Hid1 as [Hid1|Hid1].
             ++ repeat rewrite map_app in H0.
                apply NoDup_app_remove_l in H0.
                apply NoDup_app_disj in H0.
                apply (H0 id); split; auto.
             ++ apply (H1 id); split; auto.
                repeat rewrite map_app.
                apply in_or_app.
                right.
                apply in_or_app. auto.
        * intros id [Hid1 Hid2].
          repeat rewrite map_app in *.
          apply in_app_or in Hid2; destruct Hid2 as [Hid2|Hid2].
          -- apply up_oram_tr_tree_or_delta in Hid2; destruct Hid2 as [Hid2|Hid2].
             ++ apply NoDup_app_disj in H0.
                apply (H0 id); split; auto.
                apply in_or_app; auto.
             ++ apply (H1 id); split; auto.
                apply in_or_app; left; auto.
          -- apply NoDup_app_disj in H0.
             apply (H0 id); split; auto.
             apply in_or_app; right; auto.
      + apply NoDup_disjointness.
        * apply IHo1; auto.
          -- rewrite map_app in H0.
             apply NoDup_app_remove_r in H0; auto.
          -- intros id [Hid1 Hid2].
             apply (H1 id); split; auto.
             rewrite map_app.
             apply in_or_app; left; auto.
        * rewrite map_app in H0.
          apply NoDup_app_remove_l in H0; auto.
        * intros id [Hid1 Hid2].
          apply up_oram_tr_tree_or_delta in Hid1; destruct Hid1 as [Hid1|Hid1].
          -- rewrite map_app in H0.
             apply NoDup_app_disj in H0.
             apply (H0 id); split; auto.
          -- apply (H1 id); split; auto.
             rewrite map_app.
             apply in_or_app; right; auto.
      + destruct data.
        * repeat rewrite map_app in H0, H1.
          apply NoDup_disjointness.
          -- apply NoDup_app_remove_r in H0; auto.
          -- apply NoDup_app_remove_l in H0.
             apply NoDup_disjointness.
             ++ apply NoDup_app_remove_r in H0; auto.
             ++ apply IHo2; auto.
                ** apply NoDup_app_remove_l in H0; auto.
                ** intros id [Hid1 Hid2].
                   apply (H1 id); split; auto.
                   apply in_or_app; right.
                   apply in_or_app; right; auto.
             ++ intros id [Hid1 Hid2].
                apply up_oram_tr_tree_or_delta in Hid2; destruct Hid2 as [Hid2|Hid2].
                ** apply NoDup_app_disj in H0.
                   apply (H0 id); split; auto.
                ** apply (H1 id); split; auto.
                   apply in_or_app; right.
                   apply in_or_app; left; auto.
          -- intros id [Hid1 Hid2].
             apply NoDup_app_disj in H0.
             rewrite map_app in Hid2.
             apply in_app_or in Hid2; destruct Hid2 as [Hid2|Hid2].
             ++ apply (H0 id); split; auto.
                apply in_or_app; left; auto.
             ++ apply up_oram_tr_tree_or_delta in Hid2; destruct Hid2 as [Hid2|Hid2].
                ** apply (H0 id); split; auto.
                   apply in_or_app; right; auto.
                ** apply (H1 id); split; auto.
                   apply in_or_app; left; auto.           
        * repeat rewrite map_app in H0, H1.
          apply NoDup_disjointness.
          -- apply NoDup_app_remove_r in H0; auto.
          -- apply IHo2; auto.
             ++ apply NoDup_app_remove_l in H0; auto.
             ++ intros id [Hid1 Hid2].
                apply (H1 id); split; auto.
                apply in_or_app; right; auto.
          -- intros id [Hid1 Hid2].
             apply up_oram_tr_tree_or_delta in Hid2; destruct Hid2 as [Hid2|Hid2].
             ++ apply NoDup_app_disj in H0.
                apply (H0 id); split; auto.
             ++ apply (H1 id); split; auto.
                apply in_or_app; left; auto.
  Qed.
  
  (* TODO: make generic and move elsewhere *)
  Lemma NoDup_remove_list_sub : forall (dlt lst : list block),
      NoDup (List.map block_blockid lst) -> 
      NoDup (List.map block_blockid (remove_list_sub eqb dlt lst)).
  Proof.
    induction dlt; simpl.
    - intros; auto.
    - intros.
      apply IHdlt.
      apply NoDup_remove_aux; auto.
  Qed.

  Lemma subset_rel_get_cand_bs : forall `{C :Config} lst p lvl pos_map,
      subset_rel (get_cand_bs lst p lvl pos_map) lst.
  Proof.
    unfold subset_rel.
    intros.
    induction lst; simpl in *; auto.
    destruct isEqvPath eqn:p_cond.
    - inversion H.
      + left; auto.
      + right; apply IHlst; auto.
    - right. apply IHlst; auto.
  Qed.

  Lemma NoDup_get_write_back_blocks : forall `{C : Config} lst p lvl pos_map, 
      NoDup (List.map block_blockid lst) ->
      NoDup (List.map block_blockid 
               (get_write_back_blocks p lst 4 lvl pos_map)).
  Proof.
    unfold get_write_back_blocks. intros.
    destruct (length lst); try constructor.
    rewrite map_takeL.
    apply NoDup_takeL.
    induction lst; simpl.
    - apply NoDup_nil.
    - destruct isEqvPath eqn : p_cond.
      + simpl; apply NoDup_cons_iff; split.
        * intro pf. 
          rewrite in_map_iff in pf.
          destruct pf as [b [Hb1 Hb2]].
          apply subset_rel_get_cand_bs in Hb2.
          inversion H.
          apply H2.
          rewrite <- Hb1.
          apply in_map; auto.        
        * apply IHlst. inversion H; auto.
      + apply IHlst; inversion H; auto.
  Qed.
  
  Lemma disjoint_dlt : forall o lvl dlt lst p,
      NoDup (List.map block_blockid lst) ->
      subset_rel dlt lst ->
      disjoint_list
        (List.map block_blockid (get_all_blks_tree o))
        (List.map block_blockid lst) -> 
      disjoint_list
        (List.map block_blockid (get_all_blks_tree (up_oram_tr o lvl dlt p)))
        (List.map block_blockid (remove_list_sub eqb dlt lst)).
  Proof.
    intros.
    intros id [Hid1 Hid2].
    apply up_oram_tr_tree_or_delta in Hid1.
    destruct Hid1 as [Hid1|Hid1].
    - apply (H1 id); split; auto.
      rewrite in_map_iff in Hid2.
      destruct Hid2 as [b [Hb1 Hb2]].
      apply remove_list_sub_weaken in Hb2.
      rewrite <- Hb1.
      apply in_map; auto.
    - rewrite in_map_iff in Hid1.
      destruct Hid1 as [b [Hb1 Hb2]].
      unfold subset_rel in H0.
      rewrite in_map_iff in Hid2.
      destruct Hid2 as [c [Hc1 Hc2]].
      assert (b = c).
      { apply H0 in Hb2.
        apply remove_list_sub_weaken in Hc2.
        apply NoDup_map_inj in H.
        unfold inj_on_list in H.
        apply (H b c); auto.
        rewrite Hc1; auto.
      }
      subst.
      apply remove_list_sub_removed in Hc2; auto.
      eapply NoDup_map_inv; eauto.
  Qed.
