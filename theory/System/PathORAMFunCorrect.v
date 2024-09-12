Require Coq.Bool.Bool.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import POram.Utils.Lists.
Require Import POram.Utils.Vectors.
Require Import POram.Utils.Rationals.
Require Import POram.Utils.Distributions.
Require Import POram.Utils.Tree.
Require Import POram.Utils.StateT.
Require Import POram.Utils.NoDup.
Require Export POram.System.PathORAMDef.

Section PORAM_PROOF.

  Context `{C : Config}.
    
  Lemma iterate_right_split {X} n : forall (start k : nat) (f : path -> nat -> X -> X) (p : path) (x : X),
      iterate_right start p f (n+k) x =
        iterate_right start p f n
          (iterate_right (n + start) p f k x).
  Proof.
    induction n; intros.
    - reflexivity.
    - simpl.
      rewrite IHn.
      rewrite plus_n_Sm.
      reflexivity.
  Qed.

  Lemma factor_lemma {X} (L k : nat) (p : path) (f : path -> nat -> X -> X) (x : X) :
    (k < L)%nat ->
    iterate_right 0 p f L x =
      iterate_right 0 p f k
        (f p k
           (iterate_right (S k) p f (L - 1 - k) x)
        ).
  Proof.
    intro.
    assert (L = k + S ((L - 1) - k))%nat by lia.
    rewrite H0 at 1.
    rewrite iterate_right_split.
    rewrite <- (plus_n_O).
    simpl.
    reflexivity. 
  Qed.

  Lemma kv_in_list_partition:
    forall (id : block_id) (v : nat) (s : state) (del : list block),
      blk_in_stash id v s ->
      (In (Block id v)
         (remove_list_sub block_eqb del (state_stash s))  \/
         (In (Block id v) del)).
  Proof.
    intros.
    unfold blk_in_stash in H.
    apply remove_list_sub_lemma; auto.
    exact block_eqb_correct.
  Qed.

  Lemma stash_path_combined_rel_Rd : forall (id : block_id) (v : nat) (s : state) (p_new : path),
      kv_rel id v s ->
      blk_in_stash id v ((get_pre_wb_st id Read (state_position_map s)
                            (state_stash s)
                            (state_oram s)
                            (calc_path id s) p_new)).
  Proof.
    intros.
    unfold get_pre_wb_st. simpl.
    apply in_or_app.
    destruct H.
    - right; auto.
    - unfold blk_in_path in H. auto.
  Qed.

  Definition on_path b o p :=
    In b (concat (lookup_path_oram o p)).

  Lemma block_dec (b : block) bs :
    In b bs \/ ~ In b bs.
  Proof.
    induction bs.
    - right; simpl; tauto.
    - destruct (block_eqb b a) eqn:?.
      + apply block_eqb_correct in Heqb0; subst.
        left; left; reflexivity.
      + destruct IHbs.
        * left; right; auto.
        * right; intros [Heq|HIn].
          -- subst.
             rewrite eqb_correct_refl in Heqb0;
               [discriminate|].
             exact block_eqb_correct.
          -- contradiction.
  Qed.

  Lemma on_path_dec b o : forall p,
    on_path b o p \/ ~ on_path b o p.
  Proof.
    unfold on_path.
    induction o; intro p.
    - right; intro; auto.
    - destruct p; simpl.
      + destruct data; simpl; [|tauto].
        apply block_dec.
      + destruct b0.
        * destruct data; auto.
          simpl; rewrite in_app_iff.
          specialize (IHo1 p).
          pose (block_dec b b0); tauto.
        * destruct data; auto.
          simpl; rewrite in_app_iff.
          specialize (IHo2 p).
          pose (block_dec b b0); tauto.
  Qed.

  Lemma pos_map_stable_across_wb : forall n p s start,
      state_position_map s = state_position_map (write_back_r start p n s).
  Proof.
    unfold write_back_r.
    induction n; simpl; auto.
  Qed. 

  Lemma calc_path_pos_map_same : forall id s s',
      state_position_map s = state_position_map s' ->
      calc_path id s = calc_path id s'.
  Proof.
    intros.
    unfold calc_path.
    congruence.
  Qed.

  Lemma lookup_update_diffid : forall id id' m p_new,
      id <> id' ->
      lookup_dict
        (makeBoolList false LOP)
        id (update_dict id' p_new m) =
        lookup_dict (makeBoolList false LOP) id m.
  Proof.
    intros.
    unfold lookup_dict.
    unfold update_dict.
    destruct m; simpl.
    induction dict_elems as [|[k v] tl]; simpl.
    - destruct (id ?= id')%nat eqn:id_cond; auto.
      rewrite Nat.compare_eq_iff in id_cond; contradiction.
    - destruct (id' ?= k)%nat eqn:id_cond1; simpl.
      + rewrite Nat.compare_eq_iff in id_cond1; subst.
        destruct (id ?= k)%nat eqn:id_cond2; auto.
        rewrite Nat.compare_eq_iff in id_cond2; contradiction.
      + destruct (id ?= id')%nat eqn:id_cond2; auto.
        * rewrite Nat.compare_eq_iff in id_cond2; contradiction.
        * rewrite <- nat_compare_lt in *.
          assert (id < k)%nat by lia.
          rewrite nat_compare_lt in H0.
          rewrite H0; auto.
      + rewrite IHtl; auto.
  Qed.

  Lemma in_clear_path b o : forall p p',
    In b (concat (lookup_path_oram o p)) ->
    ~ In b (concat (lookup_path_oram o p')) ->
    In b (concat (lookup_path_oram (clear_path o p') p)).
  Proof.
    induction o; intros.
    - destruct H.
    - destruct p.
      (* p empty *)
      + simpl in H.
        destruct data.
        * elim H0; simpl.
          simpl in *.
          rewrite app_nil_r in H.
          destruct p'; auto.
          -- simpl.
             rewrite app_nil_r; auto.
          -- destruct b1; simpl; apply in_or_app; tauto.
        * destruct H.
      (* p non-empty *)
      + destruct b0.
        (* p left *)
        * destruct p'.
          (* p' empty *)
          -- simpl in *.
             destruct data; auto.
             simpl in *.
             apply in_app_or in H.
             destruct H; auto.
             rewrite app_nil_r in H0; tauto.
          (* p' non-empty *)
          -- destruct b0.
             (* p' left *)
             ++ simpl in *. apply IHo1.
                ** destruct data; auto.
                   simpl in *.
                   rewrite in_app_iff in *; tauto.
                ** destruct data; auto.
                   simpl in *.
                   rewrite in_app_iff in *; tauto.
             (* p' right *)
             ++ destruct data; auto.
                simpl in *.
                rewrite in_app_iff in *; tauto.
        (* p right *)
        * destruct p'.
          (* p' empty *)
          -- simpl in *.
             destruct data; auto.
             simpl in *.
             apply in_app_or in H.
             destruct H; auto.
             rewrite app_nil_r in H0; tauto.
          (* p' non-empty *)
          -- destruct b0.
             (* p' left *)
             ++ destruct data; auto.
                simpl in *.
                rewrite in_app_iff in *; tauto.
             (* p' right *)
             ++ simpl in *. apply IHo2.
                ** destruct data; auto.
                   simpl in *.
                   rewrite in_app_iff in *; tauto.
                ** destruct data; auto.
                   simpl in *.
                   rewrite in_app_iff in *; tauto.
  Qed.

  Lemma get_pre_wb_st_Read_kvr_kvr : forall (id id' : block_id) (v : nat) (s : state) (p_new : path),
      kv_rel id v s ->
      kv_rel id v ((get_pre_wb_st id' Read (state_position_map s)
                      (state_stash s)
                      (state_oram s)
                      (calc_path id' s) p_new)).
  Proof.
    intros.
    destruct H.
    - left.
      unfold blk_in_stash. simpl.
      apply in_or_app; right.
      exact H.
    - destruct (on_path_dec (Block id v)  (state_oram s) (calc_path id' s)).
      + left.
        unfold blk_in_stash; simpl.
        apply in_or_app; left.
        unfold on_path in H0.
        exact H0.
      + right.
        unfold blk_in_path in *.
        unfold blk_in_p in *.
        unfold on_path in *.
        simpl.
        assert (id <> id') by congruence.
        unfold get_pre_wb_st; simpl.
        unfold calc_path at 2; simpl.
        rewrite lookup_update_diffid; auto.
        unfold calc_path in H.
        apply in_clear_path; auto.
  Qed.

  Lemma get_pre_wb_st_Write_kvr_kvr : forall (id id' : block_id) (v v': nat) (s : state) (p_new : path),
      id <> id' -> 
      kv_rel id v s ->
      kv_rel id v ((get_pre_wb_st id' (Write v') (state_position_map s)
                      (state_stash s)
                      (state_oram s)
                      (calc_path id' s) p_new)).
  Proof.
    intros.
    destruct H0.
    - left.
      unfold blk_in_stash. simpl.
      right. apply In_remove_list.
      + apply in_or_app; right; auto.
      + simpl. rewrite Nat.eqb_neq; auto.
    - destruct (on_path_dec (Block id v) (state_oram s) (calc_path id' s)).
      + left.
        unfold blk_in_stash; simpl.
        right. apply In_remove_list.
        * apply in_or_app; left.
          unfold on_path in H1.
          exact H1.
        * simpl. rewrite Nat.eqb_neq; auto.
      + right.
        unfold blk_in_path in *.
        unfold blk_in_p in *.
        unfold on_path in *.
        simpl.
        assert (id <> id') by congruence.
        unfold get_pre_wb_st; simpl.
        unfold calc_path at 2; simpl.
        rewrite lookup_update_diffid; auto.
        unfold calc_path in H.
        apply in_clear_path; auto.
Qed.     
  
  Lemma In_path_in_tree_block : forall o p b,
      In b (concat (lookup_path_oram o p)) ->
      In b (get_all_blks_tree o). 
  Proof.
    induction o; simpl; intros; auto.
    destruct p as [|hd tl]. 
    - destruct data; simpl in *; auto.
      + rewrite app_nil_r in H.
        apply in_or_app.
        left; auto.
      + contradiction.
    - destruct hd.
      + destruct data.
        * simpl in H.
          apply in_app_or in H.
          apply in_or_app.
          destruct H.
          -- left; auto.
          -- right. apply in_or_app.
             left. eapply IHo1; eauto.
        * apply in_or_app.
          left.
          eapply IHo1; eauto.
      + destruct data.
        * simpl in H.
          apply in_app_or in H.
          apply in_or_app.
          destruct H.
          -- left; auto.
          -- right. apply in_or_app.
             right. eapply IHo2; eauto.
        * apply in_or_app.
          right.
          eapply IHo2; eauto.
  Qed.

  Lemma NoDup_tree_id_same_v:
    forall id v v' l,
      NoDup (List.map block_blockid l) -> 
      In (Block id v) l ->
      In (Block id v') l ->
      v = v'. 
  Proof.
    intros.
    apply NoDup_map_inj in H.
    unfold inj_on_list in H.
    assert (id = id) by reflexivity.
    specialize (H _ _ H0 H1 H2).
    inversion H; auto.    
  Qed.
  
  Lemma In_tree_in_path :
    forall s id v,  
      well_formed s -> 
      In (Block id v) (get_all_blks_tree (state_oram s)) ->
      blk_in_path id v s.
  Proof.
    intros.
    destruct H.
    unfold blk_in_path, blk_in_p.
    pose proof H0.
    apply in_map with (f := block_blockid) in H0.
    specialize (blk_in_path_in_tree id H0).
    rewrite in_map_iff in blk_in_path_in_tree.
    destruct blk_in_path_in_tree as [[id' v'] [Hb'1 Hb'2]]; simpl in *.
    subst.
    pose proof Hb'2.
    apply In_path_in_tree_block in Hb'2.
    rewrite (NoDup_tree_id_same_v id v v' _ no_dup_tree H Hb'2); auto.
  Qed.
  
  Lemma lookup_update_sameid : forall id m p_new, 
      lookup_dict
        (makeBoolList false LOP) id
        (update_dict id p_new m) = p_new.
  Proof.
    intros.
    unfold lookup_dict.
    unfold update_dict.
    destruct m; simpl.
    induction dict_elems as [|[k v] tl]; simpl.
    - rewrite Nat.compare_refl; auto.
    - destruct (id ?= k)%nat eqn:id_cond; simpl.
      + rewrite Nat.compare_refl; auto.
      + rewrite Nat.compare_refl; auto.
      + rewrite id_cond.
        exact IHtl.
  Qed.
  
  Lemma blk_in_p_nil_Some id v o1 o2 data :
    blk_in_p id v (node (Some data) o1 o2) [] ->
    In (Block id v) data.
  Proof.
    unfold blk_in_p; simpl.
    rewrite app_nil_r; auto.
  Qed.

  Lemma blk_in_p_nil_None id v o1 o2 :
    ~ blk_in_p id v (node None o1 o2) [].
  Proof.
    auto.
  Qed.

  Lemma blk_in_p_cons_true id v o1 o2 p data :
    blk_in_p id v o1 p ->
    blk_in_p id v (node data o1 o2) (true :: p).
  Proof.
    unfold blk_in_p.
    intro pf; simpl.
    destruct data; auto.
    apply in_or_app; right; auto.
  Qed.

  Lemma blk_in_p_cons_false id v o1 o2 p data :
    blk_in_p id v o2 p ->
    blk_in_p id v (node data o1 o2) (false :: p).
  Proof.
    unfold blk_in_p.
    intro pf; simpl.
    destruct data; auto.
    apply in_or_app; right; auto.
  Qed.

  Lemma blk_in_p_true_Some id v o1 o2 p data :
    blk_in_p id v (node (Some data) o1 o2) (true :: p) ->
    In (Block id v) data \/ blk_in_p id v o1 p.
  Proof.
    unfold blk_in_p; simpl in *.
    intro pf.
    apply in_app_or; auto.
  Qed.

  Lemma blk_in_p_true_None id v o1 o2 p :
    blk_in_p id v (node None o1 o2) (true :: p) ->
    blk_in_p id v o1 p.
  Proof.
    auto.
  Qed.

  Lemma blk_in_p_false_Some id v o1 o2 p data :
    blk_in_p id v (node (Some data) o1 o2) (false :: p) ->
    In (Block id v) data \/ blk_in_p id v o2 p.
  Proof.
    unfold blk_in_p; simpl in *.
    intro pf.
    apply in_app_or; auto.
  Qed.

  Lemma blk_in_p_false_None id v o1 o2 p :
    blk_in_p id v (node None o1 o2) (false :: p) ->
    blk_in_p id v o2 p.
  Proof.
    auto.
  Qed.

  Lemma blk_in_p_clear_path:
    forall o p p_new id v,
      blk_in_p id v (clear_path o p) p_new ->
      blk_in_p id v o p_new.
  Proof.
    induction o; simpl in *; auto.
    intros.
    destruct p; simpl in *; auto.
    - destruct p_new as [|[]].
      + destruct H.
      + apply blk_in_p_true_None in H.
        apply blk_in_p_cons_true; auto.
      + apply blk_in_p_false_None in H.
        apply blk_in_p_cons_false; auto.
    - destruct b.
      + destruct p_new as [|[]].
        * destruct H.
        * apply blk_in_p_true_None in H.
          apply blk_in_p_cons_true.
          apply IHo1 with (p := p); auto.
        * apply blk_in_p_false_None in H.
          apply blk_in_p_cons_false; auto.
      + destruct p_new as [|[]].
        * destruct H.
        * apply blk_in_p_true_None in H.
          apply blk_in_p_cons_true; auto.            
        * apply blk_in_p_false_None in H.
          apply blk_in_p_cons_false.
          apply IHo2 with (p := p); auto.
  Qed.
          
  Lemma stash_path_combined_rel_Rd_undef : forall (id id' : block_id) (s : state) (p_new : path),
      well_formed s ->
      undef id s ->
      undef id ((get_pre_wb_st id' Read (state_position_map s)
                   (state_stash s)
                   (state_oram s)
                   (calc_path id' s) p_new)).
  Proof.
    intros id id' s p_new wf_s Hids [v Hv].
    apply Hids; exists v.
    destruct Hv as [Hv|Hv].
    (* in stash as assumption *)
    - unfold blk_in_stash, get_pre_wb_st in Hv; simpl in Hv.
      apply in_app_or in Hv.
      destruct Hv as [Hv|Hv].
      (* kv in selected path *)
      + right.   
        unfold blk_in_path.
        unfold blk_in_p.
        apply In_path_in_tree_block in Hv.
        apply In_tree_in_path in Hv; auto.
      + left; exact Hv.
    - (* in tree as assumption *)
      unfold blk_in_path, get_pre_wb_st in Hv; simpl in Hv.
      right. 
      destruct (nat_eq_dec id id').
      + subst.
        unfold calc_path at 2 in Hv; simpl in Hv.
        rewrite lookup_update_sameid in Hv.
        apply blk_in_p_clear_path in Hv.
        unfold blk_in_path.
        pose proof (Hv2 := Hv).
        apply In_path_in_tree_block in Hv.
        apply In_tree_in_path in Hv; auto.
      + unfold calc_path at 2 in Hv; simpl in Hv.
        rewrite lookup_update_diffid in Hv; auto.
        apply blk_in_p_clear_path in Hv; auto.
  Qed. 

  Lemma stash_path_combined_rel_Wr_undef : forall (id id' : block_id) (v : nat) (s : state) (p_new : path),
      id <> id' ->
      well_formed s ->
      undef id' s ->
      undef id' ((get_pre_wb_st id (Write v) (state_position_map s)
                   (state_stash s)
                   (state_oram s)
                   (calc_path id s) p_new)).
  Proof. 
    intros id id' v s p_new Hneq wf_s Hids [v' Hv'].
    apply Hids; exists v'.
    destruct Hv' as [Hv'|Hv'].
    (* in stash as assumption *)
    - unfold blk_in_stash, get_pre_wb_st in Hv'; simpl in Hv'.
      destruct Hv'; [congruence|].
      rewrite In_remove_list_iff in H; destruct H as [Hv' _].
      apply in_app_or in Hv'.
      destruct Hv' as [Hv'|Hv'].
      (* kv in selected path *)
      + right.   
        unfold blk_in_path.
        unfold blk_in_p.
        apply In_path_in_tree_block in Hv'.
        apply In_tree_in_path in Hv'; auto.
      + left; exact Hv'.
    - (* in tree as assumption *)
      unfold blk_in_path, get_pre_wb_st in Hv'; simpl in Hv'.
      right.
      unfold calc_path at 2 in Hv'; simpl in Hv'.
      rewrite lookup_update_diffid in Hv'; auto.
      apply blk_in_p_clear_path in Hv'; auto.
  Qed. 
    
  Lemma get_pre_wb_st_Write_stsh : forall (id : block_id) (v : nat) (s : state) (p_new : path),
      blk_in_stash id v
        ((get_pre_wb_st id (Write v)
          (state_position_map s)
          (state_stash s)
          (state_oram s)
          (calc_path id s)
          p_new)).
  Proof.
    intros.
    unfold get_pre_wb_st;
      unfold blk_in_stash; simpl.
    left; auto.
  Qed.

  Lemma calc_path_write_bk_r_stable : forall start id s n p ,
      calc_path id (write_back_r start p n s) = calc_path id s.
  Proof.
    intros.
    apply calc_path_pos_map_same.
    symmetry.
    apply pos_map_stable_across_wb.
  Qed.

  Lemma path_conversion : forall o lvl p p' b,
      isEqvPath p p' lvl = true -> 
      at_lvl_in_path o lvl p b -> at_lvl_in_path o lvl p' b.
  Proof.
    induction o.
    - intros. auto.
    - intros.
      destruct lvl; auto.
      destruct p.
      destruct p'; simpl in *; auto.
      inversion H.
      destruct b0. 
      + destruct p'.  inversion H.
        destruct b0.
        * eapply IHo1; eauto. exact H.
        * inversion H.
      + destruct p'. inversion H.
        destruct b0.
        * inversion H.
        * eapply IHo2; eauto. exact H.
  Qed.

  Lemma locate_comp_block_selection :
    forall o p p' lvl lvl' dlt,
      (lvl < lvl')%nat ->    
      locate_node_in_tr (up_oram_tr o lvl dlt p') lvl' p =
        locate_node_in_tr o lvl' p.
  Proof.
    intros.
    unfold locate_node_in_tr.
    unfold up_oram_tr.
    rewrite lookup_tree_update_tree; auto.
  Qed.

  Lemma at_lvl_in_path_blocks_selection :
    forall s p p' lvl lvl' b,
      (lvl < lvl')%nat ->
      at_lvl_in_path (state_oram s) lvl' p b ->
      at_lvl_in_path (state_oram (blocks_selection p' lvl s)) lvl' p b.
  Proof.
    intros.
    unfold at_lvl_in_path in *.
    unfold blocks_selection; simpl.
    rewrite locate_comp_block_selection; auto.
  Qed.

  Lemma kv_in_delta_in_tree :
    forall (o : oram) (id : block_id) (v : nat) (del : list block) (lvl: nat )(p :path),
      In (Block id v) del ->
      coord_in_bound o p lvl ->
      at_lvl_in_path (up_oram_tr o lvl del p) lvl p (Block id v).
  Proof.
    induction o; simpl in *; try contradiction.
    - unfold at_lvl_in_path in *.
      destruct lvl; simpl in *; auto.
      + destruct p; simpl in *; auto.
        destruct b; simpl in *.
        * intros. apply IHo1; auto.
        * intros. apply IHo2; auto.
  Qed.

  Lemma path_eq_get_cand_bs : forall id v h p stop m,
      In (Block id v) (get_cand_bs h p stop m) ->
      isEqvPath p (lookup_dict (makeBoolList false LOP) id m) stop = true.
  Proof.
    induction h; intros; simpl in *.
    - exfalso; auto.
    - destruct isEqvPath eqn : pEqv_cond.
      + destruct H; simpl in *.
        * rewrite H in pEqv_cond. auto.
        * apply IHh. auto.
      + apply IHh; auto.
  Qed.
  
  Lemma stash_block_selection : forall p s id v lvl,
      well_formed s ->
      length p = LOP ->
      Nat.le lvl LOP -> 
      blk_in_stash id v s ->
      blk_in_stash id v (blocks_selection p lvl s) \/
        (at_lvl_in_path (state_oram
                           (blocks_selection p lvl s)) lvl p (Block id v) /\
           at_lvl_in_path (state_oram
                             (blocks_selection p lvl s)) lvl (calc_path id s) (Block id v) 
        ).
  Proof.
    intros.
    remember (blocks_selection p lvl s) as s'.
    unfold blocks_selection in Heqs'.
    unfold blk_in_stash in Heqs'.
    unfold blk_in_stash.
    rewrite Heqs'.
    simpl.
    remember (get_write_back_blocks p (state_stash s) 4 lvl (state_position_map s)) as dlt.
    apply kv_in_list_partition with (del := dlt) in H2.  destruct H2.
    - left; auto.
    - right.
      split.
      + apply kv_in_delta_in_tree; auto.
        apply pb_coord_in_bound with (k := LOP); auto.
        * apply H.
      + apply path_conversion with (p := p).
        * rewrite Heqdlt in H2. unfold get_write_back_blocks in H2.
          destruct (length (state_stash s)); try contradiction.
          apply takeL_in in H2.
          unfold calc_path.
          apply path_eq_get_cand_bs with (v := v )(h := state_stash s); auto.
        * apply kv_in_delta_in_tree; auto.
          apply pb_coord_in_bound with (k := LOP); auto.
          apply H.
  Qed.
  
  Lemma up_oram_tr_preserves_pb : forall o lvl dlt p n,
      is_p_b_tr o n ->
      is_p_b_tr (up_oram_tr o lvl dlt p) n.
  Proof.
    intros; apply update_tree_preserves_pb; auto.
  Qed.

  Lemma disjoint_weaken2 : forall dlt l lst, 
      disjoint_list
        (List.map block_blockid l)
        (List.map block_blockid lst) ->
      subset_rel dlt lst -> 
      disjoint_list
        (List.map block_blockid l)
        (List.map block_blockid dlt).
  Proof.
    intros.
    intros id [Hid1 Hid2].
    apply (H id); split; auto.
    rewrite in_map_iff in *.
    destruct Hid2 as [b [Hb1 Hb2]].
    exists b.
    split; auto.
  Qed.

  Lemma get_write_back_blocks_subset : forall lst p lvl pos_map,
      subset_rel (get_write_back_blocks p lst 4 lvl pos_map) lst.
  Proof.
    unfold subset_rel.
    intros.
    unfold get_write_back_blocks in H.
    destruct (length lst); try contradiction.
    apply takeL_in in H.
    apply subset_rel_get_cand_bs in H.
    auto.
  Qed.

  Lemma In_path_in_tree : forall o p id,
      In id (List.map block_blockid (concat (lookup_path_oram o p))) ->
      In id (List.map block_blockid (get_all_blks_tree o)).
  Proof.
    intros o p id pf.
    rewrite in_map_iff in *.
    destruct pf as [b [Hb1 Hb2]].
    exists b; split; auto.
    eapply In_path_in_tree_block; eauto.
  Qed.

  Lemma in_up_oram_tr : forall o id lvl dlt p p',
      NoDup (List.map block_blockid (get_all_blks_tree o)) ->
      In id (List.map block_blockid (get_all_blks_tree (up_oram_tr o lvl dlt p'))) ->
      In id (List.map block_blockid (concat (lookup_path_oram o p))) ->
      In id (List.map block_blockid (concat (lookup_path_oram (up_oram_tr o lvl dlt p') p))).
  Proof.
    induction o; simpl; intros; auto.
    destruct lvl; simpl in *.
    - destruct p; simpl in *.
      + rewrite app_nil_r.
        rewrite map_app in *.
        apply in_app_or in H0.
        destruct H0; auto.
        destruct data.
        * simpl in H1.
          rewrite app_nil_r in H1.
          rewrite map_app in H.
          apply NoDup_app_disj in H.
          elim (H id); split; auto.
        * destruct H1.
      + destruct b; simpl; auto.
        * destruct data; simpl; repeat rewrite map_app in *.
          -- apply in_app_or in H0.
             destruct H0.
             ++ apply in_or_app.
                left; auto.
             ++ simpl in H1.
                rewrite map_app in *.
                apply in_app_or in H1.
                apply in_or_app.
                destruct H1.
                ** apply NoDup_app_disj in H.
                   elim (H id); split; auto.
                ** right; auto.
          -- apply in_app_or in H0.
             destruct H0.
             ++ apply in_or_app.
                left; auto.
             ++ apply in_or_app.
                right; auto.
        * destruct data; simpl; repeat rewrite map_app in *.
          -- apply in_app_or in H0.
             destruct H0.
             ++ apply in_or_app.
                left; auto.
             ++ simpl in H1.
                rewrite map_app in *.
                apply in_app_or in H1.
                apply in_or_app.
                destruct H1.
                ** apply NoDup_app_disj in H.
                   elim (H id); split; auto.
                ** right; auto.
          -- apply in_app_or in H0.
             destruct H0.
             ++ apply in_or_app.
                left; auto.
             ++ apply in_or_app.
                right; auto.
    - destruct p; simpl; auto.
      + destruct p'; simpl.
        * destruct data; simpl in *; auto.
        * destruct b; simpl in *; auto.
      + destruct p'; simpl in *; auto.
        destruct b; simpl in *; auto.
        * destruct b0; simpl in *; auto.
          destruct data; simpl in *; auto; repeat rewrite map_app in *.
          -- apply in_or_app.
             apply in_app_or in H1.
             destruct H1.
             ++ left. auto.
             ++ right. apply IHo1; auto.
                ** apply NoDup_app_remove_l in H.
                   apply NoDup_app_remove_r in H; auto.
                ** apply in_app_or in H0.
                   destruct H0.
                   --- apply In_path_in_tree in H1.
                       apply NoDup_app_disj in H.
                       elim (H id); split; auto.
                       apply in_or_app; left; auto.
                   --- apply in_app_or in H0.
                       destruct H0; auto.
                       apply NoDup_app_remove_l in H.
                       apply NoDup_app_disj in H.
                       elim (H id); split; auto.
                       apply In_path_in_tree in H1; auto.
          -- apply IHo1; auto.
             ++ apply NoDup_app_remove_r in H; auto.
             ++ apply in_app_or in H0.
                destruct H0; auto.
                apply NoDup_app_disj in H.
                elim (H id); split; auto.
                apply In_path_in_tree in H1; auto.
        * destruct b0; simpl in *; auto.
          destruct data; simpl in *; auto; repeat rewrite map_app in *.
          -- apply in_or_app.
             apply in_app_or in H1.
             destruct H1.
             ++ left. auto.
             ++ right. apply IHo2; auto.
                ** do 2 apply NoDup_app_remove_l in H; auto.
                ** apply in_app_or in H0.
                   destruct H0.
                   --- apply In_path_in_tree in H1.
                       apply NoDup_app_disj in H.
                       elim (H id); split; auto.
                       apply in_or_app; right; auto.
                   --- apply in_app_or in H0.
                       destruct H0; auto.
                       apply NoDup_app_remove_l in H.
                       apply NoDup_app_disj in H.
                       elim (H id); split; auto.
                       apply In_path_in_tree in H1; auto.
          -- apply IHo2; auto.
             ++ apply NoDup_app_remove_l in H; auto.
             ++ apply in_app_or in H0.
                destruct H0; auto.
                apply NoDup_app_disj in H.
                elim (H id); split; auto.
                apply In_path_in_tree in H1; auto.
  Qed.

  Lemma get_write_back_blocks_pos_map : forall id p stsh lvl pos_map,
      In id (List.map block_blockid
               (get_write_back_blocks p stsh 4 lvl pos_map)) ->
      let p' := lookup_dict (makeBoolList false LOP) id pos_map in
      isEqvPath p p' lvl = true.
  Proof.
    intros.
    unfold p'.
    rewrite in_map_iff in H.
    destruct H as [b [Hb1 Hb2]].
    unfold get_write_back_blocks in Hb2.
    destruct (length stsh); auto.
    apply takeL_in in Hb2.
    induction stsh; simpl in *; auto.
    destruct isEqvPath eqn:p_cond; auto.
    destruct Hb2; auto.
    rewrite H in p_cond.
    rewrite Hb1 in p_cond; auto.
  Qed.

  Lemma isEqvPath_lookup_path_oram : forall o n id lvl dlt p p',
      is_p_b_tr o (S n) ->
      length p = n ->
      length p' = n ->
      (lvl < n)%nat ->
      In id (List.map block_blockid dlt) ->
      isEqvPath p p' lvl = true ->
      In id (List.map block_blockid
               (concat (lookup_path_oram
                          (up_oram_tr o lvl dlt p) p'))).
  Proof.
    induction o; simpl; intros; auto.
    destruct lvl; simpl; auto.
    - destruct p'; simpl; auto.
      + rewrite app_nil_r; auto.
      + destruct b; simpl; rewrite map_app; apply in_or_app; left; auto.
    - destruct p; simpl; auto.
      + simpl in H0. lia.
      + destruct b; simpl; auto.
        * destruct p'; simpl; auto.
          -- simpl in H1. lia.
          -- destruct b; [|discriminate].
             destruct data.
             ++ simpl.
                rewrite map_app.
                apply in_or_app; right.
                destruct n as [|k]; [simpl in *; discriminate|].
                destruct H.
                apply IHo1 with (n := k); auto. lia.
             ++ destruct n as [|k]; [simpl in *; discriminate|].
                destruct H.
                apply IHo1 with (n := k); auto. lia.
        * destruct p'; simpl; auto.
          -- simpl in H1. lia.
          -- destruct b; [discriminate|].
             destruct data.
             ++ simpl.
                rewrite map_app.
                apply in_or_app; right.
                destruct n as [|k]; [simpl in *; discriminate|].
                destruct H.
                apply IHo2 with (n := k); auto. lia.
             ++ destruct n as [|k]; [simpl in *; discriminate|].
                destruct H.
                apply IHo2 with (n := k); auto. lia.
  Qed.
  
  Lemma blocks_selection_wf : forall
      (p : path) (lvl : nat) (s : state),
      well_formed s ->
      length p = LOP ->
      (lvl < LOP)%nat ->
      well_formed (blocks_selection p lvl s).
  Proof.
    intros.
    destruct H.
    constructor; simpl.
    - remember (get_write_back_blocks p (state_stash s) 4 lvl
                  (state_position_map s)) as dlt.
      apply NoDup_remove_list_sub. auto.
    - apply NoDup_up_oram_tree; auto.
      + apply NoDup_get_write_back_blocks. auto.
      + eapply disjoint_weaken2; eauto.
        apply get_write_back_blocks_subset.
    - apply disjoint_dlt; auto.
      + apply get_write_back_blocks_subset.
    - apply up_oram_tr_preserves_pb; auto.
    - intros id Hid.
      pose proof (Hid2 := Hid).
      apply up_oram_tr_tree_or_delta in Hid2.
      destruct Hid2 as [Hid2|Hid2].
      + apply blk_in_path_in_tree in Hid2.
        apply in_up_oram_tr; auto.      
      + apply isEqvPath_lookup_path_oram with (n := LOP); auto.
        eapply get_write_back_blocks_pos_map; eauto.
    - auto.
  Qed.

  Lemma write_back_wf : forall (step start : nat) (s : state) (p : path), 
      length p = LOP ->
      well_formed s ->
      Nat.le (start + step) LOP ->
      well_formed (write_back_r start p step  s).
  Proof.
    induction step; intros.
    - exact H0.
    - apply blocks_selection_wf; auto; try lia.
      apply IHstep; auto; try lia.
  Qed.

  Lemma write_back_in_stash_kv_rel_aux : forall n s p id v start,
      well_formed s ->
      length p = LOP ->
      Nat.le (start + n) LOP ->
      blk_in_stash id v s ->
      blk_in_stash id v (write_back_r start p n s) \/
        exists k, (start <= k /\ 
                at_lvl_in_path (state_oram (write_back_r start p n s)) k p (Block id v) /\
                at_lvl_in_path (state_oram (write_back_r start p n s)) k (calc_path id s) (Block id v))%nat.
  Proof.
    induction n; intros.
    - left; auto.
    - destruct (IHn s p id v (S start) H H0); auto; try lia.
      + unfold write_back_r at 1.
        simpl iterate_right at 1.
        assert (Nat.le start LOP) by lia.
        destruct (stash_block_selection p (write_back_r (S start) p n s) id v start) as [Hs | Hr] ; auto.
        * apply write_back_wf; auto; try lia.
        * right.
          exists start; auto.
          repeat split; auto ; try tauto.
          destruct Hr. rewrite calc_path_write_bk_r_stable in H6.
          exact H6.
      + destruct H3 as [k [Hk1 Hk2]].
        right; exists k.
        split; [lia|].
        unfold write_back_r; simpl iterate_right.
        split; destruct Hk2.
        * apply at_lvl_in_path_blocks_selection; auto.
        * apply at_lvl_in_path_blocks_selection; auto.
  Qed. 

  Lemma locate_node_in_path : forall o lvl p b,
      locate_node_in_tr o lvl p = Some b ->
      In b (lookup_path_oram o p).
  Proof.
    induction o.
    - intros.
      destruct p.
      + inversion H.
      + destruct b0; simpl in *; discriminate.
    - intros.
      destruct p.
      + unfold locate_node_in_tr in H.
        simpl.
        destruct lvl; try discriminate.
        destruct data; 
          inversion H; subst; try discriminate. left. auto.
      + destruct lvl; simpl in *.
        destruct b0; simpl.
        destruct data; simpl.
        * left. inversion H. reflexivity.
        * discriminate.
        * destruct data; simpl.
          -- left. inversion H. reflexivity.
          -- discriminate.
        * destruct b0; simpl in *.
          destruct data; simpl.
          -- right. eapply IHo1; eauto.
          -- eapply IHo1; eauto.
          -- destruct data; simpl.
             ++ right.  eapply IHo2; eauto.
             ++ eapply IHo2; eauto.
  Qed.

  Lemma weaken_at_lvl_in_path : forall o lvl p id v,
      at_lvl_in_path o lvl p (Block id v) ->
      blk_in_p id v o p.
  Proof.
    intros.
    unfold at_lvl_in_path in *.
    destruct locate_node_in_tr eqn:?; [|tauto].
    unfold blk_in_path.
    unfold blk_in_p.
    rewrite in_concat.
    exists b. split; auto.
    apply locate_node_in_path with (lvl := lvl); auto.
  Qed.
  
  Lemma write_back_in_stash_kv_rel : forall s id v p,
      well_formed s ->
      length p = LOP ->
      blk_in_stash id v s ->
      kv_rel id v (write_back_r O p (length p) s).
  Proof.
    intros.
    destruct (write_back_in_stash_kv_rel_aux (length p) s p id v 0 H); auto; try lia.
    - left; auto.
    - destruct H2 as [k [_ Hk]].
      right.
      eapply weaken_at_lvl_in_path.
      rewrite calc_path_write_bk_r_stable.
      destruct Hk.
      eauto.
  Qed.

  Lemma get_post_wb_st_stsh_kvr : forall (id : block_id) (v : nat) (s : state) (p : path),
      well_formed s ->
      length p = LOP ->
      blk_in_stash id v s -> 
      kv_rel id v (get_post_wb_st s p).
  Proof.
    intros.
    unfold get_post_wb_st.
    apply write_back_in_stash_kv_rel; simpl; auto. 
  Qed.

  Definition empty_on_path o p :=
    forall lvl, locate_node_in_tr o lvl p = None.

  Fixpoint diverge_at_level (p p' : path) (lvl : nat) :=
    match lvl with
    | 0%nat => False
    | S lvl' =>
      match p, p' with
      | [], [] => False
      | (true :: p_tail), (true :: p'_tail) =>
        diverge_at_level p_tail p'_tail lvl'
      | (false :: p_tail), (false :: p'_tail) =>
        diverge_at_level p_tail p'_tail lvl'
      | _, _ => True
      end
    end.

  (* off_path id v o p p' means that (id, v) lies on
      p' and not on p *)
  Definition off_path id v o p p' :=
    exists lvl,
      diverge_at_level p p' lvl /\
      match lookup_tree o lvl p' with
      | Some (Some bucket) => In (Block id v) bucket
      | _ => False
      end.

  Lemma empty_on_path_true ob o1 o2 p :
    empty_on_path (node ob o1 o2) (true :: p) ->
    empty_on_path o1 p.
  Proof.
    intros pf lvl.
    specialize (pf (S lvl)).
    exact pf.
  Qed.

  Lemma empty_on_path_false ob o1 o2 p :
    empty_on_path (node ob o1 o2) (false :: p) ->
    empty_on_path o2 p.
  Proof.
    intros pf lvl.
    specialize (pf (S lvl)).
    exact pf.
  Qed.

  Lemma lookup_tree_lookup_path_oram_invert o : forall bkt p,
    In bkt (lookup_path_oram o p) -> exists lvl,
    lookup_tree o lvl p = Some (Some bkt).
  Proof.
    induction o; intros bkt p pf.
    - destruct pf.
    - destruct p as [|[]].
      + exists 0%nat.
        simpl in *.
        destruct data; simpl in *; [|tauto].
        destruct pf; [|tauto].
        congruence.
      + simpl in pf.
        destruct data.
        * destruct pf.
          -- exists 0%nat. simpl; congruence.
          -- apply IHo1 in H.
             destruct H as [lvl Hlvl].
             exists (S lvl); exact Hlvl.
        * apply IHo1 in pf.
          destruct pf as [lvl Hlvl].
          exists (S lvl); exact Hlvl.
      + simpl in pf.
        destruct data.
        * destruct pf.
          -- exists 0%nat. simpl; congruence.
          -- apply IHo2 in H.
             destruct H as [lvl Hlvl].
             exists (S lvl); exact Hlvl.
        * apply IHo2 in pf.
          destruct pf as [lvl Hlvl].
          exists (S lvl); exact Hlvl.
  Qed.

  Lemma empty_true data o1 o2 p :
    empty_on_path (node data o1 o2) (true :: p) ->
    empty_on_path o1 p.
  Proof.
    intros pf lvl.
    specialize (pf (S lvl)).
    exact pf.
  Qed.

  Lemma empty_false data o1 o2 p :
    empty_on_path (node data o1 o2) (false :: p) ->
    empty_on_path o2 p.
  Proof.
    intros pf lvl.
    specialize (pf (S lvl)).
    exact pf.
  Qed.

  Lemma off_path_true id v data o1 o2 p p' :
    off_path id v o1 p p' ->
    off_path id v (node data o1 o2) (true :: p) (true :: p').
  Proof.
    intros [lvl [pf1 pf2]].
    exists (S lvl); split; simpl; auto.
  Qed.

  Lemma off_path_false id v data o1 o2 p p' :
    off_path id v o2 p p' ->
    off_path id v (node data o1 o2) (false :: p) (false :: p').
  Proof.
    intros [lvl [pf1 pf2]].
    exists (S lvl); split; simpl; auto.
  Qed.

  Lemma empty_off_path id v o : forall p p',
    blk_in_p id v o p' ->
    empty_on_path o p ->
    off_path id v o p p'.
  Proof.
    induction o; intros.
    - inversion H.
    - destruct data.
      + destruct p' as [|[]].
        * apply blk_in_p_nil_Some in H.
          specialize (H0 0%nat); discriminate.
        * apply blk_in_p_true_Some in H.
          destruct H.
          -- specialize (H0 0%nat); discriminate.
          -- destruct p as [|[]].
             ++ specialize (H0 0%nat); discriminate.
             ++ apply off_path_true.
                apply IHo1; auto.
                apply empty_true in H0; auto.
             ++ unfold blk_in_p in H.
                apply in_concat in H.
                destruct H as [bkt [Hbkt1 Hbkt2]].
                apply lookup_tree_lookup_path_oram_invert in Hbkt1.
                destruct Hbkt1 as [lvl Hlvl].
                exists (S lvl); simpl in *; split; auto.
                unfold bucket in Hlvl; rewrite Hlvl; auto.
        * apply blk_in_p_false_Some in H.
          destruct H.
          -- specialize (H0 0%nat); discriminate.
          -- destruct p as [|[]].
             ++ specialize (H0 0%nat); discriminate.
             ++ unfold blk_in_p in H.
                apply in_concat in H.
                destruct H as [bkt [Hbkt1 Hbkt2]].
                apply lookup_tree_lookup_path_oram_invert in Hbkt1.
                destruct Hbkt1 as [lvl Hlvl].
                exists (S lvl); simpl in *; split; auto.
                unfold bucket in Hlvl; rewrite Hlvl; auto.
             ++ apply off_path_false.
                apply IHo2; auto.
                apply empty_false in H0; auto.
      + destruct p' as [|[]].
        * apply blk_in_p_nil_None in H; tauto.
        * apply blk_in_p_true_None in H.
          destruct p as [|[]].
          ++ unfold blk_in_p in H.
             apply in_concat in H.
             destruct H as [bkt [Hbkt1 Hbkt2]].
             apply lookup_tree_lookup_path_oram_invert in Hbkt1.
             destruct Hbkt1 as [lvl Hlvl].
             exists (S lvl); simpl in *; split; auto.
             unfold bucket in Hlvl; rewrite Hlvl; auto.
          ++ apply off_path_true.
             apply IHo1; auto.
             apply empty_true in H0; auto.
          ++ unfold blk_in_p in H.
             apply in_concat in H.
             destruct H as [bkt [Hbkt1 Hbkt2]].
             apply lookup_tree_lookup_path_oram_invert in Hbkt1.
             destruct Hbkt1 as [lvl Hlvl].
             exists (S lvl); simpl in *; split; auto.
             unfold bucket in Hlvl; rewrite Hlvl; auto.
        * apply blk_in_p_false_None in H.
          destruct p as [|[]].
          ++ unfold blk_in_p in H.
             apply in_concat in H.
             destruct H as [bkt [Hbkt1 Hbkt2]].
             apply lookup_tree_lookup_path_oram_invert in Hbkt1.
             destruct Hbkt1 as [lvl Hlvl].
             exists (S lvl); simpl in *; split; auto.
             unfold bucket in Hlvl; rewrite Hlvl; auto.
          ++ unfold blk_in_p in H.
             apply in_concat in H.
             destruct H as [bkt [Hbkt1 Hbkt2]].
             apply lookup_tree_lookup_path_oram_invert in Hbkt1.
             destruct Hbkt1 as [lvl Hlvl].
             exists (S lvl); simpl in *; split; auto.
             unfold bucket in Hlvl; rewrite Hlvl; auto.
          ++ apply off_path_false.
             apply IHo2; auto.
             apply empty_false in H0; auto.
  Qed.

  Lemma lookup_tree_update_tree_diverge {X} (o : tree X) : forall
    (lvl lvl' : nat) (p p' : path) (x : X),
    diverge_at_level p' p lvl ->
    lookup_tree (update_tree o lvl' x p') lvl p =
    lookup_tree o lvl p.
  Proof.
    induction o; intros.
    - reflexivity.
    - destruct p'; simpl in *.
      + destruct lvl; [tauto|].
        destruct p; [tauto|].
        destruct lvl'; auto.
      + destruct lvl; [tauto|].
        destruct b.
        * destruct p.
          -- destruct lvl'; auto.
          -- destruct lvl'.
             ++ reflexivity.
             ++ destruct b; auto.
                simpl; apply IHo1; auto.
        * destruct p.
          -- destruct lvl'; auto.
          -- destruct lvl'.
             ++ reflexivity.
             ++ destruct b; auto.
                simpl; apply IHo2; auto.
  Qed.

  Lemma off_path_blocks_selection id v s p p' lvl :
    off_path id v (state_oram s) p p' ->
    off_path id v (state_oram (blocks_selection p lvl s)) p p'.
  Proof.
    intros [lvl' [pf1 pf2]].
    destruct lookup_tree eqn:?; [|tauto].
    destruct o; [|tauto].
    exists lvl'; split; auto.
    unfold blocks_selection; simpl.
    unfold up_oram_tr.
    rewrite lookup_tree_update_tree_diverge; auto.
    rewrite Heqo; auto.
  Qed.

  Lemma iterate_right_ind {X} (P : X -> Prop) (x : X) f p :
    P x ->
    (forall x n, P x -> P (f p n x)) ->
    forall steps start, P (iterate_right start p f steps x).
  Proof.
    intros Px Pf steps.
    induction steps; intro start.
    - exact Px.
    - apply Pf.
      apply IHsteps.
  Qed.

  Lemma iterate_right_inversion {X} (P : X -> Prop) (x : X) f p :
    (forall x n, P (f p n x) -> P x) ->
    forall steps start, P (iterate_right start p f steps x) ->
    P x.
  Proof.
    intros Pf_inv steps.
    induction steps; intros start pf.
    - exact pf.
    - simpl in pf; apply Pf_inv in pf.
      apply (IHsteps (S start)); auto.
  Qed.

  Lemma lookup_tree_lookup_path_oram o : forall bkt lvl p,
    lookup_tree o lvl p = Some (Some bkt) ->
    In bkt (lookup_path_oram o p).
  Proof.
    induction o; intros.
    - discriminate.
    - simpl in *.
      destruct lvl.
      + inversion H.
        destruct p as [|[]]; simpl; tauto.
      + destruct p as [|[]]; [discriminate| |].
        * apply IHo1 in H.
          destruct data; simpl; tauto.
        * apply IHo2 in H.
          destruct data; simpl; tauto.
  Qed.

  Lemma off_path_blk_in_p id v o p p' :
    off_path id v o p p' ->
    blk_in_p id v o p'.
  Proof.
    intros [lvl [pf1 pf2]].
    destruct lookup_tree eqn:?; [|tauto].
    destruct o0; [|tauto].
    unfold blk_in_p.
    apply in_concat; exists l.
    split; auto.
    apply lookup_tree_lookup_path_oram in Heqo0; auto.
  Qed.

  Lemma get_post_wb_st_kvr_kvr : forall (id : block_id) (v : nat) (s : state) (p : path),
      well_formed s ->
      length p = LOP ->
      empty_on_path (state_oram s) p ->
      kv_rel id v s -> 
      kv_rel id v (get_post_wb_st s p).
  Proof.
    intros.
    destruct H2.
    - apply get_post_wb_st_stsh_kvr; auto.
    - right.
      unfold blk_in_path in *.
      unfold get_post_wb_st; simpl.
      rewrite calc_path_write_bk_r_stable.
      pose (p' := calc_path id s); fold p' in H2. fold p'.
      apply off_path_blk_in_p with (p := p).
      unfold write_back_r.
      apply iterate_right_ind.
      + eapply empty_off_path; eauto.
      + intros x n.
        apply off_path_blocks_selection.
  Qed.

  Lemma up_oram_tr_inversion id v o : forall lvl delta p p',
    blk_in_p id v
      (up_oram_tr o lvl delta p) p' ->
    blk_in_p id v o p' \/
    In (Block id v) delta.
  Proof.
    unfold up_oram_tr.
    induction o; intros.
    - inversion H.
    - simpl update_tree in H.
      destruct lvl.
      + destruct p' as [|[]].
        * right.
          apply blk_in_p_nil_Some in H; auto.
        * apply blk_in_p_true_Some in H.
          destruct H.
          -- right; auto.
          -- left; apply blk_in_p_cons_true; auto.
        * apply blk_in_p_false_Some in H.
          destruct H.
          -- right; auto.
          -- left; apply blk_in_p_cons_false; auto.
      + destruct p as [|[]].
        * left; auto.
        * destruct p' as [|[]].
          -- destruct data.
             ++ apply blk_in_p_nil_Some in H.
                left.
                unfold blk_in_p; simpl.
                rewrite app_nil_r; auto.
             ++ apply blk_in_p_nil_None in H; tauto.
          -- destruct data.
             ++ apply blk_in_p_true_Some in H.
                destruct H.
                ** left.
                   unfold blk_in_p; simpl.
                   apply in_or_app; left; auto.
                ** apply IHo1 in H.
                   destruct H; [|tauto].
                   left; apply blk_in_p_cons_true; auto.
             ++ apply blk_in_p_true_None in H.
                apply IHo1 in H.
                destruct H; [|tauto].
                left; apply blk_in_p_cons_true; auto.
          -- destruct data.
             ++ apply blk_in_p_false_Some in H.
                destruct H.
                ** left.
                   unfold blk_in_p; simpl.
                   apply in_or_app; left; auto.
                ** left; apply blk_in_p_cons_false; auto.
             ++ apply blk_in_p_false_None in H.
                left. apply blk_in_p_cons_false; auto.
        * destruct p' as [|[]].
          -- destruct data.
             ++ apply blk_in_p_nil_Some in H.
                left.
                unfold blk_in_p; simpl.
                rewrite app_nil_r; auto.
             ++ apply blk_in_p_nil_None in H; tauto.
          -- destruct data.
             ++ apply blk_in_p_true_Some in H.
                destruct H.
                ** left.
                   unfold blk_in_p; simpl.
                   apply in_or_app; left; auto.
                ** left; apply blk_in_p_cons_true; auto.
             ++ apply blk_in_p_true_None in H.
                left. apply blk_in_p_cons_true; auto.
          -- destruct data.
             ++ apply blk_in_p_false_Some in H.
                destruct H.
                ** left.
                   unfold blk_in_p; simpl.
                   apply in_or_app; left; auto.
                ** apply IHo2 in H.
                   destruct H; [|tauto].
                   left; apply blk_in_p_cons_false; auto.
             ++ apply blk_in_p_false_None in H.
                apply IHo2 in H.
                destruct H; [|tauto].
                left; apply blk_in_p_cons_false; auto.
  Qed.

  Lemma distribute_via_get_post_wb_st_undef : forall (id : block_id) (s : state) (p : path),
      well_formed s ->
      length p = LOP ->
      empty_on_path (state_oram s) p ->
      undef id s -> 
      undef id (get_post_wb_st s p).
  Proof.
    intros.
    intros [v Hv].
    apply H2.
    exists v.
    destruct Hv as [Hv|Hv].
    - left.
      unfold get_post_wb_st in Hv.
      unfold write_back_r in Hv.
      apply iterate_right_inversion in Hv; auto.
      clear Hv.
      unfold blk_in_stash, blocks_selection; simpl.
      intros x n pf.
      apply remove_list_sub_weaken in pf; auto.
    - apply or_intror with
        (A := blk_in_stash id v (get_post_wb_st s p)) in Hv.
      unfold get_post_wb_st in Hv.
      unfold write_back_r in Hv.
      apply iterate_right_inversion in Hv; auto.
      clear Hv.
      intros x n [Hid|Hid].
      + left; apply remove_list_sub_weaken in Hid; auto.
      + unfold blocks_selection in Hid.
        unfold blk_in_path in Hid.
        unfold calc_path in Hid.
        simpl in Hid.
        apply up_oram_tr_inversion in Hid.
        destruct Hid as [Hid|Hid].
        * right; auto.
        * left.
          apply get_write_back_blocks_subset in Hid; auto.
  Qed.

  Lemma NoDup_path_oram : forall o p,
      NoDup (List.map block_blockid (get_all_blks_tree o)) ->
      NoDup (List.map block_blockid (concat (lookup_path_oram o p))).
  Proof.
    induction o; intros.
    - constructor.
    - simpl in *.
      destruct p.
      + destruct data.
        * simpl.
          rewrite app_nil_r.
          repeat rewrite map_app in H.
          apply NoDup_app_remove_r in H; auto.
        * constructor.
      + destruct b.
        * destruct data.
          -- simpl in *.
             apply NoDup_disjointness.
             ++ repeat rewrite map_app in H.
                apply NoDup_app_remove_r in H; auto.
             ++ apply IHo1.
                repeat rewrite map_app in H.
                apply NoDup_app_remove_l in H; auto.
                apply NoDup_app_remove_r in H; auto.
             ++ intros id [Hid1 Hid2].
                apply In_path_in_tree in Hid2.
                repeat rewrite map_app in H.
                rewrite app_assoc in H.
                apply NoDup_app_remove_r in H.
                apply (NoDup_app_disj _ _ H id); split; auto.
          -- apply IHo1.
             rewrite map_app in H.
             apply NoDup_app_remove_r in H; auto.
        * destruct data.
          -- simpl in *.
             apply NoDup_disjointness.
             ++ repeat rewrite map_app in H.
                apply NoDup_app_remove_r in H; auto.
             ++ apply IHo2.
                repeat rewrite map_app in H.
                apply NoDup_app_remove_l in H; auto.
                apply NoDup_app_remove_l in H; auto.
             ++ intros id [Hid1 Hid2].
                apply In_path_in_tree in Hid2.
                repeat rewrite map_app in H.
                apply NoDup_app_remove_mid in H.
                apply (NoDup_app_disj _ _ H id); split; auto.
          -- apply IHo2.
             rewrite map_app in H.
             apply NoDup_app_remove_l in H; auto.
  Qed. 

  Lemma get_all_blks_tree_clear_path_weaken : forall o id p,
      In id (List.map block_blockid (get_all_blks_tree (clear_path o p))) ->
      In id (List.map block_blockid (get_all_blks_tree o)).
  Proof.
    induction o; intros.
    - auto.
    - destruct p; simpl in *; auto.
      + rewrite map_app in H.
        apply in_app_or in H.
        destruct H.
        * destruct data; repeat rewrite map_app.
          -- apply in_or_app; right.
             apply in_or_app; left; auto.
          -- apply in_or_app; left; auto.
        * destruct data; repeat rewrite map_app.
          -- apply in_or_app; right.
             apply in_or_app; right; auto.
          -- apply in_or_app; right; auto.
      + destruct b; simpl in *.
        * rewrite map_app in H.
          apply in_app_or in H.
          destruct H.
          -- destruct data; repeat rewrite map_app.
             ++ apply in_or_app; right.
                apply in_or_app; left; auto.
                eapply IHo1; eauto.
             ++ apply in_or_app; left.
                eapply IHo1; eauto.
          -- destruct data; repeat rewrite map_app.
             ++ apply in_or_app; right.
                apply in_or_app; right; auto.
             ++ apply in_or_app; right; auto.
        * destruct data; repeat rewrite map_app.
          -- rewrite map_app in H.
             apply in_app_or in H.
             destruct H.
             ++ apply in_or_app; right.
                apply in_or_app; left; auto.
             ++ apply in_or_app; right.
                apply in_or_app; right.
                eapply IHo2; eauto.
          -- rewrite map_app in H.
             apply in_app_or in H.
             destruct H.
             ++ apply in_or_app; left; auto.
             ++ apply in_or_app; right.
                eapply IHo2; eauto.
  Qed.

  Lemma NoDup_clear_path : forall o p,
      NoDup (List.map block_blockid (get_all_blks_tree o)) ->
      NoDup (List.map block_blockid (get_all_blks_tree (clear_path o p))).
  Proof.
    induction o; simpl in *; intros.
    - apply NoDup_nil.
    - destruct p; simpl.
      + destruct data; auto.
        repeat rewrite map_app in *.
        apply NoDup_app_remove_l in H. auto.
      + destruct b; simpl.
        * apply NoDup_disjointness.
          -- destruct data; apply IHo1.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                apply NoDup_app_remove_r in H.
                auto.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_r in H.
                auto.
          -- destruct data; simpl.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                apply NoDup_app_remove_l in H.
                auto.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                auto.
          -- intros id [Hid1 Hid2].
             apply get_all_blks_tree_clear_path_weaken in Hid1.
             destruct data; simpl.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                eapply NoDup_app_disj. exact H.
                split; eauto.
             ++ repeat rewrite map_app in *.
                eapply NoDup_app_disj. exact H.
                split; eauto.
        * apply NoDup_disjointness.
          -- destruct data; simpl.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                apply NoDup_app_remove_r in H.
                auto.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_r in H.
                auto.
          -- destruct data; apply IHo2.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                apply NoDup_app_remove_l in H.
                auto.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                auto.
          -- intros id [Hid1 Hid2].
             apply get_all_blks_tree_clear_path_weaken in Hid2.
             destruct data; simpl.
             ++ repeat rewrite map_app in *.
                apply NoDup_app_remove_l in H.
                eapply NoDup_app_disj. exact H.
                split; eauto.
             ++ repeat rewrite map_app in *.
                eapply NoDup_app_disj. exact H.
                split; eauto.
  Qed.
  
  Lemma clear_path_p_b_tree : forall o n p, 
      is_p_b_tr o n -> 
      is_p_b_tr (clear_path o p) n.
  Proof.
    induction o; auto; intros.
    destruct p.
    - simpl.
      destruct n.
      + inversion H.
      + split; destruct H; auto.
    - destruct b; simpl.
      destruct n.
      + inversion H.
      + inversion H. split.
        * apply IHo1; auto.
        * auto.
      + destruct n; auto.
        split.
        * inversion H. auto.
        * apply IHo2; auto. inversion H; auto.
  Qed.

  Lemma on_path_not_off_path: forall o p id,
      NoDup (List.map block_blockid (get_all_blks_tree o)) ->
      In id (List.map block_blockid (concat (lookup_path_oram o p))) ->
      ~ In id (List.map block_blockid (get_all_blks_tree (clear_path o p))).
  Proof.
    induction o; auto; intros.
    destruct p. 
    - destruct data; simpl in *.
      + repeat rewrite map_app in *.
        apply NoDup_app_disj in H.
        intro Hid.
        apply (H id); split.
        * simpl in H0.
          rewrite app_nil_r in H0; auto.
        * auto.
      + auto.
    - destruct data; simpl in *.
      + destruct b; simpl in *.
        * repeat rewrite map_app in *. (* true *)
          apply in_app_or in H0.
          destruct H0.
          -- apply NoDup_app_disj in H.
             intro Hid.
             apply (H id); split; auto.
             apply in_or_app.
             apply in_app_or in Hid.
             destruct Hid.
             ++ left. eapply get_all_blks_tree_clear_path_weaken. exact H1.
             ++ right. auto.
          -- intro.
             apply in_app_or in H1.
             destruct H1. 
             ++ apply (IHo1 p id); auto.
                apply NoDup_app_remove_l in H.
                apply NoDup_app_remove_r in H; auto.
             ++ apply NoDup_app_remove_l in H.
                apply NoDup_app_disj in H.
                apply (H id); split; auto.
                eapply In_path_in_tree. exact H0.
        * repeat rewrite map_app in *. (* false *)
          apply in_app_or in H0.
          destruct H0.
          -- apply NoDup_app_disj in H.
             intro Hid.
             apply (H id); split; auto.
             apply in_or_app.
             apply in_app_or in Hid.
             destruct Hid.
             ++ left. auto.
             ++ right. eapply get_all_blks_tree_clear_path_weaken. exact H1.
          -- intro.
             apply in_app_or in H1.
             destruct H1. 
             ++ apply (IHo2 p id); auto.
                ** apply NoDup_app_remove_l in H.
                   apply NoDup_app_remove_l in H; auto.
                ** apply NoDup_app_remove_l in H.
                   apply NoDup_app_disj in H.
                   elim (H id); split; auto.
                   eapply In_path_in_tree; eauto.                 
             ++ apply (IHo2 p id); auto.
                apply NoDup_app_remove_l in H.
                apply NoDup_app_remove_l in H; auto.
      + destruct b; simpl in *.
        * repeat rewrite map_app in *.
          pose proof (H' := H).
          apply NoDup_app_disj in H.
          intro Hid.
          apply (H id); split; auto.
          -- eapply In_path_in_tree; eauto.
          -- apply in_app_or in Hid.
             destruct Hid; auto.
             elim (IHo1 p id); auto.
             apply NoDup_app_remove_r in H'; auto.
        * repeat rewrite map_app in *.
          pose proof (H' := H).
          apply NoDup_app_disj in H.
          intro Hid.
          apply (H id); split; auto.
          -- apply in_app_or in Hid.
             destruct Hid; auto.
             elim (IHo2 p id); auto.
             apply NoDup_app_remove_l in H'; auto.
          -- eapply In_path_in_tree; eauto.
  Qed.

  Lemma disjoint_list_dlt : forall o p h,
      disjoint_list (List.map block_blockid (get_all_blks_tree o))
        (List.map block_blockid h) ->
      NoDup (List.map block_blockid (get_all_blks_tree o)) -> 
      disjoint_list (List.map block_blockid (get_all_blks_tree (clear_path o p)))
        (List.map block_blockid (concat (lookup_path_oram o p) ++ h)).
  Proof.
    intros.
    intros id [Hid1 Hid2].
    rewrite map_app in *.
    apply in_app_or in Hid2.
    destruct Hid2.
    - eapply on_path_not_off_path; eauto.
    - apply (H id); split; auto.
      eapply get_all_blks_tree_clear_path_weaken; eauto.
  Qed.
  
  Lemma disjoint_list_sub : forall {A} (l1 l2 l3: list A),
      (forall x, In x l1 -> In x l2) -> 
      disjoint_list l2 l3 ->
      disjoint_list l1 l3.
  Proof.
    intros.
    unfold disjoint_list in *.
    intros. unfold not in *.
    firstorder.
  Qed.

  Lemma lookup_off_path : forall o id p p',
      NoDup (List.map block_blockid (get_all_blks_tree o)) ->
      In id (List.map block_blockid (get_all_blks_tree (clear_path o p))) ->
      In id (List.map block_blockid (concat (lookup_path_oram o p'))) ->
      In id (List.map block_blockid (concat (lookup_path_oram (clear_path o p) p'))).
  Proof.
    induction o; intros; simpl in *; auto.
    destruct p; simpl in *.
    - destruct p'.
      + simpl.
        destruct data; auto.
        repeat rewrite map_app in *.
        apply NoDup_app_disj in H.
        simpl in H1; rewrite app_nil_r in H1.
        apply (H id); split; auto.
      + destruct b.
        * destruct data; simpl in *; auto.
          rewrite map_app in *.
          apply in_app_or in H1.
          destruct H1; auto.
          apply NoDup_app_disj in H.
          elim (H id); split; auto.
          rewrite map_app; auto.
        * destruct data; simpl in *; auto.
          rewrite map_app in *.
          apply in_app_or in H1.
          destruct H1; auto.
          apply NoDup_app_disj in H.
          elim (H id); split; auto.
          rewrite map_app; auto.
    - destruct p'.
      + destruct data; simpl in *.
        * rewrite app_nil_r in H1.
          destruct b.
          -- simpl in *.
             rewrite map_app in *.
             apply NoDup_app_disj in H.
             apply (H id); split; auto.
             rewrite map_app.
             rewrite in_app_iff in *.
             destruct H0; auto.
             left; eapply get_all_blks_tree_clear_path_weaken; eauto.
          -- simpl in *.
             rewrite map_app in *.
             apply NoDup_app_disj in H.
             apply (H id); split; auto.
             rewrite map_app.
             rewrite in_app_iff in *.
             destruct H0; auto.
             right; eapply get_all_blks_tree_clear_path_weaken; eauto.
        * contradiction.
      + destruct b0; simpl in *.
        * destruct data; simpl in *.
          -- destruct b; simpl in *.
             ++ repeat rewrite map_app in *.
                apply in_app_or in H1.
                destruct H1.
                ** apply NoDup_app_disj in H.
                   elim (H id); split; auto.
                   apply in_app_or in H0.
                   apply in_or_app.
                   destruct H0; auto.
                   left. eapply get_all_blks_tree_clear_path_weaken; eauto.
                ** apply IHo1; auto.
                   --- apply NoDup_app_remove_l in H.
                       apply NoDup_app_remove_r in H; auto.
                   --- apply in_app_or in H0.
                       destruct H0; auto.
                       apply NoDup_app_remove_l in H.
                       apply NoDup_app_disj in H.
                       elim (H id); split; auto.
                       eapply In_path_in_tree; eauto.
             ++ repeat rewrite map_app in *.
                apply in_app_or in H1.
                destruct H1; auto.
                apply NoDup_app_disj in H.
                elim (H id); split; auto.
                apply in_or_app.
                apply in_app_or in H0.
                destruct H0; auto.
                right. eapply get_all_blks_tree_clear_path_weaken; eauto.
          -- destruct b; simpl in *; auto. 
             repeat rewrite map_app in *.
             apply in_app_or in H0.
             destruct H0.
             ++ apply IHo1; auto.
                apply NoDup_app_remove_r in H; auto.
             ++ apply NoDup_app_disj in H.
                elim (H id); split; auto.
                eapply In_path_in_tree; eauto.
        * destruct data; simpl in *.
          -- destruct b; simpl in *.
             ++ repeat rewrite map_app in *.
                apply in_app_or in H1.
                destruct H1; auto.
                apply NoDup_app_disj in H.
                elim (H id); split; auto.
                apply in_or_app.
                apply in_app_or in H0.
                destruct H0; auto.
                left. eapply get_all_blks_tree_clear_path_weaken; eauto.
             ++ repeat rewrite map_app in *.
                apply in_app_or in H1.
                destruct H1; auto.
                ** apply NoDup_app_disj in H.
                   elim (H id); split; auto.
                   apply in_or_app.
                   apply in_app_or in H0.
                   destruct H0; auto.
                   right. eapply get_all_blks_tree_clear_path_weaken; eauto.
                ** apply IHo2; auto.
                   --- apply NoDup_app_remove_l in H.
                       apply NoDup_app_remove_l in H; auto.
                   --- apply in_app_or in H0.
                       destruct H0; auto.
                       apply NoDup_app_remove_l in H.
                       apply NoDup_app_disj in H.
                       elim (H id); split; auto.
                       eapply In_path_in_tree; eauto.
          -- destruct b; simpl in *; auto. 
             repeat rewrite map_app in *.
             apply in_app_or in H0.
             destruct H0; auto.
             ++ apply NoDup_app_disj in H.
                elim (H id); split; auto.
                eapply In_path_in_tree; eauto.
             ++ apply IHo2; auto.
                apply NoDup_app_remove_l in H; auto.
  Qed.

  Lemma rd_op_wf : forall (id : block_id) (m : position_map) (h : stash) (o : oram) (p p_new : path),
      lookup_dict (makeBoolList false LOP) id m = p ->
      well_formed (State m h o) -> length p_new = LOP -> 
      well_formed
        {|
          state_position_map := update_dict id p_new m;
          state_stash := (concat (lookup_path_oram o p) ++ h)%list;
          state_oram := clear_path o p
        |}.
  Proof.
    intros.
    destruct H0.
    constructor; simpl in *.
    - apply NoDup_disjointness.
      + apply NoDup_path_oram. auto.
      + auto.
      + apply disjoint_list_sub with
          (l2 := List.map block_blockid (get_all_blks_tree o)); auto.
        intros. apply In_path_in_tree with (p := p). exact H0.
    - apply NoDup_clear_path. auto.
    - apply disjoint_list_dlt. auto. auto.
    - apply clear_path_p_b_tree. auto.
    - intros id' Hid'.
      destruct (id =? id') eqn:id_cond.
      + rewrite Nat.eqb_eq in id_cond. 
        rewrite <- id_cond in *; clear id_cond.
        pose (get_all_blks_tree_clear_path_weaken _ _ _ Hid') as Hid'2.
        specialize (blk_in_path_in_tree id Hid'2).
        rewrite H in blk_in_path_in_tree; clear Hid'2.
        elim on_path_not_off_path with (id := id) (o := o) (p := p); auto.
      + rewrite Nat.eqb_neq in id_cond.
        rewrite lookup_update_diffid; auto.
        apply lookup_off_path; auto.
        apply blk_in_path_in_tree.
        eapply get_all_blks_tree_clear_path_weaken; eauto.
    - intro.
      destruct (Nat.eqb id id0) eqn : id_cond.
      + rewrite Nat.eqb_eq in id_cond. rewrite id_cond. rewrite lookup_update_sameid.
        auto.
      + rewrite lookup_update_diffid. auto.
        rewrite Nat.eqb_neq in id_cond. auto.
  Qed.

  Lemma not_in_removed : forall l id,
      ~ In id
        (List.map block_blockid
           (remove_list (fun blk : block => block_blockid blk =? id)
              l)).
  Proof.
    intros.
    rewrite in_map_iff.
    intros [b [Hb1 Hb2]].
    rewrite In_remove_list_iff in Hb2.
    destruct Hb2 as [_ Hb2].
    rewrite Hb1 in Hb2.
    simpl in Hb2.
    rewrite Nat.eqb_neq in Hb2.
    contradiction.
  Qed.

  Lemma NoDup_remove_list: forall l id,
      NoDup (List.map block_blockid l) -> 
      NoDup
        (List.map block_blockid
           (remove_list (fun blk : block => block_blockid blk =? id)
              l)).
  Proof.
    induction l; simpl; intros; auto.
    destruct (block_blockid a =? id).
    - apply IHl; auto.
      inversion H; auto.
    - simpl.
      constructor.
      + intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [b [Hb1 Hb2]].
        rewrite In_remove_list_iff in Hb2.
        destruct Hb2 as [Hb2 Hb3].
        inversion H.
        rewrite <- Hb1 in H2.
        apply H2.
        apply in_map; auto.
      + apply IHl.
        inversion H; auto.
  Qed.
  
  Lemma wr_op_wf : forall (id : block_id) (v : nat) (m : position_map) (h : stash) (o : oram) (p p_new : path),
      well_formed (State m h o) -> length p_new = LOP ->
      lookup_dict (makeBoolList false LOP) id m = p ->
      well_formed
        {|
          state_position_map := update_dict id p_new m;
          state_stash :=
            {| block_blockid := id; block_payload := v |}
              :: remove_list (fun blk : block => block_blockid blk =? id)
              (concat (lookup_path_oram o p) ++ h);
          state_oram := clear_path o p
        |}.
  Proof.
    intros.
    destruct H.
    constructor; simpl in *.
    - rewrite NoDup_cons_iff; split.
      + apply not_in_removed.
      + apply NoDup_remove_list.
        apply NoDup_disjointness; auto.
        * apply NoDup_path_oram; auto.
        * eapply disjoint_list_sub.
          -- apply In_path_in_tree.
          -- auto.
    - apply NoDup_clear_path. auto.
    - intros id' [Hid'1 Hid'2].
      destruct Hid'2.
      + rewrite <- H in Hid'1; clear H.
        apply on_path_not_off_path with (id := id) (o := o) (p := p); auto.
        rewrite <- H1.
        apply blk_in_path_in_tree.
        eapply get_all_blks_tree_clear_path_weaken; eauto.
      + eapply disjoint_list_dlt; eauto; split; eauto.
        rewrite in_map_iff in *.
        destruct H as [b [Hb1 Hb2]].
        exists b; split; auto.
        rewrite In_remove_list_iff in Hb2; destruct Hb2; auto.
    - apply clear_path_p_b_tree. auto.
    - intros id' Hid'.
      destruct (id =? id') eqn:id_cond.
      + rewrite Nat.eqb_eq in id_cond. 
        rewrite <- id_cond in *; clear id_cond.
        pose (get_all_blks_tree_clear_path_weaken _ _ _ Hid') as Hid'2.
        specialize (blk_in_path_in_tree id Hid'2).
        rewrite H1 in blk_in_path_in_tree; clear Hid'2.
        elim on_path_not_off_path with (id := id) (o := o) (p := p); auto.
      + rewrite Nat.eqb_neq in id_cond.
        rewrite lookup_update_diffid; auto.
        apply lookup_off_path; auto.
        apply blk_in_path_in_tree.
        eapply get_all_blks_tree_clear_path_weaken; eauto.
    - intro.
      destruct (Nat.eqb id id0) eqn : id_cond.
      + rewrite Nat.eqb_eq in id_cond. rewrite id_cond. rewrite lookup_update_sameid.
        auto.
      + rewrite lookup_update_diffid. auto.
        rewrite Nat.eqb_neq in id_cond. auto.
  Qed.

  Lemma get_pre_wb_st_wf : forall (id : block_id) (op : operation) (m : position_map) (h : stash) (o : oram) (p p_new : path),
      well_formed (State m h o) ->
      length p_new = LOP ->
      lookup_dict (makeBoolList false LOP) id m = p ->    
      well_formed (get_pre_wb_st id op m h o p p_new).
  Proof.
    intros.
    unfold get_pre_wb_st.
    destruct op. 
    - simpl. apply rd_op_wf; auto.
    - simpl. apply wr_op_wf; auto.
  Qed.

  Lemma get_post_wb_st_wf : forall (s : state) (p : path),
      well_formed s ->
      length p = LOP ->
      well_formed (get_post_wb_st s p).
  Proof.
    intros.
    unfold get_post_wb_st.
    apply write_back_wf; auto; lia.
  Qed.

  Lemma zero_sum_stsh_tr_Wr
    (s : state) (id : block_id) (v : nat) (p p_new : path):
    well_formed s ->
    length p = LOP ->
    length p_new = LOP ->
    kv_rel id v
      (get_post_wb_st
         (get_pre_wb_st id (Write v)
            (state_position_map s) (state_stash s) (state_oram s)
            (calc_path id s) p_new) p).
  Proof.
    intros.
    apply get_post_wb_st_stsh_kvr; auto.
    - apply get_pre_wb_st_wf; auto.
      destruct s; auto.
    - apply get_pre_wb_st_Write_stsh.
  Qed.
  
  Lemma zero_sum_stsh_tr_Rd_rev :
    forall (id : block_id) (v : nat) (s : state) (p p_new : path),
      well_formed s ->
      length p = LOP ->
      length p_new = LOP -> 
      kv_rel id v s  -> 
      kv_rel id v (get_post_wb_st
                     (get_pre_wb_st id Read (state_position_map s)
                        (state_stash s)
                        (state_oram s)
                        (calc_path id s) p_new) p). 
  Proof.
    intros.
    apply get_post_wb_st_stsh_kvr; auto.
    - apply get_pre_wb_st_wf; auto. destruct s; auto.
    - apply stash_path_combined_rel_Rd. auto.
  Qed.

  Lemma locate_node_in_tr_clear_path o : forall p lvl,
    locate_node_in_tr (clear_path o p) lvl p = None.
  Proof.
    unfold locate_node_in_tr.
    induction o; intros.
    - reflexivity.
    - destruct p; simpl.
      + destruct lvl; reflexivity.
      + destruct b, lvl; simpl; auto.
  Qed.

  Lemma read_access_kvr_kvr :
    forall (id id' : block_id) (v : nat) (s : state) (p_new : path),
      well_formed s ->
      length p_new = LOP -> 
      kv_rel id v s  -> 
      kv_rel id v (get_post_wb_st
                     (get_pre_wb_st id' Read (state_position_map s)
                        (state_stash s)
                        (state_oram s)
                        (calc_path id' s) p_new) (calc_path id' s)). 
  Proof.
    intros.
    apply get_post_wb_st_kvr_kvr; auto.
    - apply get_pre_wb_st_wf; auto. destruct s; auto.
    - apply H.
    - unfold get_pre_wb_st; simpl.
      intro lvl.
      apply locate_node_in_tr_clear_path.
    - apply get_pre_wb_st_Read_kvr_kvr; auto.
  Qed.

  
  Lemma write_access_kvr_kvr :
    forall (id id' : block_id) (v v': nat) (s : state) (p_new : path),
      id <> id' -> 
      well_formed s ->
      length p_new = LOP -> 
      kv_rel id v s  -> 
      kv_rel id v (get_post_wb_st
                     (get_pre_wb_st id' (Write v') (state_position_map s)
                        (state_stash s)
                        (state_oram s)
                        (calc_path id' s) p_new) (calc_path id' s)). 
  Proof.
    intros.
    apply get_post_wb_st_kvr_kvr; auto.
    - apply get_pre_wb_st_wf; auto. destruct s; auto.
    - apply H0.
    - unfold get_pre_wb_st; simpl.
      intro lvl.
      apply locate_node_in_tr_clear_path.
    - apply get_pre_wb_st_Write_kvr_kvr; auto.
  Qed.

  Lemma zero_sum_stsh_tr_Rd_rev_undef :
    forall (id id' : block_id) (s : state) (p_new : path),
      well_formed s ->
      length p_new = LOP -> 
      undef id s  -> 
      undef id (get_post_wb_st
                     (get_pre_wb_st id' Read (state_position_map s)
                        (state_stash s)
                        (state_oram s)
                        (calc_path id' s) p_new) (calc_path id' s)). 
  Proof.
    intros.
    apply distribute_via_get_post_wb_st_undef; auto.
    - apply get_pre_wb_st_wf; auto. destruct s; auto.
    - apply H.
    - unfold get_pre_wb_st; simpl.
      intro lvl.
      apply locate_node_in_tr_clear_path.
    - apply stash_path_combined_rel_Rd_undef; auto.
  Qed.

  Lemma zero_sum_stsh_tr_Wr_rev_undef :
    forall (id id' : block_id) (v : nat) (s : state) (p_new : path),
      well_formed s ->
      id <> id' -> 
      length p_new = LOP -> 
      undef id' s -> 
      undef id' (get_post_wb_st
                  (get_pre_wb_st id (Write v) (state_position_map s)
                     (state_stash s)
                     (state_oram s)
                     (calc_path id s) p_new) (calc_path id s)). 
  Proof.
    intros.
    apply distribute_via_get_post_wb_st_undef; auto.
    - apply get_pre_wb_st_wf; auto. destruct s; auto.
    - apply H.
    - unfold get_pre_wb_st; simpl.
      intro lvl.
      apply locate_node_in_tr_clear_path.
    - 
      apply stash_path_combined_rel_Wr_undef; auto.
  Qed.
    
  
  Lemma lookup_ret_data_block_in_list (id : block_id) (v : nat) (l : list block) :
    NoDup (List.map block_blockid l) ->
    In (Block id v) l -> lookup_ret_data id l = v.
  Proof.
    intro ND.
    intros.
    induction l; simpl; try contradiction.
    destruct (block_blockid a =? id) eqn: id_cond.
    - destruct H; simpl in *.
      + rewrite H; auto.
      + inversion ND; subst.
        rewrite Nat.eqb_eq in id_cond.
        rewrite id_cond in H2.
        apply List.in_map with (f := block_blockid) in H.
        simpl in *. contradiction.
    - apply IHl.
      + inversion ND; auto.
      + destruct H; auto.
        rewrite H in id_cond. simpl in *. rewrite Nat.eqb_neq in id_cond.
        contradiction.
  Qed.

  Lemma zero_sum_stsh_tr_Rd (id : block_id) (v : nat) (m : position_map) (h : stash) (o : oram) :
    well_formed (State m h o) ->
    kv_rel id v (State m h o) ->
    get_ret_data id h (calc_path id (State m h o)) o = v.
  Proof.
    simpl.
    intros.
    destruct H0. 
    - (* assume in stash *)
      apply lookup_ret_data_block_in_list.
      + apply NoDup_disjointness; try repeat apply H.
        * apply NoDup_path_oram. apply H.
        * destruct H.
          apply disjoint_list_sub with
            (l2 := List.map block_blockid (get_all_blks_tree o)); auto.
          intros. eapply In_path_in_tree. exact H.
      + apply in_or_app. right. auto.
    - (* assume in path *)
      apply lookup_ret_data_block_in_list.
      + apply NoDup_disjointness; try repeat apply H.
        * apply NoDup_path_oram. apply H.
        * destruct H.
          apply disjoint_list_sub with
            (l2 := List.map block_blockid (get_all_blks_tree o)); auto.
          intros. eapply In_path_in_tree. exact H.
      + unfold blk_in_path in H. simpl in *.
        apply in_or_app. left. auto.
  Qed.

  Lemma read_access_just_wf (id : block_id) :
    state_plift well_formed well_formed (fun _ => True) (read_access id).
  Proof.
    apply state_plift_bind with
      (Mid := well_formed)
      (P := well_formed).
    - apply state_plift_get.
    - intros.
      apply state_plift_bind with
        (Mid := well_formed) (P := fun p => length p = LOP).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros; simpl.
        apply state_plift_bind with
          (Mid := well_formed) (P := fun _ => True).
        * apply state_plift_put.
          apply get_post_wb_st_wf.
          -- apply get_pre_wb_st_wf; auto.
             destruct x; exact H.
          -- apply H.
        * intros _ _.
          apply state_plift_ret; auto.
  Qed.

  Lemma lookup_ret_data_0 k l :
    (forall v, ~ In {| block_blockid := k; block_payload := v |} l) ->
    lookup_ret_data k l = 0%nat.
  Proof.
    induction l; intro Hk.
    - reflexivity.
    - destruct a as [k' v]; simpl.
      destruct (k' =? k) eqn:Hk'.
      + rewrite Nat.eqb_eq in Hk'; subst.
        elim (Hk v); left; auto.
      + apply IHl; intro v'.
        simpl in *; firstorder.
  Qed.

  Lemma get_ret_data_0 k s :
    well_formed s ->
    undef k s ->
    get_ret_data k (state_stash s)
      (lookup_dict (makeBoolList false LOP) k (state_position_map s)) 
      (state_oram s) = 0%nat.
  Proof.
    intros wf_s Hks.
    unfold get_ret_data.
    apply lookup_ret_data_0.
    intros v Hv.
    apply in_app_or in Hv.
    destruct Hv as [Hv|Hv].
    - apply Hks; exists v.
      right.
      exact Hv.
    - apply Hks; exists v.
      left.
      exact Hv.
  Qed.

  Lemma read_access_undef_0 k :
    state_plift
      (fun st => well_formed st /\ undef k st)
      well_formed
      (has_value 0)
      (read_access k).
  Proof.
    eapply state_plift_bind.
    - apply state_plift_get.
    - intros s [wf_s Hks].
      eapply state_plift_bind.
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros p Hp. simpl in Hp.
        apply state_plift_bind with
          (Mid := well_formed)
          (P := fun _ => True).
        * apply state_plift_put.
          apply get_post_wb_st_wf; [|apply wf_s].
          apply get_pre_wb_st_wf; auto.
          destruct s; auto.
        * intros _ _.
          apply state_plift_ret.
          simpl; symmetry.
          apply get_ret_data_0; auto.
  Qed.

  Lemma read_access_wf (id : block_id)(v : nat) :
    state_plift (fun st => well_formed st /\ kv_rel id v st) (fun st => well_formed st /\ kv_rel id v st) (has_value v) (read_access id).
  Proof.
    remember (fun st : state => well_formed st /\ kv_rel id v st) as Inv. 
    apply (state_plift_bind Inv Inv).
    - apply state_plift_get.
    - intros.
      apply (state_plift_bind Inv (fun p => length p = LOP)).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros. simpl.
        apply (state_plift_bind Inv (fun _ => True)).
        * apply state_plift_put. rewrite HeqInv in H; destruct H.
          rewrite HeqInv. split.
          -- apply get_post_wb_st_wf; [|apply H].
             apply get_pre_wb_st_wf; auto. destruct x. exact H.
          -- apply zero_sum_stsh_tr_Rd_rev; auto. apply H. 
        * intros. rewrite HeqInv. apply state_plift_ret.
          rewrite HeqInv in H. destruct H. simpl.
          symmetry. apply zero_sum_stsh_tr_Rd; destruct x; auto.
  Qed.

  Lemma write_access_just_wf (id : block_id) (v : nat) :
    state_plift well_formed well_formed (fun _ => True)  
    (write_access id v).
  Proof.
    apply (state_plift_bind well_formed well_formed).
    - apply state_plift_get.
    - intros.
      apply (state_plift_bind well_formed (fun p => length p = LOP)).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros. simpl.
        apply (state_plift_bind well_formed (fun _ => True)).
        * apply state_plift_put; simpl.
          apply get_post_wb_st_wf; auto.
          -- apply get_pre_wb_st_wf; auto. destruct x; exact H.
          -- apply H.
        * intros. eapply state_plift_ret. auto.
  Qed.

  Lemma write_access_wf (id : block_id) (v : nat) :
    state_plift (fun st => well_formed st) (fun st => well_formed st /\ kv_rel id v st) (fun _ => True) (write_access id v).
  Proof.
    remember (fun st : state => well_formed st) as Inv.
    apply (state_plift_bind Inv Inv).
    - apply state_plift_get.
    - intros.
      rewrite HeqInv in H.
      apply (state_plift_bind Inv (fun p => length p = LOP)).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros. simpl.
        apply (state_plift_bind (fun st => well_formed st /\ kv_rel id v st) (fun _ => True)).
        * apply state_plift_put; simpl; split.
          apply get_post_wb_st_wf; auto.
          -- apply get_pre_wb_st_wf; auto. destruct x; exact H.
          -- apply H.
          -- apply zero_sum_stsh_tr_Wr; auto. 
             apply H.
        * intros. eapply state_plift_ret. auto.
  Qed.

  Lemma write_and_read_access_lift (id : block_id)(v : nat):
    state_plift (well_formed) well_formed (has_value v)
      (write_and_read_access id v).
  Proof.
    apply (state_plift_bind
             (fun st => well_formed st /\ kv_rel id v st)
             (fun _ => True)).
    - eapply write_access_wf.
    - intros _ _.
      apply (state_plift_weaken (fun st : state => well_formed st /\ kv_rel id v st)).
      + exact dist_has_weakening.
      + tauto.
      + apply read_access_wf.
  Qed.

  Lemma read_access_kv id v id' :
    state_plift
      (fun st => well_formed st /\ kv_rel id v st)
      (fun st => well_formed st /\ kv_rel id v st)
      (fun _ => True)
      (read_access id').
  Proof.
    remember (fun st : state => well_formed st /\ kv_rel id v st) as Inv. 
    apply (state_plift_bind Inv Inv).
    - apply state_plift_get.
    - intros.
      apply (state_plift_bind Inv (fun p => length p = LOP)).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros. simpl.
        apply (state_plift_bind Inv (fun _ => True)).
        * apply state_plift_put. rewrite HeqInv in H; destruct H.
          rewrite HeqInv. split.
          -- apply get_post_wb_st_wf; [|apply H].
             apply get_pre_wb_st_wf; auto. destruct x. exact H.
          -- apply read_access_kvr_kvr; auto.
        * intros. rewrite HeqInv. apply state_plift_ret; auto.
  Qed.

  Lemma read_access_undef id id' :
    state_plift
      (fun s => well_formed s /\ undef id s)
      (fun s : state => well_formed s /\ undef id s)
      (fun _ => True)
      (read_access id').
  Proof.
    remember (fun st : state => well_formed st /\ undef id st) as Inv. 
    apply (state_plift_bind Inv Inv).
    - apply state_plift_get.
    - intros.
      apply (state_plift_bind Inv (fun p => length p = LOP)).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros. simpl.
        apply (state_plift_bind Inv (fun _ => True)).
        * apply state_plift_put. rewrite HeqInv in H; destruct H.
          rewrite HeqInv. split.
          -- apply get_post_wb_st_wf; [|apply H].
             apply get_pre_wb_st_wf; auto. destruct x. exact H.
          -- apply zero_sum_stsh_tr_Rd_rev_undef; auto.
        * intros. rewrite HeqInv. apply state_plift_ret; auto.
  Qed.

  Lemma write_access_undef id id' v :
    id <> id' ->
    state_plift
      (fun s : state => well_formed s /\ undef id' s)
      (fun s : state => well_formed s /\ undef id' s)
      (fun _ => True) (write_access id v).
  Proof.
    intros Hneq.
    remember (fun st : state => well_formed st /\ undef id' st) as Inv. 
    apply (state_plift_bind Inv Inv).
    - apply state_plift_get.
    - intros.
      apply (state_plift_bind Inv (fun p => length p = LOP)).
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros. simpl.
        apply (state_plift_bind Inv (fun _ => True)).
        * apply state_plift_put.
          rewrite HeqInv in H; destruct H.
          rewrite HeqInv. split.
          -- apply get_post_wb_st_wf; [|apply H].
             apply get_pre_wb_st_wf; auto.
             destruct x. exact H.
          -- apply zero_sum_stsh_tr_Wr_rev_undef; auto. 
        * intros. rewrite HeqInv.
          apply state_plift_ret; auto.
  Qed.
    
  Lemma extract_payload (id : block_id) (v : nat) (s : state) : 
    plift (fun '(x, s') => has_value v x /\ well_formed s') (write_and_read_access id v s) -> 
    get_payload (write_and_read_access id v s) = v.
  Proof.
    intros ops_on_s.
    unfold get_payload.
    apply dist_lift_peek in ops_on_s.
    destruct peek.
    destruct p.
    destruct ops_on_s.
    unfold has_value in H.
    symmetry. auto.
  Qed.

  Theorem PathORAM_simulates_RAM_idx_eq (i : block_id) (v : nat) (s : state) :
    well_formed s -> 
    get_payload(write_and_read_access i v s) = v.
  Proof.
    intros wf_s.
    apply extract_payload.
    apply write_and_read_access_lift. auto.
  Qed.

  Lemma blk_in_stash_get_pre_wb_st :
    forall (s : state) (i k: block_id) (v v' : nat) (p p_new : path),
      blk_in_stash i v' s ->
      i <> k ->
      blk_in_stash i v'
        (get_pre_wb_st k
           (Write v)
           (state_position_map s)
           (state_stash s)
           (state_oram s)
           (calc_path k s)
           p_new).
  Proof.
    intros.
    unfold get_pre_wb_st.
    unfold blk_in_stash in *.
    simpl; right.
    apply In_remove_list.
    - apply in_or_app; right; auto.
    - simpl.
      rewrite Nat.eqb_neq; auto.
  Qed.

  Lemma blk_in_stash_get_post_wb_st :
    forall (s : state) (i : block_id) (v : nat) p,
      well_formed s ->
      length p = LOP ->
      blk_in_stash i v s ->
      kv_rel i v
        (get_post_wb_st s p).
  Proof.
    intros.
    unfold get_post_wb_st.
    apply get_post_wb_st_stsh_kvr; auto.
  Qed.
  
  Lemma blk_in_stash_neq : 
    forall (s : state) (i k: block_id) (v v' : nat) (p p_new : path),
      well_formed s ->
      length p = LOP ->
      length p_new = LOP ->
      blk_in_stash i v' s -> 
      i <> k -> 
      kv_rel i v'
        (get_post_wb_st
           (get_pre_wb_st k (Write v) (state_position_map s) (state_stash s) 
              (state_oram s) (calc_path k s) p_new) p).
  Proof.
    intros.
    apply blk_in_stash_get_post_wb_st; auto.
    apply get_pre_wb_st_wf; destruct s; auto.
    apply blk_in_stash_get_pre_wb_st; auto.
  Qed.
  
  Lemma write_access_neq : forall i k v v',
      i <> k -> 
      state_plift (fun s : state => well_formed s /\ kv_rel i v' s)
        (fun st : state => well_formed st /\ kv_rel i v' st)
        (fun _ =>  True)
        (write_access k v).
  Proof.
    intros.
    unfold write_access.
    unfold access.
    eapply state_plift_bind.
    - apply state_plift_get.
    - intros.
      eapply state_plift_bind.
      + apply state_plift_liftT.
        apply coin_flips_length.
      + intros p p_len.
        apply (state_plift_bind (fun st : state => well_formed st /\ kv_rel i v' st) (fun _ => True)).
        * apply state_plift_put.
          destruct H0; split.
          -- apply get_post_wb_st_wf; [|apply H0].
             apply get_pre_wb_st_wf; auto.
             destruct x; simpl in *; tauto.
          -- apply write_access_kvr_kvr; auto.
        * intros. apply state_plift_ret; auto.
  Qed.
  
  Theorem PathORAM_simulates_RAM_idx_neq :
    forall (i k : block_id) (v v' : nat),
      i <> k -> 
      state_plift
        (fun s => well_formed s /\ kv_rel i v' s)
        (fun s => well_formed s /\ kv_rel i v' s)
        (has_value v')
        (_ <- write_access k v ;; read_access i).
  Proof.
    intros.
    eapply state_plift_bind.
    - apply write_access_neq; auto.
    - intros [p x] _. apply read_access_wf. 
  Qed.

  Lemma value_pred_weaken :
    forall {X} (S : Type) (M : Type -> Type) `{PredLift M}
      (Pre Post: S -> Prop) (P Q : X -> Prop),
      (forall x, P x -> Q x) ->
      has_weakening M ->
      forall m, state_plift Pre Post P m ->
           state_plift Pre Post Q m.
  Proof.
    intros.
    unfold state_plift.
    intros.
    specialize (H3 s H4).
    unfold has_weakening in H2.
    apply H2 with (P := (fun '(x, s') => P x /\ Post s')).
    - intros. destruct x.  destruct H5. split. apply H1; tauto. auto.
    - auto.
  Qed.
  
End PORAM_PROOF.

Require Import Lia RAM.

Module Type ConfigParams.
  Parameter LOP : nat.

End ConfigParams.
  
Module Dist_State <: StateMonad.

  Definition state S X := dist (X * S).
  Definition State S X := S -> state S X.

  Definition ret {S X} := @StateT_ret S dist _ X.
  Definition bind {S X} := @StateT_bind S dist _ X.

  Definition get : forall {S}, State S S := fun S => get.
  Definition put : forall {S}, S -> State S unit := fun S => put.
    
End Dist_State.

(* Path ORAM is a RAM (functional correctness specification, WIP) *)
Module PathORAM (C : ConfigParams)<: RAM (Dist_State).

  #[export] Instance PoramConfig : Config := {LOP := C.LOP}.

  Definition K := block_id.
  Definition V := nat.
  Definition S : Type := state. 
  Definition Vw (V : Type) := prod path V.

  Module M := Dist_State.
  Definition bind {X Y} := @M.bind S X Y.
  Definition ret {X} := @M.ret S X.
  Definition get := @M.get S.
  Definition put := @M.put S.

  Definition well_formed s := 
    well_formed s. 

  Definition write k v := 
    write_access k v.

  Definition read k :=
    read_access k.

  Definition wrap v : Vw V := ([], v). (* path doesn't matter for this *)

  Definition get_payload (s : M.state S (Vw V)) : option V :=
   Some (get_payload s).

  Lemma extract_payload_read_read k (s : state) : 
    plift
      (fun '(x, s') => get_payload
        (bind (read k) ret s) = Some (snd x) /\ well_formed s')
      (bind (read k) (fun _ => read k) s) -> 
    get_payload
      (bind (read k) (fun _ => read k) s) = get_payload ((bind (read k) ret) s).
  Proof.
    intros.
    destruct (bind (read k) (fun _ => read k) s).
    destruct (bind (read k) ret s).
    unfold get_payload.
    destruct dist_pmf0, dist_pmf; try discriminate.
    simpl in *. destruct p. destruct p. destruct p.
    destruct p0. destruct p0. destruct p0.
    simpl in H. inversion H. destruct H2. simpl in *.
    unfold get_payload in H2.
    unfold PathORAMDef.get_payload in *.
    simpl in *.
    symmetry; auto.
  Qed.

  Definition opt_lift {X} (P : X -> Prop) : option X -> Prop :=
    fun o =>
      match o with
      | None => False
      | Some x => P x
      end.

  Lemma lift_payload {Pre Post : state -> Prop} {P : nat -> Prop} 
    (m : Poram (path * nat)) s :
    Pre s ->
    state_plift Pre Post (fun '(_,x) => P x) m ->
    opt_lift P (get_payload (m s)).
  Proof.
    intros Hs Hm.
    unfold get_payload.
    specialize (Hm s Hs).
    destruct (m s); simpl.
    destruct dist_pmf.
    - discriminate.
    - destruct p. destruct p. destruct p.
      inversion Hm.
      unfold PathORAMDef.get_payload.
      simpl.
      tauto.
  Qed.

  Lemma is_p_b_tr_height : forall (o:oram) n,
    is_p_b_tr o n ->
    get_height o = n.
  Proof.
    induction o; intros n Ho; simpl in *.
    - destruct n; auto.
      contradiction.
    - destruct n; destruct Ho.
      rewrite (IHo1 n); auto.
      rewrite (IHo2 n); auto.
      rewrite Nat.max_id; auto.
  Qed.

  Lemma get_height_wf : forall s,
      well_formed s ->
      get_height (state_oram s) = Datatypes.S LOP.
  Proof.
    intros s Hs.
    apply is_pb_tr in Hs.
    apply is_p_b_tr_height; auto.
  Qed.
  
  Lemma read_and_write_compat_lemma_1_aux:
    forall k v s,
      well_formed s ->
      get_payload ((bind (write k v) (fun _ => read k)) s) =
      get_payload (write_and_read_access k v s).
  Proof.
    intros k v s wf_s.
    reflexivity.
  Qed.

  Lemma read_and_write_compat_lemma_1 :
    forall k v s,
      well_formed s ->
      get_payload ((bind (write k v) (fun _ => read k)) s) =
      get_payload (write_and_read_access k v s).
  Proof.
    intros k v s wf_s.
    apply read_and_write_compat_lemma_1_aux.
    exact wf_s.
  Qed.

  Lemma read_and_write_compat_lemma_2 :
    forall k v s,
      get_payload ((bind (write k v) (fun _ => ret (wrap v))) s) = Some v.
  Proof.
    intros. unfold get_payload. unfold get_payload.
    destruct (bind (write k v) (fun _ : path * nat => ret (wrap v)) s) eqn:?.
    simpl. destruct dist_pmf.
    - discriminate.
    - destruct p. destruct p. destruct v0. f_equal.
      unfold bind in Heqd. unfold M.bind in Heqd. 
      unfold StateT_bind in Heqd. destruct (write k v s) eqn:?.
      simpl in Heqd. inversion Heqd. unfold mbind_dist_pmf in H0.
      simpl in H0. destruct dist_pmf0.
      + discriminate.
      + simpl in H0. destruct p0. simpl in H0. destruct p0. simpl in H0.
        unfold wrap in H0. inversion H0.
        reflexivity.
  Qed.

  (* --- RAM laws --- *)

  Theorem read_read :
    forall (k : K) (s : S), 
      well_formed s ->
      get_payload ((bind (read k) (fun _ => read k)) s) =
      get_payload ((bind (read k) (fun v => ret v)) s). 
  Proof.
  Admitted.
  
  Theorem read_write :
    forall (k : K) (v : nat) (s : S),
      well_formed s ->
      get_payload ((bind (write k v) (fun _ => read k)) s) =
      get_payload ((bind (write k v) (fun _ => ret (wrap v))) s).
  Proof.
    intros. rewrite read_and_write_compat_lemma_1; auto.
    rewrite read_and_write_compat_lemma_2.
    unfold get_payload.
    erewrite PathORAM_simulates_RAM_idx_eq; eauto.
  Qed.

  Theorem read_write_commute :
    forall (k1 k2 : K) (v : nat) f (s : S),
      well_formed s ->
      k1 <> k2 ->
      get_payload (bind (read k1) (fun v' => bind (write k2 v) (fun _ => f v')) s) =
      get_payload (bind (write k2 v) (fun _ => bind (read k1) f) s).
  Proof.
  Admitted.

  Theorem read_commute :
    forall (k1 k2 : K) f (s : S),
      well_formed s ->
      get_payload (bind (read k1) (fun v1 => bind (read k2) (fun v2 => f v1 v2)) s) =
      get_payload (bind (read k2) (fun v2 => bind (read k1) (fun v1 => f v1 v2)) s).
  Proof.
  Admitted.

End PathORAM.
