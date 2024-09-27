Require Import List.
Import ListNotations.

Require Import POram.System.PathORAMDef.
Require Import POram.Utils.Distributions.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import POram.System.PathORAMFunCorrect.
Require Import POram.System.Equiv.
Require Import POram.Utils.StateT.

Section EquivProofs.

Context `{C : Config}.

Definition read id : Poram nat :=
  monad_map snd (read_access id).

Definition write id v : Poram unit :=
  monad_map (fun _ => tt) (write_access id v).

Definition triv {X} : X -> Prop :=
  fun _ => True.

Definition pand {X} (P Q : X -> Prop) : X -> Prop :=
  fun x => P x /\ Q x.

Definition poram_lift {X} (Pre Post : state -> Prop)
  (P : X -> Prop) : Poram X -> Prop :=
  state_plift
    (pand well_formed Pre)
    (pand well_formed Post)
    P.

Definition state_plift2 {M} `{PredLift M} {S X Y}
  (Pre Post : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m1 : StateT S M X)
  (m2 : StateT S M Y) : Prop :=
  forall s1 s2,
    Pre s1 s2 ->
    plift2 (prod_rel P Post) (m1 s1) (m2 s2).

Definition state_plift2_val {M} `{PredLift M} {S X Y}
  (Pre : S -> S -> Prop)
  (Post : S -> S -> X -> Y -> Prop)
  (m1 : StateT S M X)
  (m2 : StateT S M Y) : Prop :=
  forall s1 s2,
    Pre s1 s2 ->
    plift2 (fun '(x, s) '(y, s') => Post s s' x y) (m1 s1) (m2 s2).

Definition poram_lift2 {X Y} (Pre Post : state -> state -> Prop)
  (P : X -> Y -> Prop) : Poram X -> Poram Y -> Prop :=
  state_plift2
    (fun s s' => well_formed s /\ well_formed s' /\ Pre s s')
    (fun s s' => well_formed s /\ well_formed s' /\ Post s s')
    P.

Definition poram_lift2_val {X Y} (Pre : state -> state -> Prop)
  (Post : state -> state -> X -> Y -> Prop) : Poram X -> Poram Y -> Prop :=
  state_plift2_val
    (fun s s' => well_formed s /\ well_formed s' /\ Pre s s')
    (fun s s' x y => well_formed s /\ well_formed s' /\ Post s s' x y).

Lemma poram_lift2_val_to_poram_lift2 {X Y}
  (Pre : state -> state -> Prop)
  (Post : state -> state -> Prop)
  (P : X -> Y -> Prop)
  (m1 : Poram X) (m2 : Poram Y) :
  poram_lift2_val Pre (fun s s' x y => Post s s' /\ P x y) m1 m2 ->
  poram_lift2 Pre Post P m1 m2.
Proof.
  intros Hm1m2 s s' pfs.
  specialize (Hm1m2 s s' pfs).
  eapply dist_has_weakening; [|exact Hm1m2].
  intros [x t] pf; simpl.
  eapply dist_has_weakening; [|exact pf].
  intros [y t'] pf'; simpl.
  unfold prod_rel; simpl; tauto.
Qed.

(*
Lemma state_plift2_bind {M} `{PredLift M}
  {S X Y X' Y'}
  (Pre Mid Post : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (Q : X' -> Y' -> Prop)
  (m1 : StateT S M X)
  (m2 : StateT S M Y)
  (f1 : X -> StateT S M X')
  (f2 : Y -> StateT S M Y') :
  state_plift2 Pre Mid P m1 m2 ->
  (forall x y, P x y ->
    state_plift2 Mid Post Q (f1 x) (f2 y)) ->
  state_plift2 Pre Post Q
    (mbind m1 f1) (mbind m2 f2).
Proof.
  intros Hm1m2 Hf1f2 s1 s2 Hs1s2.
  eapply plift2_bind.
  - apply Hm1m2; auto.
  - intros [x s] [y s'] [H1 H2]; simpl in *.
    apply Hf1f2; auto.
Qed.
*)

(*
Lemma poram_lift2_bind {X Y X' Y'}
  (Pre Mid Post : state -> state -> Prop)
  (P : X -> Y -> Prop)
  (Q : X' -> Y' -> Prop)
  (m1 : Poram X)
  (m2 : Poram Y)
  (f1 : X -> Poram X')
  (f2 : Y -> Poram Y') :
  poram_lift2 Pre Mid P m1 m2 ->
  (forall x y, P x y ->
    poram_lift2 Mid Post Q (f1 x) (f2 y)) ->
  poram_lift2 Pre Post Q
    (mbind m1 f1) (mbind m2 f2).
Proof.
  apply state_plift2_bind.
Qed.
*)

(*
Lemma poram_lift2_val_bind {X Y X' Y'}
  (Pre : state -> state -> Prop)
  (Mid : state -> state -> X -> Y -> Prop)
  (Post : state -> state -> X' -> Y' -> Prop)
  (m1 : Poram X)
  (m2 : Poram Y)
  (f1 : X -> Poram X')
  (f2 : Y -> Poram Y') :
  poram_lift2_val Pre Mid m1 m2 ->
  (forall x y,
    poram_lift2_val (fun s s' => Mid s s' x y) Post (f1 x) (f2 y)) ->
  poram_lift2_val Pre Post
    (mbind m1 f1) (mbind m2 f2).
Proof.
  intros Hm1m2 Hf1f2 s s' pfs.
  eapply plift2_bind.
  - apply Hm1m2; auto.
  - intros [x t] [y t'] pfs'.
    apply Hf1f2; auto.
Qed.
*)

Definition equiv {X} (m1 m2 : Poram X) : Prop :=
  poram_lift2
    state_equiv
    state_equiv
    eq m1 m2.

Lemma equiv_implies_poram_equiv {X}
  (m1 m2 : Poram X) :
  equiv m1 m2 ->
  poram_equiv eq m1 m2.
Proof.
  intros eqv s1 s2 Hs1s2 wf_s1 wf_s2.
  pose proof (conj wf_s1 (conj wf_s2 Hs1s2)) as pf.
  specialize (eqv s1 s2 pf).
  destruct (m1 s1), (m2 s2); simpl in *.
  eapply Forall_impl; [|exact eqv].
  intros [x s] Hxs.
  eapply Forall_impl; [|exact Hxs].
  intros [x' s'] [H1 [H2 [H3 H4]]].
  split; auto.
Qed.

Definition triv2 {X Y} : X -> Y -> Prop :=
  fun _ _ => True.

Definition pforall {I X} (P : I -> X -> Prop) : X -> Prop :=
  fun x => forall i, P i x.

Lemma plift_conj {X}
  (P Q : X -> Prop) (m : dist X) :
  plift P m ->
  plift Q m ->
  plift (pand P Q) m.
Proof.
  unfold plift; simpl.
  unfold dist_lift.
  destruct m as [l q]; simpl; clear q.
  repeat rewrite Forall_forall.
  intros; split; auto.
Qed.

Lemma plift_forall {I X}
  (P : I -> X -> Prop) (m : dist X) :
  (forall i, plift (P i) m) ->
  plift (pforall P) m.
Proof.
  intros.
  unfold pforall.
  unfold plift in *; simpl in *.
  destruct m as [l q]; simpl in *; clear q.
  rewrite Forall_forall.
  intros x Hx i.
  specialize (H i).
  rewrite Forall_forall in H.
  apply H; auto.
Qed.

Lemma poram_lift2_forall {I X Y} Pre
  (Post : I -> state -> state -> Prop)
  (P : X -> Y -> Prop) (m : Poram X) (m' : Poram Y) : I ->
  (forall i, poram_lift2 Pre (Post i) P m m') ->
  poram_lift2 Pre (fun x y => forall i, Post i x y) P m m'.
Proof.
  intros i H s s' pfs.
  unfold plift2; simpl.
  unfold dist_lift2.
  unfold plift; simpl.
  unfold dist_lift.
  pose proof (H i s s' pfs) as Hi.
  unfold plift2 in Hi; simpl in Hi.
  unfold dist_lift2 in Hi; simpl in Hi.
  unfold dist_lift in Hi.
  destruct (m s) as [l q] eqn:ms; simpl in *.
  destruct (m' s') as [l' q'] eqn:m's'; simpl in *.
  rewrite Forall_forall in *.
  intros p Hp.
  specialize (Hi p Hp).
  rewrite Forall_forall in *.
  intros p' Hp'.
  specialize (Hi p' Hp').
  destruct Hi; split; auto.
  do 2 (split; [tauto|]).
  intro j.
  pose proof (H j s s' pfs) as Hj.
  unfold plift2 in Hj; simpl in Hj.
  unfold dist_lift2 in Hj; simpl in Hj.
  unfold dist_lift in Hj.
  rewrite ms, m's' in Hj.
  rewrite Forall_forall in Hj.
  specialize (Hj p Hp).
  rewrite Forall_forall in Hj.
  destruct (Hj p' Hp'); tauto.
Qed.

Lemma blk_in_state_functional : forall s,
  well_formed s ->
  forall k v v',
    blk_in_state k v s ->
    blk_in_state k v' s ->
    v = v'.
Proof.
  intros s wf_s k v v' [Hv|Hv] [Hv'|Hv'].
  - apply no_dup_stash in wf_s.
    unfold blk_in_stash in *.
    apply NoDup.NoDup_map_inj in wf_s.
    unfold NoDup.inj_on_list in wf_s.
    specialize (wf_s _ _ Hv Hv' eq_refl).
    congruence.
  - apply tree_stash_disj in wf_s.
    elim (wf_s k); split.
    + apply In_path_in_tree_block in Hv'.
      apply in_map with (f := block_blockid) in Hv'; auto.
    + apply in_map with (f := block_blockid) in Hv; auto.
  - apply tree_stash_disj in wf_s.
    elim (wf_s k); split.
    + apply In_path_in_tree_block in Hv.
      apply in_map with (f := block_blockid) in Hv; auto.
    + apply in_map with (f := block_blockid) in Hv'; auto.
  - apply no_dup_tree in wf_s.
    unfold blk_in_path in *.
    apply NoDup.NoDup_map_inj in wf_s.
    unfold NoDup.inj_on_list in wf_s.
    unfold blk_in_p in *.
    apply In_path_in_tree_block in Hv.
    apply In_path_in_tree_block in Hv'.
    specialize (wf_s _ _ Hv Hv' eq_refl).
    congruence.
Qed.

Lemma kv_rel_functional : forall s,
  well_formed s ->
  forall k v v',
    kv_rel k v s ->
    kv_rel k v' s ->
    v = v'.
Proof.
  intros s wf_s k v v' pf1 pf2.
  destruct pf1 as [Hkvs|[Hks Hv]]; subst.
  - destruct pf2 as [Hkv's|[Hks Hv]]; subst.
    + apply blk_in_state_functional with (s := s) (k := k); auto.
    + elim Hks; exists v; auto.
  - destruct pf2 as [Hkv's|[Hks2 Hv]]; subst.
    + elim Hks; exists v'; auto.
    + reflexivity.
Qed.

Lemma impl_dist {X} (m : dist X)
  (P : Prop) (Q : X -> Prop) :
  (P -> plift Q m) ->
  plift (fun x => P -> Q x) m.
Proof.
  intro.
  unfold plift in *.
  simpl in *.
  destruct m as [l q]; simpl in *; clear q.
  rewrite Forall_forall in *.
  firstorder.
Qed.

Lemma plift_triv {X} (m : dist X) (P : X -> Prop) :
  (forall x, P x) -> plift P m.
Proof.
  destruct m as [l q].
  unfold plift; simpl; clear q.
  rewrite Forall_forall.
  intros.
  apply H.
Qed.

Lemma state_plift2_ret_l {S X} (x : X)
  (m : StateT S dist X) Pre Post P :
  (forall s, state_plift (Pre s) (Post s) (P x) m) ->
  state_plift2 Pre Post P (mreturn x) m.
Proof.
  intros Hm s s' HPre.
  apply plift_ret.
  unfold state_plift in Hm.
  specialize (Hm s s' HPre).
  eapply dist_has_weakening; [|exact Hm].
  unfold prod_rel.
  intros []; simpl; tauto.
Qed.

Lemma poram_lift2_ret_l {X} (x : X)
  (m : Poram X) Pre Post P :
  (forall s, poram_lift (Pre s) (Post s) (P x) m) ->
  poram_lift2 Pre Post P (mreturn x) m.
Proof.
  intros.
  apply state_plift2_ret_l.
  unfold poram_lift in H.
  intros s s' [wf_s [wf_s' eq_ss']].
  specialize (H s s' (conj wf_s' eq_ss')).
  eapply dist_has_weakening; [|exact H].
  intros [].
  unfold pand; tauto.
Qed.

Lemma split_post_and_pred {S X Y}
  (m : StateT S dist X)
  (m' : StateT S dist Y) Pre Post P :
  state_plift2 Pre triv2 P m m' ->
  state_plift2 Pre Post triv2 m m' ->
  state_plift2 Pre Post P m m'.
Proof.
  intros H1 H2 s s' eq_ss'.
  specialize (H1 s s' eq_ss').
  specialize (H2 s s' eq_ss').
  unfold plift2 in *; simpl in *.
  unfold dist_lift2 in *.
  unfold plift in *; simpl in *.
  destruct (m s) as [l q].
  destruct (m' s') as [l' q'].
  unfold dist_lift in *; simpl in *.
  clear q q'.
  rewrite Forall_forall in *.
  intros p Hp.
  specialize (H1 p Hp).
  specialize (H2 p Hp).
  rewrite Forall_forall in *.
  intros q Hq.
  specialize (H1 q Hq).
  specialize (H2 q Hq).
  destruct H1 as [H1 _].
  destruct H2 as [_ H2].
  split; auto.
Qed.

Lemma poram_split_post_and_pred {X}
  (m : Poram X) Pre Post P :
  poram_lift Pre triv P m ->
  poram_lift Pre Post triv m ->
  poram_lift Pre Post P m.
Proof.
  intros Hm1 Hm2 s pfs.
  specialize (Hm1 s pfs).
  specialize (Hm2 s pfs).
  pose proof (plift_conj _ _ _ Hm1 Hm2).
  eapply dist_has_weakening; [|exact H].
  unfold pand, triv.
  intros []; tauto.
Qed.

Lemma poram2_split_post_and_pred {X Y}
  (m : Poram X)
  (m' : Poram Y) Pre Post P :
  poram_lift2 Pre triv2 P m m' ->
  poram_lift2 Pre Post triv2 m m' ->
  poram_lift2 Pre Post P m m'.
Proof.
  intros.
  unfold poram_lift2 in *.
  apply split_post_and_pred.
  - intros s s' pfs.
    specialize (H s s' pfs).
    eapply dist_has_weakening; [|exact H].
    intros [x t] pf.
    eapply dist_has_weakening; [|exact pf].
    intros [y t'] [pf' _].
    split; auto.
    exact I.
  - intros s s' pfs.
    specialize (H0 s s' pfs).
    eapply dist_has_weakening; [|exact H0].
    intros [x t] pf.
    eapply dist_has_weakening; [|exact pf].
    intros [y t'] [_ pf'].
    split; auto.
    exact I.
Qed.

Fixpoint lookup_block (bs : list block) (id : block_id) : option nat :=
  match bs with
  | [] => None
  | b :: bs' =>
    if Nat.eqb (block_blockid b) id
      then Some (block_payload b)
      else lookup_block bs' id
  end.

Lemma lookup_block_Some bs id v :
  lookup_block bs id = Some v ->
  In {| block_blockid := id; block_payload := v |} bs.
Proof.
  induction bs; intro pf.
  - discriminate pf.
  - simpl in pf.
    destruct Nat.eqb eqn:Hk.
    + left.
      destruct a; simpl in *.
      inversion pf.
      rewrite PeanoNat.Nat.eqb_eq in Hk.
      rewrite Hk; auto.
    + right.
      apply IHbs; auto.
Qed.

Lemma lookup_block_None bs id :
  lookup_block bs id = None ->
  ~ exists v, In {| block_blockid := id; block_payload := v |} bs.
Proof.
  induction bs; intro pf.
  - intros [v []].
  - intros [v [Hv|Hv]].
    + rewrite Hv in pf.
      simpl in pf.
      rewrite PeanoNat.Nat.eqb_refl in pf; discriminate.
    + apply IHbs.
      * simpl in pf.
        destruct Nat.eqb; auto.
        discriminate.
      * exists v; auto.
Qed.

Definition key_in_stash_dec k s :
  { v : nat & blk_in_stash k v s } +
  { ~ exists v, blk_in_stash k v s }.
Proof.
  destruct (lookup_block (state_stash s) k) as [v|] eqn:Hk.
  - left; exists v.
    apply lookup_block_Some; auto.
  - right.
    apply lookup_block_None; auto.
Defined.

Definition key_in_path_dec k s :
  { v : nat & blk_in_path k v s } +
  { ~ exists v, blk_in_path k v s }.
Proof.
  destruct (lookup_block (concat (lookup_path_oram (state_oram s) (calc_path k s))) k) 
    as [v|] eqn:Hk.
  - left; exists v.
    apply lookup_block_Some; auto.
  - right.
    apply lookup_block_None; auto.
Defined.

Definition def_or_undef k s :
  { v : nat & blk_in_state k v s } +
  { undef k s }.
Proof.
  destruct (key_in_stash_dec k s) as [[v Hkv]|Hk1].
  - left; exists v; left; auto.
  - destruct (key_in_path_dec k s) as [[v Hkv]|Hk2].
    + left; exists v; right; auto.
    + right; intros [v Hkv].
      destruct Hkv.
      * apply Hk1; exists v; auto.
      * apply Hk2; exists v; auto.
Defined.

Definition get_state_val k s : option nat :=
  match def_or_undef k s with
  | inleft p => Some (projT1 p)
  | inright _ => None
  end.

Definition get_val k s : nat :=
  match get_state_val k s with
  | Some v => v
  | None => 0
  end.

Lemma blk_in_state_get_state_val : forall k v s,
  well_formed s ->
  blk_in_state k v s -> get_state_val k s = Some v.
Proof.
  intros k v s wf_s Hkv.
  unfold get_state_val.
  destruct (def_or_undef k s) as [[v' Hkv']|Hk].
  - simpl.
    rewrite blk_in_state_functional with (s := s) (k := k) (v := v) (v' := v'); auto.
  - elim Hk.
    exists v; auto.
Qed.

Lemma get_state_val_blk_in_state : forall k v s,
  well_formed s ->
  get_state_val k s = Some v -> blk_in_state k v s.
Proof.
  intros k v s wf_s gv_k.
  unfold get_state_val in gv_k.
  destruct (def_or_undef k s) as [[v' Hv']|]; [|discriminate].
  inversion gv_k; congruence.
Qed.

Lemma kv_rel_get_val : forall k v s,
  well_formed s ->
  kv_rel k v s -> get_val k s = v.
Proof.
  intros.
  unfold get_val.
  destruct H0.
  - apply blk_in_state_get_state_val in H0; auto.
    rewrite H0; auto.
  - destruct H0; subst.
    destruct get_state_val eqn:?; auto.
    elim H0; exists n.
    apply get_state_val_blk_in_state; auto.
Qed.

Lemma undef_get_state_val : forall k s,
  well_formed s ->
  undef k s -> get_state_val k s = None.
Proof.
  intros k s wf_s Hks.
  unfold get_state_val.
  destruct (def_or_undef k s) as [[v Hkv]|Hk]; auto.
  elim Hks.
  exists v; auto.
Qed.

Lemma get_state_val_undef : forall k s,
  well_formed s ->
  get_state_val k s = None -> 
  undef k s.
Proof.
  intros.
  unfold get_state_val in H0.
  destruct (def_or_undef k s) as [[v Hkv]|Hk]; auto.
  discriminate.
Qed.

Definition get_val_equiv s s' : Prop :=
  forall k, get_val k s = get_val k s'.

Lemma poram_lift_change_post {X Y}
  (Pre Post Post' : state -> state -> Prop)
  {P : X -> Y -> Prop} (m : Poram X) (m' : Poram Y) :
  (forall s s', well_formed s -> well_formed s' -> Post s s' -> Post' s s') ->
  poram_lift2 Pre Post P m m' ->
  poram_lift2 Pre Post' P m m'.
Proof.
  intros Hposts H1 s s' pfs.
  specialize (H1 s s' pfs).
  eapply dist_has_weakening; [|exact H1].
  intros [x t] H2.
  eapply dist_has_weakening; [|exact H2].
  intros [y t'] [H3 [wf_t [wf_t' Htt']]].
  split; auto.
Qed.

Lemma get_val_equiv_state_equiv : forall s s',
  well_formed s -> well_formed s' ->
  get_val_equiv s s' ->
  state_equiv s s'.
Proof.
  intros s s' wf_s wf_s' Hss' k v.
  split; intro pf.
  - apply kv_rel_get_val in pf; auto.
    rewrite Hss' in pf.
    unfold get_val in pf.
    destruct get_state_val eqn:?.
    + left. apply get_state_val_blk_in_state in Heqo; auto.
      congruence.
    + right; split; auto.
      intros [v' Hv'].
      erewrite blk_in_state_get_state_val in Heqo; eauto.
      discriminate.
  - apply kv_rel_get_val in pf; auto.
    rewrite <- Hss' in pf.
    unfold get_val in pf.
    destruct get_state_val eqn:?.
    + left. apply get_state_val_blk_in_state in Heqo; auto.
      congruence.
    + right; split; auto.
      intros [v' Hv'].
      erewrite blk_in_state_get_state_val in Heqo; eauto.
      discriminate.
Qed.

Lemma blk_in_state_imp_kv_rel s k v:
  blk_in_state k v s -> kv_rel k v s.
Proof.
  unfold kv_rel; tauto.
Qed.

Lemma undef_imp_kv_rel s k :
  undef k s -> kv_rel k 0 s.
Proof.
  unfold kv_rel; tauto.
Qed.

Lemma state_equiv_get_val_equiv : forall s s',
  well_formed s -> well_formed s' ->
  state_equiv s s' ->
  get_val_equiv s s'.
Proof.
  intros s s' wf_s wf_s' eq_ss' k.
  unfold get_val.
  destruct (get_state_val k s) eqn:Hks.
  - apply get_state_val_blk_in_state in Hks; auto.
    apply blk_in_state_imp_kv_rel in Hks.
    apply eq_ss' in Hks.
    destruct Hks.
    + apply blk_in_state_get_state_val in H; auto.
      rewrite H; auto.
    + destruct H.
      apply undef_get_state_val in H; auto.
      rewrite H; auto.
  - apply get_state_val_undef in Hks; auto.
    apply undef_imp_kv_rel in Hks.
    apply eq_ss' in Hks.
    destruct Hks.
    + apply blk_in_state_get_state_val in H; auto.
      rewrite H; auto.
    + destruct H.
      apply undef_get_state_val in H; auto.
      rewrite H; auto.
Qed.

Lemma read_wf k :
  poram_lift
    triv
    triv
    triv
    (read k).
Proof.
  eapply state_plift_bind.
  - intros s [wf_s _].
    eapply dist_has_weakening; [|apply read_access_just_wf]; auto.
    intros [p s'] [_ wf_s'].
    split.
    + exact I.
    + exact wf_s'.
  - intros [] _ s wf_s.
    apply plift_ret.
    unfold triv, pand; tauto.
Qed.

Lemma read_pres_state k v k' :
  poram_lift
    (blk_in_state k v)
    (blk_in_state k v)
    triv
    (read k').
Proof.
  apply state_plift_bind with
    (Mid := fun s => well_formed s /\ blk_in_state k v s)
    (P := triv).
  - apply read_access_state.
  - intros [] _ s wf_s.
    apply plift_ret.
    unfold triv, pand; tauto.
Qed.

Lemma read_undef k k' :
  poram_lift
    (undef k)
    (undef k)
    triv
    (read k').
Proof.
  apply state_plift_bind with
    (Mid := fun s => well_formed s /\ undef k s)
    (P := triv).
  - apply read_access_undef.
  - intros [] _ s wf_s.
    apply plift_ret.
    unfold triv, pand; tauto.
Qed.

Lemma read_undef_0 k :
  poram_lift
    (undef k)
    triv
    (eq 0)
    (read k).
Proof.
  apply state_plift_bind with (Mid := well_formed)
    (P := has_value 0).
  - unfold pand.
    apply read_access_undef_0.
  - intros [] H s wf_s.
    apply state_plift_ret; auto.
    unfold pand, triv; tauto.
Qed.

Lemma read_pres_kv k v k' :
  poram_lift
    (kv_rel k v)
    (kv_rel k v)
    triv
    (read k').
Proof.
  intros s [wf_s [Hkv|[Hk Hv]]].
  - pose proof (read_pres_state k v k' s (conj wf_s Hkv)).
    eapply dist_has_weakening; [|exact H].
    intros [v' s'].
    unfold pand, kv_rel; tauto.
  - subst.
    pose proof (read_undef k k' s (conj wf_s Hk)).
    eapply dist_has_weakening; [|exact H].
    intros [v' s'].
    unfold pand, kv_rel; tauto.
Qed.

Lemma read_state_val k v :
  poram_lift
    (blk_in_state k v)
    triv
    (eq v)
    (read k).
Proof.
  eapply state_plift_bind.
  - exact (read_access_wf k v).
  - intros [] pf s [wf_s kv_s].
    apply plift_ret; split.
    + exact pf.
    + split; auto.
      exact I.
Qed.

Lemma read_val k v :
  poram_lift
    (kv_rel k v)
    triv
    (eq v)
    (read k).
Proof.
  intros s [wf_s [Hkv|[Hk Hv]]].
  - pose proof (read_state_val k v s (conj wf_s Hkv)).
    eapply dist_has_weakening; [|exact H].
    intros [v' s']; tauto.
  - pose proof (read_undef_0 k s (conj wf_s Hk)).
    eapply dist_has_weakening; [|exact H].
    intros [v' s']; subst; tauto.
Qed.

Lemma read_val_kv k v :
  poram_lift
    (kv_rel k v)
    (kv_rel k v)
    (eq v)
    (read k).
Proof.
  apply poram_split_post_and_pred.
  - apply read_val.
  - apply read_pres_kv.
Qed.

Lemma write_wf k v :
  poram_lift
    triv
    triv
    triv
    (write k v).
Proof.
  eapply state_plift_bind.
  - intros s [wf_s _].
    eapply dist_has_weakening;
      [|apply write_access_just_wf]; auto.
    intros [p s'] [_ wf_s'].
    split.
    + exact I.
    + exact wf_s'.
  - intros [] _ s wf_s.
    apply plift_ret.
    unfold triv, pand; tauto.
Qed.

Lemma write_undef k k' v :
  k <> k' ->
  poram_lift
    (undef k')
    (undef k')
    triv
    (write k v).
Proof.
  intros.
  apply state_plift_bind with
    (Mid := fun s => well_formed s /\ undef k' s)
    (P := triv).
  - apply write_access_undef; auto.
  - intros [] _ s wf_s.
    apply plift_ret.
    unfold triv, pand; tauto.
Qed.

Lemma state_plift_pre {S X}
  (Pre Pre' Post : S -> Prop) (P : X -> Prop) (m : StateT S dist X) :
  (forall s, Pre' s -> Pre s) ->
  state_plift Pre Post P m ->
  state_plift Pre' Post P m.
Proof.
  intros HPre'Pre Hm s Hs.
  apply Hm.
  apply HPre'Pre; exact Hs.
Qed.

Lemma write_state_val_eq k v :
  poram_lift
    triv
    (blk_in_state k v)
    triv
    (write k v).
Proof.
  unfold poram_lift, write; eapply state_plift_bind.
  - apply state_plift_pre with (Pre := well_formed).
    + unfold pand; tauto.
    + apply write_access_wf.
  - intros [] _.
    apply state_plift_ret; exact I.
Qed.

Lemma write_val_eq k v :
  poram_lift
    triv
    (kv_rel k v)
    triv
    (write k v).
Proof.
  intros s pfs.
  pose proof (write_state_val_eq k v s pfs).
  eapply dist_has_weakening; [|exact H].
  intros [[] s'].
  unfold kv_rel, pand; tauto.
Qed.

Lemma write_state_val_neq k v k' v' :
  k <> k' ->
  poram_lift
    (blk_in_state k' v')
    (blk_in_state k' v')
    triv
    (write k v).
Proof.
  intro k_neq.
  apply state_plift_bind with
    (Mid := fun s => well_formed s /\ blk_in_state k' v' s)
    (P := triv).
  - apply write_access_neq; auto.
  - intros [] _ s pfs.
    apply plift_ret.
    unfold triv, pand; tauto.
Qed.

Lemma write_val_neq k v k' v' :
  k <> k' ->
  poram_lift
    (kv_rel k' v')
    (kv_rel k' v')
    triv
    (write k v).
Proof.
  intros k_neq s [wf_s [Hk'v'|[Hk' Hv']]].
  - pose proof (write_state_val_neq k v k' v' k_neq s (conj wf_s Hk'v')).
    eapply dist_has_weakening; [|exact H].
    intros [[] s'].
    unfold pand, kv_rel; tauto.
  - pose proof (write_undef k k' v k_neq s (conj wf_s Hk')).
    eapply dist_has_weakening; [|exact H].
    intros [[] s'].
    unfold pand, kv_rel; tauto.
Qed.

Definition get_val_equiv_single_exception k (s s' : state) : Prop :=
  forall k', k' <> k -> get_val k' s = get_val k' s'.

Definition get_val_equiv_double_exception k1 k2 (s s' : state) : Prop :=
  forall k', k' <> k1 -> k' <> k2 -> get_val k' s = get_val k' s'.

Definition near_stable {X} (m : Poram X) k : Prop :=
  forall s, well_formed s -> poram_lift (state_equiv s) (get_val_equiv_single_exception k s) triv m.

Lemma write_near_stable k v : near_stable (write k v) k.
Proof.
  intros s wf_s s' [wf_s' eq_ss'].
  apply dist_has_weakening with
    (P := pand (fun p => well_formed (snd p)) (fun p => get_val_equiv_single_exception k s (snd p))).
  - intros []; unfold pand, triv; tauto.
  - apply plift_conj.
    + eapply dist_has_weakening; [| apply write_wf].
      * intros []; unfold pand; tauto.
      * unfold pand, triv; tauto.
    + apply plift_forall; intro k'.
      apply impl_dist; intro k'_neq.
      assert (k <> k') as k_neq by auto.
      destruct (def_or_undef k' s) as [[v' Hk'v']|Hk'].
      * rewrite kv_rel_get_val with (v := v'); [|auto|left; auto].
        apply or_introl with (B := undef k' s /\ v' = 0) in Hk'v' .
        apply eq_ss' in Hk'v'.
        pose proof (write_val_neq k v k' v' k_neq s' (conj wf_s' Hk'v')).
        eapply dist_has_weakening; [|exact H].
        intros [[] t] pfs.
        unfold pand in *.
        rewrite kv_rel_get_val with (v := v'); tauto.
      * rewrite kv_rel_get_val with (v := 0); [|auto|right; auto].
        assert (kv_rel k' 0 s) by (right; tauto).
        apply eq_ss' in H.
        pose proof (write_val_neq k v k' 0 k_neq s' (conj wf_s' H)).
        eapply dist_has_weakening; [|exact H0].
        intros [[] t] pfs.
        unfold pand in *.
        rewrite kv_rel_get_val with (v := 0); tauto.
Qed.

Lemma state_equiv_sym : forall s s',
  state_equiv s s' -> state_equiv s' s.
Proof.
  intros s s' pf k v.
  specialize (pf k v); tauto.
Qed.

Lemma state_equiv_refl : forall s,
  state_equiv s s.
Proof.
  intros s k v; tauto.
Qed.

Lemma state_equiv_trans : forall s1 s2 s3,
  state_equiv s1 s2 ->
  state_equiv s2 s3 ->
  state_equiv s1 s3.
Proof.
  intros s1 s2 s3 pf1 pf2 k v.
  specialize (pf1 k v).
  specialize (pf2 k v); tauto.
Qed.

Definition kv_stable {X} (m : Poram X) : Prop :=
  forall s, poram_lift (state_equiv s) (state_equiv s) triv m.

Lemma mreturn_stable {X} (x : X) : kv_stable (mreturn x).
Proof.
  intros s s' [wf_s' eq_ss'].
  unfold triv, pand.
  apply plift_ret; split; auto.
Qed.

Lemma bind_stable {X Y} (m : Poram X) (f : X -> Poram Y) :
  kv_stable m ->
  (forall x, kv_stable (f x)) ->
  kv_stable (x <- m;; f x).
Proof.
  intros Hm Hf s s' pfs.
  eapply plift_bind.
  - apply Hm; exact pfs.
  - intros [] pfs'.
    apply Hf; tauto.
Qed.

Lemma read_stable k' :
  kv_stable (read k').
Proof.
  intros s s' [wf_s' eq_ss'].
  eapply dist_has_weakening with
    (P := fun p => well_formed (snd p) /\ state_equiv s (snd p)).
  - intros [] pf; split; auto.
    exact I.
  - apply plift_conj.
    + pose proof (read_wf k' s' (conj wf_s' I)).
      eapply dist_has_weakening; [|exact H].
      intros []; unfold pand; tauto.
    + apply plift_forall.
      intro k.
      apply plift_forall.
      intro v.
      apply plift_conj.
      * apply impl_dist.
        intro pf.
        apply eq_ss' in pf.
        pose proof (read_pres_kv k v k' s' (conj wf_s' pf)).
        eapply dist_has_weakening; [|exact H].
        intros []; unfold pand; tauto.
      * destruct (def_or_undef k s').
        -- destruct s0.
           pose (read_pres_kv k x k' s' (conj wf_s' (or_introl b))).
           eapply dist_has_weakening; [|exact p].
           intros [] [_ pf] pf'.
           simpl in pf'.
           apply eq_ss'.
           destruct pf.
           rewrite kv_rel_functional with (s := s0) (k := k) (v := v) (v' := x); auto.
           left; auto.
        -- pose (read_pres_kv k 0 k' s' (conj wf_s' (or_intror (conj u eq_refl)))).
           eapply dist_has_weakening; [|exact p].
           intros [] [_ pf] pf'.
           simpl in *.
           apply eq_ss'.
           destruct pf.
           rewrite kv_rel_functional with (s := s0) (k := k) (v := v) (v' := 0); auto.
           right; tauto.
Qed.

Definition dummy {X Y} (P : X -> Prop) (Q : Y -> Prop) : X -> Y -> Prop :=
  fun x y => P x /\ Q y.

Lemma poram_lift2_strengthen_pre {X Y}
  (Pre Pre' Post : state -> state -> Prop)
  (P : X -> Y -> Prop)
  (m : Poram X)
  (m' : Poram Y) :
  (forall s s', Pre' s s' -> Pre s s') ->
  poram_lift2 Pre Post P m m' ->
  poram_lift2 Pre' Post P m m'.
Proof.
  intros HPre'Pre H1 s s' Hss'.
  apply H1.
  split; [tauto|].
  split; [tauto|].
  apply HPre'Pre; tauto.
Qed.

Lemma plift2_conj {X X' Y Y'}
  (P : X -> Y -> Prop)
  (Q : X' -> Y' -> Prop)
  (dx : dist (X * X')) (dy : dist (Y * Y')) :
  plift2 (fun p p' => P (fst p) (fst p')) dx dy ->
  plift2 (fun p p' => Q (snd p) (snd p')) dx dy ->
  plift2 (prod_rel P Q) dx dy.
Proof.
  unfold plift2; simpl.
  unfold dist_lift2.
  intros.
  unfold plift in *; simpl in *.
  destruct dx as [l q]; simpl in *; clear q.
  rewrite Forall_forall in *.
  intros p Hp.
  specialize (H p Hp).
  specialize (H0 p Hp).
  unfold dist_lift in *; destruct dy as [l' q'].
  simpl in *; clear q'.
  rewrite Forall_forall in *.
  intros q Hq.
  split.
  - apply H; auto.
  - apply H0; auto.
Qed.

Lemma plift2_triv {X Y} (dx : dist X) (dy : dist Y)
  (P : X -> Y -> Prop) :
  (forall x y, P x y) -> plift2 P dx dy.
Proof.
  intro.
  apply plift_triv; intro.
  apply plift_triv; auto.
Qed.

Lemma poram_split_dummy {X Y}
  (Pre Pre' Post Post' : state -> Prop)
  (m : Poram X) (m' : Poram Y) :
  poram_lift Pre Post triv m ->
  poram_lift Pre' Post' triv m' ->
  poram_lift2 (dummy Pre Pre') (dummy Post Post') triv2 m m'.
Proof.
  intros Hm Hm' s s' [wf_s [wf_s' [Hs Hs']]].
  specialize (Hm s (conj wf_s Hs)).
  specialize (Hm' s' (conj wf_s' Hs')).
  apply plift2_conj.
  - unfold triv2. apply plift2_triv.
    tauto.
  - unfold plift2; simpl.
    unfold dist_lift2.
    eapply dist_has_weakening; [|exact Hm].
    intros [x t] [_ [wf_t Ht]].
    eapply dist_has_weakening; [|exact Hm'].
    intros [y t'] [_ [wf_t' Ht']].
    unfold dummy; tauto.
Qed.

Lemma plift2_and {X Y} {P Q : X -> Y -> Prop}
  (m : dist X) (m' : dist Y) :
  plift2 P m m' ->
  plift2 Q m m' ->
  plift2 (fun x y => P x y /\ Q x y) m m'.
Proof.
  unfold plift2; simpl.
  unfold dist_lift2; simpl.
  unfold dist_lift; simpl.
  destruct m as [l q]; simpl; clear q.
  destruct m' as [l' q']; simpl; clear q'.
  repeat rewrite Forall_forall.
  intros H1 H2 x Hx.
  specialize (H1 x Hx).
  specialize (H2 x Hx).
  rewrite Forall_forall in *.
  intros y Hy.
  specialize (H1 y Hy).
  specialize (H2 y Hy).
  split; auto.
Qed.

Lemma plift_to_plift2_l {X Y} (P : X -> Prop) (m : dist X) (m' : dist Y) :
  plift P m ->
  plift2 (fun x _ => P x) m m'.
Proof.
  unfold plift2; simpl.
  unfold dist_lift2; simpl.
  unfold dist_lift.
  destruct m as [l q]; simpl; clear q.
  destruct m' as [l' q']; simpl; clear q'.
  intro pf.
  rewrite Forall_forall in *.
  intros x Hx.
  specialize (pf x Hx).
  rewrite Forall_forall; auto.
Qed.

Lemma plift_to_plift2_r {X Y} (Q : Y -> Prop) (m : dist X) (m' : dist Y) :
  plift Q m' ->
  plift2 (fun _ y => Q y) m m'.
Proof.
  unfold plift2; simpl.
  unfold dist_lift2; simpl.
  unfold dist_lift.
  destruct m as [l q]; simpl; clear q.
  destruct m' as [l' q']; simpl; clear q'.
  intro pf.
  rewrite Forall_forall.
  intros; exact pf.
Qed.

Lemma plift2_split_eq {X Y Z} (f : X -> Z) (g : Y -> Z) (z : Z)
  (m : dist X) (m' : dist Y) :
  plift (fun x => f x = z) m ->
  plift (fun y => g y = z) m' ->
  plift2 (fun x y => f x = g y) m m'.
Proof.
  intros Hm Hm'.
  eapply dist_has_weakening; [|exact Hm].
  intros x Hx.
  eapply dist_has_weakening; [|exact Hm'].
  intros y Hy.
  congruence.
Qed.

Lemma poram_lift2_kv_stable {X Y} (m : Poram X) (m' : Poram Y) :
  kv_stable m -> kv_stable m' ->
  poram_lift2 state_equiv state_equiv triv2 m m'.
Proof.
  intros Hm Hm' s s' [wf_s [wf_s' eq_ss']].
  specialize (Hm s s (conj wf_s (state_equiv_refl s))).
  eapply dist_has_weakening; [|exact Hm].
  intros [x t] [_ [wf_t eq_st]].
  specialize (Hm' s s' (conj wf_s' eq_ss')).
  eapply dist_has_weakening; [|exact Hm'].
  intros [y t'] [_ [wf_t' eq_st']].
  split; [exact I|].
  split; auto.
  split; auto.
  apply state_equiv_trans with (s2 := s); auto.
  apply state_equiv_sym; auto.
Qed.

Lemma get_state_val_Some_kv_rel k v s :
  well_formed s ->
  get_state_val k s = Some v ->
  kv_rel k v s.
Proof.
  intro; left.
  apply get_state_val_blk_in_state; auto.
Qed.

Lemma get_state_val_None_kv_rel k s :
  well_formed s ->
  get_state_val k s = None ->
  kv_rel k 0 s.
Proof.
  intro; right; split; auto.
  intros [v Hv].
  erewrite blk_in_state_get_state_val in H0; eauto.
  discriminate.
Qed.
  
Theorem read_write : forall k,
    poram_equiv
      eq
      (mreturn tt)
      (v <- read k ;; write k v) .
Proof.
  intros.
  apply equiv_implies_poram_equiv; auto.
  unfold equiv.
  apply poram2_split_post_and_pred; auto.
  - intros s s'.
    intros [wf_s [wf_s' eq_ss]].
    apply plift_ret.
    eapply plift_bind.
    + apply read_wf.
      unfold pand, triv; tauto.
    + intros [v t] [_ wf_t].
      pose proof (write_wf k v t wf_t).
      eapply dist_has_weakening; [|exact H].
      intros [[] t'] [_ [wf_t' _]].
      unfold prod_rel, triv2; simpl; tauto.
  - intros s s' [wf_s [wf_s' eq_ss']].
    apply plift_ret.
    destruct (get_state_val k s) as [v|] eqn:Hks.
    + apply get_state_val_Some_kv_rel in Hks; auto.
      apply plift_bind with
        (P := fun p => fst p = v /\ well_formed (snd p) /\ state_equiv s (snd p)); auto.
      * pose proof (read_stable k s s' (conj wf_s' eq_ss')).
        apply eq_ss' in Hks.
        pose proof (read_val k v s' (conj wf_s' Hks)).
        pose proof (plift_conj _ _ _ H H0).
        eapply dist_has_weakening; [|exact H1].
        intros [v' t] [[_ [wf_t Hst]] [? _]]; subst.
        simpl; tauto.
      * intros [v' t] [? [wf_t Hst]]; subst.
        simpl in Hks, Hst, wf_t.
        pose proof (write_near_stable k v' s wf_s t (conj wf_t Hst)).
        pose proof (write_val_eq k v' t (conj wf_t I)).
        pose proof (plift_conj _ _ _ H H0).
        eapply dist_has_weakening; [|exact H1].
        intros [[] t'] [[_ [wf_t' Hst']] [_ [_ Hkv't']]].
        split; [exact I|].
        simpl; do 2 (split; try tauto).
        apply get_val_equiv_state_equiv; auto.
        intro k'.
        destruct (nat_eq_dec k' k).
        -- subst.
           repeat rewrite kv_rel_get_val with (v := v'); auto.
        -- rewrite <- Hst'; auto.
    + apply get_state_val_None_kv_rel in Hks; auto.
      apply plift_bind with
        (P := fun p => fst p = 0 /\ well_formed (snd p) /\ state_equiv s (snd p)); auto.
      * pose proof (read_stable k s s' (conj wf_s' eq_ss')).
        apply eq_ss' in Hks.
        pose proof (read_val k 0 s' (conj wf_s' Hks)).
        pose proof (plift_conj _ _ _ H H0).
        eapply dist_has_weakening; [|exact H1].
        intros [v' t] [[_ [wf_t Hst]] [? _]]; subst.
        simpl; tauto.
      * intros [v' t] [? [wf_t Hst]].
        simpl in H; subst.
        simpl in Hks, Hst, wf_t.
        pose proof (write_near_stable k 0 s wf_s t (conj wf_t Hst)).
        pose proof (write_val_eq k 0 t (conj wf_t I)).
        pose proof (plift_conj _ _ _ H H0).
        eapply dist_has_weakening; [|exact H1].
        intros [[] t'] [[_ [wf_t' Hst']] [_ [_ Hkv't']]].
        split; [exact I|].
        simpl; do 2 (split; try tauto).
        apply get_val_equiv_state_equiv; auto.
        intro k'.
        destruct (nat_eq_dec k' k).
        -- subst.
           repeat rewrite kv_rel_get_val with (v := 0); auto.
        -- rewrite <- Hst'; auto.
Qed.

Theorem write_read : forall k v,
  poram_equiv
  eq
  (write k v;; mreturn v)
  (write k v;; read k).
Proof.
  intros.
  intros s s'.
  intros.
  apply equiv_implies_poram_equiv; auto.
  unfold equiv.
  apply poram2_split_post_and_pred.
  - eapply poram_lift2_bind with
      (Mid := dummy (kv_rel k v) (kv_rel k v))
      (P := triv2).
    + apply poram_lift2_strengthen_pre with
        (Pre := dummy triv triv).
      * intros; unfold dummy, triv; tauto.
      * apply poram_split_dummy.
        -- apply write_val_eq.
        -- apply write_val_eq.
    + intros _ _ _.
      apply poram_lift2_ret_l.
      intros t t' [wf_t' [Ht Ht']].
      pose proof (read_val k v t' (conj wf_t' Ht')).
      eapply dist_has_weakening; [|exact H2].
      intros []; unfold pand, triv; tauto.
  - apply poram_lift2_bind with
      (Mid := state_equiv) (P := triv2).
    + clear s s' H H0 H1.
      apply poram_lift_change_post with (Post := get_val_equiv).
      * apply get_val_equiv_state_equiv.
      * apply poram_lift2_forall; [exact 0|].
        intros k' s s' [wf_s [wf_s' eq_ss']].
        apply plift2_and; [|apply plift2_and]; [ | | apply plift2_and] .
        -- unfold triv2; apply plift2_triv; auto.
        -- apply plift_to_plift2_l.
           pose proof (write_wf k v s (conj wf_s I)) as pf.
           eapply dist_has_weakening; [|exact pf].
           intros []; unfold pand; tauto.
        -- apply plift_to_plift2_r.
           pose proof (write_wf k v s' (conj wf_s' I)) as pf.
           eapply dist_has_weakening; [|exact pf].
           intros []; unfold pand; tauto.
        -- destruct (nat_eq_dec k k').
           ++ subst.
              pose proof (write_val_eq k' v s (conj wf_s I)) as pf.
              eapply dist_has_weakening; [|exact pf].
              intros [x t] [_ [wf_t Ht]].
              pose proof (write_val_eq k' v s' (conj wf_s' I)) as pf'.
              eapply dist_has_weakening; [|exact pf'].
              intros [y t'] [_ [wf_t' Ht']].
              simpl. repeat rewrite kv_rel_get_val with (v := v); auto.
           ++ destruct (def_or_undef k' s) as [[v' Hk'v']|Hk'].
              ** apply plift2_split_eq with (z := v').
                 --- apply blk_in_state_imp_kv_rel in Hk'v'.
                     pose proof (write_val_neq k v k' v' n s (conj wf_s Hk'v')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     apply kv_rel_get_val; auto.
                 --- apply blk_in_state_imp_kv_rel in Hk'v'.
                     apply eq_ss' in Hk'v'.
                     pose proof (write_val_neq k v k' v' n s' (conj wf_s' Hk'v')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     apply kv_rel_get_val; auto.
              ** apply plift2_split_eq with (z := 0).
                 --- pose proof (write_undef k k' v n s (conj wf_s Hk')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     unfold get_val.
                     rewrite undef_get_state_val; auto.
                 --- apply undef_imp_kv_rel in Hk'.
                     apply eq_ss' in Hk'.
                     pose proof (write_val_neq k v k' 0 n s' (conj wf_s' Hk')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     rewrite kv_rel_get_val with (v := 0); auto.
    + intros _ _ _.
      apply poram_lift2_ret_l.
      intro s''.
      exact (read_stable k s'').
Qed.

Theorem read_read : forall k,
  poram_equiv
  eq
  (v <- read k;; mreturn v)
  (read k;; read k).
Proof.
  intros k s s' eq_ss' wf_s wf_s'.
  apply equiv_implies_poram_equiv; auto.
  unfold equiv.
  apply poram2_split_post_and_pred.
  - apply poram_lift2_val_to_poram_lift2.
    apply poram_lift2_val_bind with
      (Mid := fun s s' v v' =>
        (kv_rel k v s /\ kv_rel k v s')).
    + clear eq_ss' wf_s wf_s' s s'.
      intros s s' [wf_s [wf_s' eq_ss']].
      destruct (def_or_undef k s).
      * destruct s0 as [v Hv].
        apply blk_in_state_imp_kv_rel in Hv.
        pose proof (read_val_kv k v s (conj wf_s Hv)).
        eapply dist_has_weakening; [|exact H].
        intros [] pfs.
        apply eq_ss' in Hv.
        pose proof (read_val_kv k v s' (conj wf_s' Hv)).
        eapply dist_has_weakening; [|exact H0].
        intros [] pfs'.
        unfold pand in *.
        split; try tauto.
        split; try tauto.
        destruct pfs.
        rewrite <- H1. tauto.
      * apply undef_imp_kv_rel in u.
        pose proof (read_val_kv k 0 s (conj wf_s u)).
        eapply dist_has_weakening; [|exact H].
        intros [] pfs.
        apply eq_ss' in u.
        pose proof (read_val_kv k 0 s' (conj wf_s' u)).
        eapply dist_has_weakening; [|exact H0].
        intros [] pfs'.
        unfold pand in *.
        destruct pfs; subst.
        destruct pfs'; subst.
        split; try tauto.
    + intros v v'.
      clear wf_s eq_ss' wf_s' s s'.
      intros s s' [wf_s [wf_s' Hk]].
      destruct Hk.
      apply plift_ret.
      pose proof (read_val_kv k v s' (conj wf_s' H0)).
      eapply dist_has_weakening; [|exact H1].
      intros []. unfold triv, triv2, pand in *; tauto.
  - apply poram_lift2_kv_stable.
    + apply bind_stable.
      * apply read_stable.
      * apply mreturn_stable.
    + apply bind_stable.
      * apply read_stable.
      * intro; apply read_stable.
Qed.

Theorem read_commute : forall k1 k2,
  poram_equiv
  eq
  (v1 <- read k1;; v2 <- read k2;; mreturn (v1, v2))
  (v2 <- read k2;; v1 <- read k1;; mreturn (v1, v2)).
Proof.
  intros k1 k2 s s' eq_ss' wf_s wf_s'.
  apply equiv_implies_poram_equiv; auto.
  clear eq_ss' wf_s wf_s' s s'.
  unfold equiv.
  apply poram2_split_post_and_pred.
  - apply poram_lift2_val_to_poram_lift2.
    apply poram_lift2_val_bind with
      (Mid := fun s s' v v' =>
        (kv_rel k1 v s /\ kv_rel k1 v s') /\
        (kv_rel k2 v' s /\ kv_rel k2 v' s')).
    + intros s s' [wf_s [wf_s' eq_ss']].
      destruct (def_or_undef k1 s) as [[v1 Hk1v1]|Hk1]. 
      * apply blk_in_state_imp_kv_rel in Hk1v1.
        destruct (def_or_undef k2 s) as [[v2 Hk2v2]|Hk2].
        -- apply blk_in_state_imp_kv_rel in Hk2v2.
           pose proof (read_val_kv k1 v1 s (conj wf_s Hk1v1)).
           pose proof (read_pres_kv k2 v2 k1 s (conj wf_s Hk2v2)).
           pose proof (plift_conj _ _ _ H H0).
           eapply dist_has_weakening; [|exact H1].
           intros [] [[]]; subst.
           apply eq_ss' in Hk1v1, Hk2v2.
           pose proof (read_val_kv k2 v2 s' (conj wf_s' Hk2v2)).
           pose proof (read_pres_kv k1 n k2 s' (conj wf_s' Hk1v1)).
           pose proof (plift_conj _ _ _ H2 H5).
           eapply dist_has_weakening; [|exact H6].
           intros [] [[]]; subst.
           unfold pand in *; tauto.
        -- apply undef_imp_kv_rel in Hk2.
           pose proof (read_val_kv k1 v1 s (conj wf_s Hk1v1)).
           pose proof (read_pres_kv k2 0 k1 s (conj wf_s Hk2)).
           pose proof (plift_conj _ _ _ H H0).
           eapply dist_has_weakening; [|exact H1].
           intros [] [[]]; subst.
           apply eq_ss' in Hk1v1.
           apply eq_ss' in Hk2.
           pose proof (read_val_kv k2 0 s' (conj wf_s' Hk2)).
           pose proof (read_pres_kv k1 n k2 s' (conj wf_s' Hk1v1)).
           pose proof (plift_conj _ _ _ H2 H5).
           eapply dist_has_weakening; [|exact H6].
           intros [] [[]]; subst.
           unfold pand in *; tauto.
      * apply undef_imp_kv_rel in Hk1.
        destruct (def_or_undef k2 s) as [[v2 Hk2v2]|Hk2].
        -- apply blk_in_state_imp_kv_rel in Hk2v2.
           pose proof (read_val_kv k1 0 s (conj wf_s Hk1)).
           pose proof (read_pres_kv k2 v2 k1 s (conj wf_s Hk2v2)).
           pose proof (plift_conj _ _ _ H H0).
           eapply dist_has_weakening; [|exact H1].
           intros [] [[]]; subst.
           apply eq_ss' in Hk2v2.
           apply eq_ss' in Hk1.
           pose proof (read_val_kv k2 v2 s' (conj wf_s' Hk2v2)).
           pose proof (read_pres_kv k1 0 k2 s' (conj wf_s' Hk1)).
           pose proof (plift_conj _ _ _ H2 H5).
           eapply dist_has_weakening; [|exact H6].
           intros [] [[]]; subst.
           unfold pand in *; tauto.
        -- apply undef_imp_kv_rel in Hk2.
           pose proof (read_val_kv k1 0 s (conj wf_s Hk1)).
           pose proof (read_pres_kv k2 0 k1 s (conj wf_s Hk2)).
           pose proof (plift_conj _ _ _ H H0).
           eapply dist_has_weakening; [|exact H1].
           intros [] [[]]; subst.
           apply eq_ss' in Hk1, Hk2.
           pose proof (read_val_kv k2 0 s' (conj wf_s' Hk2)).
           pose proof (read_pres_kv k1 0 k2 s' (conj wf_s' Hk1)).
           pose proof (plift_conj _ _ _ H2 H5).
           eapply dist_has_weakening; [|exact H6].
           intros [] [[]]; subst.
           unfold pand in *; tauto.
    + intros v1 v2.
      apply poram_lift2_val_bind with
        (Mid := fun _ _ w2 w1 => w1 = v1 /\ w2 = v2).
      * intros s s' [wf_s [wf_s' [Hk1 Hk2]]].
        destruct Hk1 as [Hk1v1 Hk1v1'].
        destruct Hk2 as [Hk2v2 Hk2v2'].
        pose proof (read_val_kv k2 v2 s (conj wf_s Hk2v2)).
        eapply dist_has_weakening; [|exact H].
        intros [w2 t] []; subst.
        pose proof (read_val_kv k1 v1 s' (conj wf_s' Hk1v1')).
        eapply dist_has_weakening; [|exact H0].
        intros [w1 t'] []; subst.
        unfold pand in *; tauto.
      * intros w1 w2 s s' [wf_s [wf_s' [? ?]]]; subst.
        do 2 apply plift_ret.
        unfold triv2; tauto.
  - apply poram_lift2_kv_stable.
    + apply bind_stable.
      * apply read_stable.
      * intro; apply bind_stable.
        -- apply read_stable.
        -- intro; apply mreturn_stable.
    + apply bind_stable.
      * apply read_stable.
      * intro; apply bind_stable.
        -- apply read_stable.
        -- intro; apply mreturn_stable.
Qed.

Theorem read_write_commute : forall k1 k2 v2,
  k1 <> k2 ->
  poram_equiv
  eq
  (v1 <- read k1;; write k2 v2;; mreturn v1)
  (write k2 v2;; v1 <- read k1;; mreturn v1).
Proof.
  intros k1 k2 v2 k1_neq s s' eq_ss' wf_s wf_s'.
  assert (k2 <> k1) as k2_neq by auto.
  apply equiv_implies_poram_equiv; auto.
  unfold equiv.
  clear eq_ss' wf_s wf_s' s s'.
  apply poram2_split_post_and_pred.
  - apply poram_lift2_val_to_poram_lift2.
    apply poram_lift2_val_bind with
      (Mid := fun s s' v u =>
        (kv_rel k1 v s /\ kv_rel k1 v s')).
    + intros s s' [wf_s [wf_s' eq_ss']].
      destruct (def_or_undef k1 s) as [[v1 Hk1v1]|Hk1].
      * apply blk_in_state_imp_kv_rel in Hk1v1.
        pose proof (read_val_kv k1 v1 s (conj wf_s Hk1v1)).
        eapply dist_has_weakening; [|exact H].
        intros [? t] [? [wf_t Ht]]; subst.
        apply eq_ss' in Hk1v1.
        pose proof (write_val_neq k2 v2 k1 n k2_neq s' (conj wf_s' Hk1v1)).
        eapply dist_has_weakening; [|exact H0].
        intros [[] t'] [_ [wf_t' Ht']]; tauto.
      * apply undef_imp_kv_rel in Hk1.
        pose proof (read_val_kv k1 0 s (conj wf_s Hk1)).
        eapply dist_has_weakening; [|exact H].
        intros [? t] [? [wf_t Ht]]; subst.
        apply eq_ss' in Hk1.
        pose proof (write_val_neq k2 v2 k1 0 k2_neq s' (conj wf_s' Hk1)).
        eapply dist_has_weakening; [|exact H0].
        intros [_ t'] [_ [wf_t' Ht']].
        tauto.
    + intros v1 _.
      apply poram_lift2_val_bind with
        (Mid := fun s s' u v =>
                  (kv_rel k1 v1 s /\ kv_rel k1 v1 s' /\ v1 = v)).
      * intros s s' [wf_s [wf_s' pf]].
        destruct pf as [Hk1v1 Hk1v1'].
        pose proof (write_val_neq k2 v2 k1 v1 k2_neq s (conj wf_s Hk1v1)).
           eapply dist_has_weakening; [|exact H].
           intros [[] t] [_ [wf_t Ht]].
           pose proof (read_val_kv k1 v1 s' (conj wf_s' Hk1v1')).
           eapply dist_has_weakening; [|exact H0].
           intros [? t'] []; subst. unfold pand in *. tauto.
      * intros _ v1'.
        intros s s' [wf_s [wf_s' pf]].
        apply plift_ret.
        apply plift_ret.
        unfold triv2.
        do 3 (split; try tauto).
  - apply poram_lift2_bind with
      (Mid := fun s s' =>
        kv_rel k2 v2 s' /\
        get_val_equiv_single_exception k2 s s'
      )
      (P := triv2).
    + intros s s' [wf_s [wf_s' eq_ss']].
      pose proof (read_stable k1 s s (conj wf_s (state_equiv_refl s))).
      eapply dist_has_weakening; [|exact H].
      intros [v1 t] [_ [wf_t Hst]].
      pose proof (write_near_stable k2 v2 s' wf_s' s' (conj wf_s' (state_equiv_refl s'))).
      pose proof (write_val_eq k2 v2 s' (conj wf_s' I)).
      pose proof (plift_conj _ _ _ H0 H1).
      eapply dist_has_weakening; [|exact H2].
      intros [? t'] [[_ [wf_t' Hs't']] [_ [_ Hk2v2t']]].
      unfold triv2.
      do 4 (split; try tauto).
      intros k k_neq; simpl.
      rewrite <- Hs't'; auto.
      apply state_equiv_sym in Hst.
      rewrite state_equiv_get_val_equiv with (s' := s); auto.
      apply state_equiv_get_val_equiv; auto.
    + intros v _ _.
      apply poram_lift2_bind with
        (Mid := state_equiv)
        (P := triv2).
      * intros s s' [wf_s [wf_s' [Hk2v2 Hss']]].
        pose proof (write_near_stable k2 v2 s wf_s s (conj wf_s (state_equiv_refl s))).
        pose proof (write_val_eq k2 v2 s (conj wf_s I)).
        pose proof (plift_conj _ _ _ H H0).
        eapply dist_has_weakening; [|exact H1].
        intros [? t] [[_ [wf_t Hst]] [_ [_ Ht]]].
        pose proof (read_stable k1 s' s' (conj wf_s' (state_equiv_refl s'))).
        eapply dist_has_weakening; [|exact H2].
        intros [? t'] [_ [wf_t' Hs't']].
        unfold triv2; simpl.
        do 3 (split; try tauto).
        simpl.
        apply get_val_equiv_state_equiv; auto.
        intro k.
        destruct (nat_eq_dec k k2).
        -- subst.
           rewrite kv_rel_get_val with (v := v2); auto.
           apply state_equiv_sym in Hs't'.
           rewrite state_equiv_get_val_equiv with (s' := s'); auto.
           rewrite kv_rel_get_val with (v := v2); auto.
        -- rewrite <- Hst; auto.
           rewrite Hss'; auto.
           rewrite state_equiv_get_val_equiv with (s' := t'); auto.
      * intros _ v' _ s s' pfs.
        do 2 (apply plift_ret).
        split; [exact I|exact pfs].
Qed.

Theorem write_commute : forall k1 k2 v1 v2,
  k1 <> k2 ->
  poram_equiv
  eq
  (write k1 v1;; write k2 v2)
  (write k2 v2;; write k1 v1).
Proof.
  intros k1 k2 v1 v2 k_neq s s' eq_ss' wf_s wf_s'.
  assert (k2 <> k1) as k_neq' by auto.
  apply equiv_implies_poram_equiv; auto.
  unfold equiv.
  clear eq_ss' wf_s wf_s' s s'.
  apply poram2_split_post_and_pred.
  - apply poram_lift2_bind with (Mid := triv2) (P := triv2).
    + intros s s' [wf_s [wf_s' eq_ss']].
      pose proof (write_wf k1 v1 s (conj wf_s I)).
      eapply dist_has_weakening; [|exact H].
      intros [[] t] [_ [wf_t _]].
      pose proof (write_wf k2 v2 s' (conj wf_s' I)).
      eapply dist_has_weakening; [|exact H0].
      intros [[] t'] [_ [wf_t' _]].
      unfold prod_rel, triv2; tauto.
    + intros _ _ _ s s' [wf_s [wf_s' _]].
      pose proof (write_wf k2 v2 s (conj wf_s I)).
      eapply dist_has_weakening; [|exact H].
      intros [[] t] [_ [wf_t _]].
      pose proof (write_wf k1 v1 s' (conj wf_s' I)).
      eapply dist_has_weakening; [|exact H0].
      intros [[] t'] [_ [wf_t' _]].
      unfold prod_rel, triv2.
      simpl; tauto.
  - apply poram_lift2_bind with
      (Mid := fun s s' =>
        kv_rel k1 v1 s /\
        kv_rel k2 v2 s' /\
        get_val_equiv_double_exception k1 k2 s s'
      )
      (P := triv2).
    + intros s s' [wf_s [wf_s' eq_ss']].
      pose proof (write_val_eq k1 v1 s (conj wf_s I)).
      pose proof (write_near_stable k1 v1 s wf_s s (conj wf_s (state_equiv_refl s))).
      pose proof (plift_conj _ _ _ H H0).
      eapply dist_has_weakening; [|exact H1].
      intros [[] t] [[_ [wf_t Hk1v1]] [_ [_ Hst]]].
      pose proof (write_val_eq k2 v2 s' (conj wf_s' I)).
      pose proof (write_near_stable k2 v2 s wf_s s' (conj wf_s' eq_ss')).
      pose proof (plift_conj _ _ _ H2 H3).
      eapply dist_has_weakening; [|exact H4].
      intros [[] t'] [[_ [wf_t' Hk2v2]] [_ [_ Hs't']]].
      unfold prod_rel, triv2; simpl.
      do 5 (split; try tauto).
      intros k neq1 neq2.
      rewrite <- Hst; auto.
    + intros _ _ _ s s' [wf_s [wf_s' [Hk1v1 [Hk2v2 Hss']]]].
      pose proof (write_near_stable k2 v2 s wf_s s (conj wf_s (state_equiv_refl s))).
      pose proof (write_val_eq k2 v2 s (conj wf_s I)).
      pose proof (write_val_neq k2 v2 k1 v1 k_neq' s (conj wf_s Hk1v1)).
      pose proof (plift_conj _ _ _ H (plift_conj _ _ _ H0 H1)).
      eapply dist_has_weakening; [|exact H2].
      intros [[] t] [[_ [wf_t Hst]] [[_ [_ Hk1v1t]] [_ [_ Hk2v2t]]]].
      pose proof (write_near_stable k1 v1 s' wf_s' s' (conj wf_s' (state_equiv_refl s'))).
      pose proof (write_val_eq k1 v1 s' (conj wf_s' I)).
      pose proof (write_val_neq k1 v1 k2 v2 k_neq s' (conj wf_s' Hk2v2)).
      pose proof (plift_conj _ _ _ H3 (plift_conj _ _ _ H4 H5)).
      eapply dist_has_weakening; [|exact H6].
      intros [[] t'] [[_ [wf_t' Hs't']] [[_ [_ Hk1v1t']] [_ [_ Hk2v2t']]]].
      split; [exact I|].
      simpl; do 2 (split; auto).
      apply get_val_equiv_state_equiv; auto.
      intro k.
      destruct (nat_eq_dec k k1); subst.
      * repeat rewrite kv_rel_get_val with (v := v1); auto.
      * destruct (nat_eq_dec k k2); subst.
        -- repeat rewrite kv_rel_get_val with (v := v2); auto.
        -- rewrite <- Hst; auto.
           rewrite <- Hs't'; auto.
Qed.

Theorem write_absorb : forall k v v',
  poram_equiv
  eq
  (write k v;; write k v')
  (write k v').
Proof.
  intros k v v' s s' eq_ss' wf_s wf_s'.
  apply equiv_implies_poram_equiv; auto.
  unfold equiv.
  clear eq_ss' wf_s wf_s' s s'.
  apply poram2_split_post_and_pred.
  - intros s s' [wf_s [wf_s' eq_ss']].
    apply plift_bind with (P := fun p => well_formed (snd p)).
    + pose proof (write_state_val_eq k v s (conj wf_s I)).
      eapply dist_has_weakening; [|exact H].
      intros [[] t].
      unfold triv, pand; tauto.
    + intros [[] t] wf_t.
      simpl in wf_t.
      pose proof (write_state_val_eq k v' t (conj wf_t I)).
      eapply dist_has_weakening; [|exact H].
      intros [[] t'].
      intros [_ [wf_t' Hkv't']].
      pose proof (write_state_val_eq k v' s' (conj wf_s' I)).
      eapply dist_has_weakening; [|exact H0].
      intros [[] t''].
      unfold prod_rel, pand, triv2.
      tauto.
  - intros s s' [wf_s [wf_s' eq_ss']].
    apply plift_bind with (P := fun p => well_formed (snd p) /\
      get_val_equiv_single_exception k s (snd p)).
    + pose proof (write_near_stable k v s wf_s s (conj wf_s (state_equiv_refl s))).
      eapply dist_has_weakening; [|exact H].
      intros [[] t].
      unfold triv, pand; tauto.
    + intros [[] t] [wf_t Hst].
      simpl in wf_t, Hst.
      pose proof (write_near_stable k v' t wf_t t (conj wf_t (state_equiv_refl t))).
      pose proof (write_val_eq k v' t (conj wf_t I)).
      pose proof (plift_conj _ _ _ H H0).
      eapply dist_has_weakening; [|exact H1].
      intros [[] t'] [[_ [wf_t' Htt']] [_ [_ Hkv't']]].
      pose proof (write_near_stable k v' s wf_s s' (conj wf_s' eq_ss')).
      pose proof (write_val_eq k v' s' (conj wf_s' I)).
      pose proof (plift_conj _ _ _ H2 H3).
      eapply dist_has_weakening; [|exact H4].
      intros [[] t''] [[_ [wf_t'' Hst'']] [_ [_ Hkv't'']]].
      unfold prod_rel, triv2; simpl.
      do 3 (split; try tauto).
      apply get_val_equiv_state_equiv; auto.
      intro k''.
      destruct (nat_eq_dec k'' k).
      * subst.
        repeat rewrite kv_rel_get_val with (v := v'); auto; left; auto.
      * rewrite <- Hst''; auto.
        rewrite <- Htt'; auto.
        rewrite <- Hst; auto.
Qed.

End EquivProofs.

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
Module PathORAM (C : ConfigParams) <: RAM (Dist_State).

  Global Instance PoramConfig : Config := {LOP := C.LOP}.

  Definition K := block_id.
  Definition V := nat.
  Definition S : Type := state.

  Module M := Dist_State.
  Definition bind {X Y} := @M.bind S X Y.
  Definition ret {X} := @M.ret S X.
  Definition get := @M.get S.
  Definition put := @M.put S.

  Definition well_formed s := 
    well_formed s.

  Definition read : K -> M.State S V := read.

  Definition write : K -> V -> M.State S unit := write.

  Definition equiv : forall {X}, M.State S X -> M.State S X -> Prop :=
    fun X => poram_equiv eq.

  Theorem read_write : forall (k : K),
    equiv
      (ret tt)
      (bind (read k) (fun v => write k v)).
  Proof.
    exact read_write.
  Qed.

  Theorem write_read : forall (k : K) (v : V),
    equiv
      (bind (write k v) (fun _ => ret v))
      (bind (write k v) (fun _ => read k)).
  Proof.
    exact write_read.
  Qed.

  Theorem read_read : forall (k : K),
    equiv
      (bind (read k) (fun v => ret v))
      (bind (read k) (fun _ => read k)).
  Proof.
    exact read_read.
  Qed.

  Theorem read_commute : forall (k1 k2 : K),
    equiv
      (bind (read k1) (fun v1 =>
        bind (read k2) (fun v2 =>
        ret (v1, v2))))
      (bind (read k2) (fun v2 =>
        bind (read k1) (fun v1 =>
        ret (v1, v2)))).
  Proof.
    exact read_commute.
  Qed.

  Theorem read_write_commute : forall (k1 k2 : K) (v2 : V),
    k1 <> k2 ->
    equiv
      (bind (read k1) (fun v1 =>
        bind (write k2 v2) (fun _ =>
        ret v1)))
      (bind (write k2 v2) (fun _ =>
        bind (read k1) (fun v1 =>
        ret v1))).
  Proof.
    exact read_write_commute.
  Qed.

  Theorem write_commute : forall (k1 k2 : K) (v1 v2 : V),
    k1 <> k2 ->
    equiv
      (bind (write k1 v1) (fun _ =>
        write k2 v2))
      (bind (write k2 v2) (fun _ =>
        write k1 v1)).
  Proof.
    exact write_commute.
  Qed.

  Theorem write_absorb : forall (k : K) (v v' : V),
    equiv
      (bind (write k v) (fun _ => write k v'))
      (write k v').
  Proof.
    exact write_absorb.
  Qed.

End PathORAM.
