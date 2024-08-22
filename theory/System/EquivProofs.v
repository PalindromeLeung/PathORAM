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
  map snd (read_access id).

Definition write id v : Poram nat :=
  map snd (write_access id v).

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

Definition state_plift2 {M} `{PredLift2 M} {S X Y}
  (Pre Post : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m1 : StateT S M X)
  (m2 : StateT S M Y) : Prop :=
  forall s1 s2,
    Pre s1 s2 ->
    plift2 (prod_rel P Post) (m1 s1) (m2 s2).

Definition poram_lift2 {X Y} (Pre Post : state -> state -> Prop)
  (P : X -> Y -> Prop) : Poram X -> Poram Y -> Prop :=
  state_plift2
    (fun s s' => well_formed s /\ well_formed s' /\ Pre s s')
    (fun s s' => well_formed s /\ well_formed s' /\ Post s s')
    P.

Lemma state_plift2_ret {M} `{PredLift M} {S X Y}
  (Pre : S -> S -> Prop)
  (P : X -> Y -> Prop) : forall x y,
  P x y -> state_plift2 Pre Pre P
    (mreturn x) (mreturn y).
Proof.
  intros x y Hxy s1 s2 Hs1s2.
  apply plift2_ret.
  split; auto.
Qed.

Lemma poram_lift2_ret {X Y}
  (Pre : state -> state -> Prop)
  (P : X -> Y -> Prop) : forall x y,
  P x y -> poram_lift2 Pre Pre P
    (mreturn x) (mreturn y).
Proof.
  apply state_plift2_ret.
Qed.

Lemma state_plift2_bind {M} `{PredLift2 M}
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


Definition equiv {X} (m1 m2 : Poram X) : Prop :=
  poram_lift2
    state_equiv
    state_equiv
    eq m1 m2.
(*
  state_plift2
    (fun s1 s2 =>
      well_formed s1 /\
      well_formed s2 /\
      state_equiv s1 s2)
    (fun s1 s2 =>
      well_formed s1 /\
      well_formed s2 /\
      state_equiv s1 s2)
    eq m1 m2
*)

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

Lemma plift2_forall {I X Y}
  (P : I -> X -> Y -> Prop)
  (m : dist X) (m' : dist Y) :
  (forall i, plift2 (P i) m m') ->
  plift2 (fun x y => forall i, P i x y) m m'.
Proof.
  intros.
  unfold pforall; simpl in *.
  unfold dist_lift2 in *; simpl in *.
  unfold dist_lift in *.
  destruct m as [l q]; simpl in *; clear q.
  destruct m' as [l' q']; simpl in *; clear q'.
  rewrite Forall_forall.
  intros x Hx.
  rewrite Forall_forall.
  intros y Hy i.
  specialize (H i).
  rewrite Forall_forall in H.
  specialize (H x Hx).
  rewrite Forall_forall in H.
  apply H; auto.
Qed.

Lemma state_plift_split {S X}
  (m : StateT S dist X)
  (Pre Post1 Post2 : S -> Prop)
  (P : X -> Prop) :
  state_plift Pre Post1 P m ->
  state_plift Pre Post2 triv m ->
  state_plift Pre (pand Post1 Post2) P m.
Proof.
  intros.
  intros s Hs.
  specialize (H s Hs).
  specialize (H0 s Hs).
  pose proof (plift_conj _ _ _ H H0).
  eapply dist_has_weakening; [|exact H1].
  intros [x s'] [[H5 H6] [_ H7]].
  split; auto.
  split; auto.
Qed.

Lemma state_plift_proj1 {M} `{PredLift M} {S X}
  (m : StateT S M X)
  (Pre1 Pre2 Post : S -> Prop)
  (P : X -> Prop) :
  state_plift Pre1 Post P m ->
  state_plift (pand Pre1 Pre2) Post P m.
Proof.
  intros Hm s [Hs _].
  apply (Hm s Hs).
Qed.

Lemma kv_rel_functional : forall s,
  well_formed s ->
  forall k v v',
    kv_rel k v s ->
    kv_rel k v' s ->
    v = v'.
Proof.
Admitted.

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

Lemma impl_trans {X} (m : dist X)
  (P Q R : X -> Prop) :
  plift (fun x => P x -> Q x) m ->
  plift (fun x => Q x -> R x) m ->
  plift (fun x => P x -> R x) m.
Proof.
  unfold plift; simpl.
  destruct m as [l q]; simpl; clear q.
  repeat rewrite Forall_forall.
  firstorder.
Qed.

Lemma plift_triv {X} (m : dist X) (P : Prop) :
  P -> plift (fun _ => P) m.
Proof.
  destruct m as [l q].
  unfold plift; simpl; clear q.
  rewrite Forall_forall.
  tauto.
Qed.

Definition sigma {X} (P : X -> Prop) (m : dist X) : Prop :=
  Exists P (List.map fst (dist_pmf m)).

Lemma curry {X} (P : X -> Prop) (Q : Prop) (m : dist X) :
  (sigma P m -> Q) ->
  plift (fun x => P x -> Q) m.
Proof.
  unfold sigma, plift; simpl.
  unfold dist_lift.
  destruct m as [l q]; simpl; clear q.
  intro pf.
  rewrite Forall_forall.
  intros x Hx1 Hx2.
  apply pf.
  rewrite Exists_exists.
  exists x; tauto.
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

Lemma state_plift2_conj {S X Y}
  (Pre Post1 Post2 : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m1 : StateT S dist X)
  (m2 : StateT S dist Y) :
  state_plift2 Pre Post1 P m1 m2 ->
  state_plift2 Pre Post2 P m1 m2 ->
  state_plift2 Pre (fun s s' => Post1 s s' /\ Post2 s s') P m1 m2.
Proof.
  intros H1 H2 s1 s2 Hs1s2.
  specialize (H1 s1 s2 Hs1s2).
  specialize (H2 s1 s2 Hs1s2).
  unfold plift2 in *; simpl in *.
  unfold dist_lift2 in *.
  pose proof (plift_conj _ _ _ H1 H2) as H3.
  eapply dist_has_weakening; [|exact H3].
  intros [x s] [H4 H5].
  apply plift_conj.
  - eapply dist_has_weakening; [|exact H4].
    intros [] []; auto.
  - apply plift_conj.
    + eapply dist_has_weakening; [|exact H4].
      intros [] []; auto.
    + eapply dist_has_weakening; [|exact H5].
      intros [] []; auto.
Qed.

Lemma poram_lift2_conj {X Y}
  (Pre Post1 Post2 : state -> state -> Prop)
  (P : X -> Y -> Prop)
  (m1 : Poram X)
  (m2 : Poram Y) :
  poram_lift2 Pre Post1 P m1 m2 ->
  poram_lift2 Pre Post2 P m1 m2 ->
  poram_lift2 Pre (fun s s' => Post1 s s' /\ Post2 s s') P m1 m2.
Proof.
  intros.
  pose proof (state_plift2_conj _ _ _ _ m1 m2 H H0).
  unfold poram_lift2.
  intros s s' pfs.
  specialize (H1 s s' pfs).
  unfold plift2 in *; simpl in *.
  unfold dist_lift2 in *.
  eapply dist_has_weakening; [|exact H1].
  intros [x t] pf; simpl.
  eapply dist_has_weakening; [|exact pf].
  intros [y t'] [pf1 pf2].
  unfold prod_rel; tauto.
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

Lemma poram_split_post_and_pred {X Y}
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

Definition undef k s :=
  ~ exists v, kv_rel k v s.

Definition def_or_undef k s :
  { v : nat & kv_rel k v s } +
  { undef k s }.
Proof.
Admitted.

Definition get_val k s : option nat :=
  match def_or_undef k s with
  | inleft p => Some (projT1 p)
  | inright _ => None
  end.

Lemma kv_rel_get_val : forall k v s,
  well_formed s ->
  kv_rel k v s -> get_val k s = Some v.
Proof.
  intros k v s wf_s Hkv.
  unfold get_val.
  destruct (def_or_undef k s) as [[v' Hkv']|Hk].
  - simpl.
    rewrite kv_rel_functional with (s := s) (k := k) (v := v) (v' := v'); auto.
  - elim Hk.
    exists v; auto.
Qed.

Lemma get_val_kv_rel : forall k v s,
  well_formed s ->
  get_val k s = Some v -> kv_rel k v s.
Proof.
  intros k v s wf_s gv_k.
  unfold get_val in gv_k.
  destruct (def_or_undef k s) as [[v' Hv']|]; [|discriminate].
  inversion gv_k; congruence.
Qed.

Lemma undef_get_val : forall k s,
  well_formed s ->
  undef k s -> get_val k s = None.
Proof.
  intros k s wf_s Hks.
  unfold get_val.
  destruct (def_or_undef k s) as [[v Hkv]|Hk]; auto.
  elim Hks.
  exists v; auto.
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
  specialize (Hss' k).
  split; intro pf.
  - rewrite kv_rel_get_val with (v := v) in Hss'; auto.
    symmetry in Hss'.
    apply get_val_kv_rel; auto.
  - rewrite kv_rel_get_val with (v := v) (s := s') in Hss'; auto.
    apply get_val_kv_rel; auto.
Qed.

Lemma read_wf k :
  poram_lift
    triv
    triv
    triv
    (read k).
Proof.
Admitted.

Lemma read_pres_kv k v k' :
  poram_lift
    (kv_rel k v)
    (kv_rel k v)
    triv
    (read k').
Proof.
Admitted.

Lemma read_undef k k' :
  poram_lift
    (undef k)
    (undef k)
    triv
    (read k').
Proof.
Admitted.

Lemma read_val k v :
  poram_lift
    (kv_rel k v)
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

Lemma write_wf k v :
  poram_lift
    triv
    triv
    triv
    (write k v).
Proof.
Admitted.

Lemma write_undef k k' v :
  k <> k' ->
  poram_lift
    (undef k')
    (undef k')
    triv
    (write k v).
Proof.
Admitted.

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

Lemma write_val_eq k v :
  poram_lift
    triv
    (kv_rel k v)
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

Lemma write_val_neq k v k' v' :
  k <> k' ->
  poram_lift
    (kv_rel k' v')
    (kv_rel k' v')
    triv
    (write k v).
Proof.
Admitted.

Lemma read_pres_equiv k' s :
  poram_lift (state_equiv s) (state_equiv s) triv (read k').
Proof.
  intros s' [wf_s' eq_ss'].
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
           pose (read_pres_kv k x k' s' (conj wf_s' k0)).
           eapply dist_has_weakening; [|exact p].
           intros [] [_ pf] pf'.
           simpl in pf'.
           apply eq_ss'.
           destruct pf.
           rewrite kv_rel_functional with (s := s0) (k := k) (v := v) (v' := x); auto.
        -- pose (read_undef k k' s' (conj wf_s' u)).
           eapply dist_has_weakening; [|exact p].
           intros [] [_ pf]; simpl; intros pf'.
           destruct pf.
           elim H0.
           exists v; exact pf'.
Qed.

Definition dummy {X Y} (P : X -> Prop) (Q : Y -> Prop) : X -> Y -> Prop :=
  fun x y => P x /\ Q y.

Lemma state_plift2_strengthen_pre {S X Y}
  (Pre Pre' Post : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m : StateT S dist X)
  (m' : StateT S dist Y) :
  (forall s s', Pre' s s' -> Pre s s') ->
  state_plift2 Pre Post P m m' ->
  state_plift2 Pre' Post P m m'.
Proof.
  intros HPre'Pre H1 s s' Hss'.
  apply H1.
  apply HPre'Pre.
  exact Hss'.
Qed.

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
  (P : Prop) :
  P -> plift2 (fun _ _ => P) dx dy.
Proof.
  intro.
  unfold plift2.
  simpl.
  unfold dist_lift2.
  apply plift_triv.
  apply plift_triv.
  auto.
Qed.

(*
Lemma state_plift_split_dummy {S X Y}
  (Pre Pre' Post Post' : S -> Prop)
  (m : StateT S dist X) (m' : StateT S dist Y) :
  state_plift Pre Post triv m ->
  state_plift Pre' Post' triv m' ->
  state_plift2 (dummy Pre Pre') (dummy Post Post') triv2 m m'.
Proof.
  intros H1 H2 s s' [Hs Hs'].
  specialize (H1 _ Hs).
  specialize (H2 _ Hs').
  apply plift2_conj.
  - unfold triv2. apply plift2_triv.
    exact I.
  - unfold plift2; simpl.
    unfold dist_lift2.
    eapply dist_has_weakening; [|exact H1].
    intros [] [_ pf].
    eapply dist_has_weakening; [|exact H2].
    intros [] [_ pf'].
    split; auto.
Qed.
*)

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
    exact I.
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

Lemma plift2_implication {X Y}
  {P : X -> Prop} {Q : Y -> Prop}
  (m : dist X) (m' : dist Y) :
  (sigma P m -> plift Q m') ->
  plift2 (fun x y => P x -> Q y) m m'.
Proof.
  unfold plift2; simpl.
  unfold dist_lift2.
  unfold plift; simpl.
  unfold dist_lift, sigma.
  destruct m as [l q]; simpl; clear q.
  destruct m' as [l' q']; simpl; clear q'.
  repeat rewrite Forall_forall.
  rewrite Exists_exists.
  intro pf.
  intros x Hx.
  rewrite Forall_forall.
  intros y Hy p.
  apply pf; auto.
  exists x; split; auto.
Qed.

Lemma plift2_implication2 {X Y}
  {P : X -> Prop} {Q : Y -> Prop}
  (m : dist X) (m' : dist Y) :
  (sigma Q m' -> plift P m) ->
  plift2 (fun x y => Q y -> P x) m m'.
Proof.
  unfold plift2; simpl.
  unfold dist_lift2.
  unfold plift; simpl.
  unfold dist_lift, sigma.
  destruct m as [l q]; simpl; clear q.
  destruct m' as [l' q']; simpl; clear q'.
  repeat rewrite Forall_forall.
  rewrite Exists_exists.
  intro pf.
  intros x Hx.
  rewrite Forall_forall.
  intros y Hy p.
  apply pf; auto.
  exists y; split; auto.
Qed.

Lemma sigma_plift {X} (P Q : X -> Prop) (d : dist X) :
  plift P d -> sigma Q d ->
  sigma (fun x => P x /\ Q x) d.
Proof.
  unfold plift, sigma; simpl.
  unfold dist_lift.
  destruct d as [l q]; simpl; clear q.
  rewrite Forall_forall.
  repeat rewrite Exists_exists; intros.
  destruct H0 as [x [Hx1 Hx2]].
  exists x; split; auto.
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

Lemma state_equiv_undef s s' k :
  state_equiv s s' ->
  undef k s ->
  undef k s'.
Proof.
  intros eq_ss' Hks [v Hkv].
  elim Hks.
  exists v.
  apply eq_ss'; auto.
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
  apply poram_split_post_and_pred.
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
              ** apply plift2_split_eq with (z := Some v').
                 --- pose proof (write_val_neq k v k' v' n s (conj wf_s Hk'v')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     apply kv_rel_get_val; auto.
                 --- apply eq_ss' in Hk'v'.
                     pose proof (write_val_neq k v k' v' n s' (conj wf_s' Hk'v')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     apply kv_rel_get_val; auto.
              ** apply plift2_split_eq with (z := None).
                 --- pose proof (write_undef k k' v n s (conj wf_s Hk')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     apply undef_get_val; auto.
                 --- apply state_equiv_undef with (s' := s') in Hk'; auto.
                     pose proof (write_undef k k' v n s' (conj wf_s' Hk')) as pf.
                     eapply dist_has_weakening; [|exact pf].
                     intros [x t] [_ [wf_t Ht]]; simpl.
                     apply undef_get_val; auto.
    + intros _ _ _.
      apply poram_lift2_ret_l.
      intro s''.
      exact (read_pres_equiv k s'').
Qed.

Print Assumptions write_read.

End EquivProofs.
