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

Definition snd_eq {X Y} (p1 p2 : X * Y) : Prop :=
  snd p1 = snd p2.

Lemma read_access_lawful (id : block_id) :
  lawful snd_eq (read_access id).
Proof.
Admitted.

Lemma write_access_lawful (id : block_id) (v : nat) :
  lawful snd_eq (write_access id v).
Proof.
Admitted.

Definition read id : Poram nat :=
  map snd (read_access id).

Definition write id v : Poram nat :=
  map snd (write_access id v).

Definition triv {X} : X -> Prop :=
  fun _ => True.

Lemma kv_rel_read_1 : forall k v k',
  state_plift
    (fun st => well_formed st /\ kv_rel k v st)
    (fun st => well_formed st /\ kv_rel k v st)
    triv
    (read_access k').
Proof.
Admitted.

Lemma kv_rel_read_2 : forall s k v k',
  plift
    (fun x => kv_rel k v (snd x) -> kv_rel k v s)
    (read_access k' s).
Proof.
Admitted.

Lemma kv_rel_write_neq : forall k v k' v',
  k <> k' ->
  state_plift
    (fun st => well_formed st /\ kv_rel k v st)
    (fun st => well_formed st /\ kv_rel k v st)
    triv
    (write_access k' v').
Proof.
Admitted.

Lemma kv_rel_write_eq : forall k v,
  state_plift
    well_formed
    (fun st => well_formed st /\ kv_rel k v st)
    triv
    (write_access k v).
Proof.
Admitted.

Definition state_plift2 {M} `{PredLift2 M} {S X Y}
  (Pre Post : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m1 : StateT S M X)
  (m2 : StateT S M Y) : Prop :=
  forall s1 s2,
    Pre s1 s2 ->
    plift2 (prod_rel P Post) (m1 s1) (m2 s2).

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

Definition equiv {X} (m1 m2 : Poram X) : Prop :=
  state_plift2
    (fun s1 s2 =>
      well_formed s1 /\
      well_formed s2 /\
      state_equiv s1 s2)
    (fun s1 s2 =>
      well_formed s1 /\
      well_formed s2 /\
      state_equiv s1 s2)
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

Definition lawful {M} `{PredLift2 M} {S X}
  (m : StateT S M X) (Pre : S -> S -> Prop) :=
  state_plift2 Pre Pre eq m m.

Definition pand {X} (P Q : X -> Prop) : X -> Prop :=
  fun x => P x /\ Q x.

Lemma write_access_wf2_eq : forall
  (id : block_id) (v_old v_new : nat),
  state_plift
  (pand well_formed (kv_rel id v_old))
  (pand well_formed (kv_rel id v_new))
  (has_value v_old)
  (write_access id v_new).
Proof.
Admitted.

Lemma write_access_wf2_neq : forall
  (id id' : block_id) (v v' : nat),
  id <> id' ->
  state_plift
  (pand well_formed (kv_rel id' v'))
  (pand well_formed (kv_rel id' v'))
  (has_value v)
  (write_access id v).
Proof.
Admitted.

Lemma state_plift2_write_write k v : 
  state_plift2
  (fun s1 s2 : state =>
    well_formed s1 /\
    well_formed s2 /\
    state_equiv s1 s2)
  (fun s1 s2 : state =>
    well_formed s1 /\
    well_formed s2 /\
    state_equiv s1 s2 /\
    kv_rel k v s1)
  triv2
  (write k v)
  (write k v).
Proof.
  intros s s'.
  intros [H1 [H2 H3]].
  unfold plift2.
  unfold Pred_Dist_Lift2.
  unfold dist_lift2.
  eapply plift_bind.
  - eapply write_access_wf; auto.
  - intros [] pfs.
    apply plift_ret.
    eapply plift_bind.
    + eapply write_access_wf2_eq.
      split; auto.
      admit.
    + intros [] pfs2.
      apply plift_ret.
      simpl; split.
      * exact I.
      * simpl.
        split; try tauto.
        split; try tauto.
        admit.
        split.
        split; try tauto.


(* TODO: make write_access_wf_2 like read_access_wf_2 *)
Admitted.

Definition pforall {I X} (P : I -> X -> Prop) : X -> Prop :=
  fun x => forall i, P i x.

Lemma plift_conj {M} `{PredLift M} {X}
  (P Q : X -> Prop) (m : M X) :
  plift P m ->
  plift Q m ->
  plift (pand P Q) m.
Proof.
Admitted.

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

Lemma state_plift_split {M} `{PredLift M} {S X}
  (m : StateT S M X)
  (Pre Post1 Post2 : S -> Prop)
  (P : X -> Prop) :
  has_weakening M ->
  state_plift Pre Post1 P m ->
  state_plift Pre Post2 triv m ->
  state_plift Pre (pand Post1 Post2) P m.
Proof.
  intros.
  intros s Hs.
  specialize (H2 s Hs).
  specialize (H3 s Hs).
  pose proof (plift_conj _ _ _ H2 H3).
  eapply H1; [|exact H4].
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

Lemma read_access_wf2 : forall
  (id : block_id) (v : nat) s,
  state_plift
  (pand (pand well_formed (kv_rel id v)) (state_equiv s))
  (pand (pand well_formed (kv_rel id v)) (state_equiv s))
  (has_value v)
  (read_access id).
Proof.
  intros id v s'.
  apply state_plift_split.
  - apply dist_has_weakening.
  - apply state_plift_proj1.
    apply read_access_wf.
  - intros s [[H1 H2] H3].
    eapply dist_has_weakening with
      (P := fun x => state_equiv s' (snd x)).
    + intros [p s1] H4; split; auto.
      exact I.
    + eapply plift_forall.
      intro id'.
      eapply plift_forall.
      intro v'.
      apply plift_conj.
      * apply impl_dist.
        intro.
        assert (kv_rel id' v' s) by (apply H3; auto).
        pose proof (kv_rel_read_1 id' v' id s
          (conj H1 H0)).
        eapply dist_has_weakening; [|exact H4].
        intros [] pfs.
        apply pfs.
      * apply impl_trans with (Q := fun _ => kv_rel id' v' s).
        -- apply kv_rel_read_2.
        -- eapply plift_triv.
           apply H3.
Qed.

Lemma state_equiv_sym : forall s s',
  state_equiv s s' ->
  state_equiv s' s.
Admitted.

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

Lemma foobar k v :
  state_plift2
    (fun s s' =>
      state_equiv s s' /\
      kv_rel k v s /\
      kv_rel k v s')
    state_equiv
    (fun x x' => x = v /\ x' = v)
    (mreturn v)
    (read k).
Proof.
  intros s s' [eq_ss' [kv_s kv_s']].
  unfold plift2.
  apply plift_ret.
  apply plift_conj.
  - apply plift_conj; simpl fst.
    + apply plift_triv; reflexivity.
    + eapply plift_bind.
      * apply read_access_wf; split.
        -- admit.
        -- exact kv_s'.
      * intros [] ?.
        apply plift_ret.
        destruct H.
        destruct p; simpl.
        unfold has_value in H.
        symmetry; exact H.
  - simpl snd.
Admitted.

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

Axiom cheat : forall {X}, X.

Lemma state_plift2_conj {S X Y}
  (Pre Post1 Post2 : S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m1 : StateT S dist X)
  (m2 : StateT S dist Y) :
  state_plift2 Pre Post1 P m1 m2 ->
  state_plift2 Pre Post2 P m1 m2 ->
  state_plift2 Pre (fun s s' => Post1 s s' /\ Post2 s s') P m1 m2.
Proof.
Admitted.

Lemma state_plift2_forall {S V X Y}
  (Pre : S -> S -> Prop)
  (Post : V -> S -> S -> Prop)
  (P : X -> Y -> Prop)
  (m1 : StateT S dist X)
  (m2 : StateT S dist Y) :
  (forall v, state_plift2 Pre (Post v) P m1 m2) ->
  state_plift2 Pre (fun s s' => forall v, Post v s s') P m1 m2.
Proof.
Admitted.

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

Definition undef k s :=
  ~ exists v, kv_rel k v s.

Lemma def_or_undef k s :
  { exists v, kv_rel k v s } +
  { undef k s }.
Proof.
Admitted.

Lemma read_pres_kv k v k' :
  state_plift (kv_rel k v) (kv_rel k v) triv
  (read k').
Admitted.

Lemma read_pres_undef k k' :
  state_plift (undef k) (undef k) triv
  (read k').
Admitted.

Lemma function_property : forall s k v v',
  kv_rel k v s -> kv_rel k v' s -> v = v'.
Admitted.

Lemma read_val k v :
  state_plift (kv_rel k v) triv (eq v) (read k).
Proof.
Admitted.

Lemma write_val_eq k v :
  state_plift triv (kv_rel k v) triv (write k v).
Proof.
Admitted.

Lemma write_val_neq k v k' v' :
  k <> k' ->
  state_plift (kv_rel k' v') (kv_rel k' v') triv (write k v).
Proof.
Admitted.

Lemma read_pres_equiv k' s :
  state_plift (state_equiv s) (state_equiv s) triv (read k').
Proof.
  intros s' eq_ss'.
  eapply dist_has_weakening with
    (P := fun p => state_equiv s (snd p)).
  - intros [] pf; split; auto.
    exact I.
  - apply plift_forall.
    intro k.
    apply plift_forall.
    intro v.
    apply plift_conj.
    + apply impl_dist.
      intro pf.
      apply eq_ss' in pf.
      pose proof (read_pres_kv k v k' s' pf).
      eapply dist_has_weakening; [|exact H].
      intros []; tauto.
    + destruct (def_or_undef k s').
      * destruct e.
        pose (read_pres_kv k x k' s' H).
        eapply dist_has_weakening; [|exact p].
        intros [] [_ pf] pf'.
        simpl in pf'.
        apply eq_ss'.
        rewrite (function_property _ _ _ _ pf' pf).
        auto.
      * pose (read_pres_undef k k' s' u).
        eapply dist_has_weakening; [|exact p].
        intros [] [_ pf]; simpl; intros pf'.
        elim pf.
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

Axiom cheat2 : forall {X}, X.

Lemma plift2_and {X Y} {P Q : X -> Y -> Prop}
  (m : dist X) (m' : dist Y) :
  plift2 P m m' ->
  plift2 Q m m' ->
  plift2 (fun x y => P x y /\ Q x y) m m'.
Proof.
Admitted.

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
  apply split_post_and_pred.
  - eapply state_plift2_bind with
      (Mid := dummy (kv_rel k v) (kv_rel k v))
      (P := triv2).
    + apply state_plift2_strengthen_pre with
        (Pre := dummy well_formed well_formed).
      * unfold dummy; tauto.
      * apply state_plift_split_dummy.
        -- intros t _.
           apply write_val_eq; exact I.
        -- intros t _.
           apply write_val_eq; exact I.
    + intros _ _ _.
      apply state_plift2_ret_l.
      intro.
      pose (read_val k v).
      intros t [_ Ht].
      specialize (s1 t Ht).
      eapply dist_has_weakening; [|exact s1].
      intros [] [pf _]; split; auto. exact I.
  - apply state_plift2_bind with
      (Mid := fun s1 s2 => well_formed s1 /\ well_formed s2 /\ state_equiv s1 s2) (P := triv2).
    + apply state_plift2_conj.
      * admit.
      * apply state_plift2_conj.
        -- admit.
        -- intros t t' pfs.
           unfold plift2; simpl.
           apply plift2_conj.
           ++ unfold triv2.
              apply plift2_triv; auto.
           ++ apply plift2_forall.
              intro k'.
              apply plift2_forall.
              intro v'.
              destruct (nat_eq_dec k k').
              ** subst; apply plift2_and.
                 --- apply plift2_implication.
                     intro pf.
                     assert (v = v').
                     { admit. }
                     subst.
                     epose (write_val_eq k' v' t' I).
                     eapply dist_has_weakening; [|exact p].
                     intros []; simpl; tauto.
                 --- apply plift2_implication2.
                     intro pf.
                     assert (v = v').
                     { admit. }
                     subst.
                     epose (write_val_eq k' v' t I).
                     eapply dist_has_weakening; [|exact p].
                     intros []; simpl; tauto.
              ** apply plift2_and.
                 --- apply plift2_implication.
                     intro pf.
                     assert (kv_rel k' v' t').
                     { admit. }
                     epose (write_val_neq k v k' v' n t' H2).
                     eapply dist_has_weakening; [|exact p].
                     intros []; simpl; tauto.
                 --- apply plift2_implication2.
                     intro pf.
                     assert (kv_rel k' v' t).
                     { admit. }
                     epose (write_val_neq k v k' v' n t H2).
                     eapply dist_has_weakening; [|exact p].
                     intros []; simpl; tauto.
    + intros _ _ _.
      apply state_plift2_ret_l.
      intro s''. Search state_plift.
      pose (read_pres_equiv k s'').
      admit.
Admitted.

Print Assumptions write_read.

End EquivProofs.

