(*
Require Import List RAM.
Import ListNotations.

Section StateMonad.

Definition State S X := S -> X * S.

Definition ret {S X} : X -> State S X := pair.

Definition bind {S X Y} : State S X ->
  (X -> State S Y) -> State S Y :=
  fun m f s => let (x, s') := m s in f x s'.

Definition get {S} : State S S :=
  fun s => (s, s).

Definition put {S} : S -> State S unit :=
  fun s _ => (tt, s).

Definition state_lift {S X} (Pre Post : S -> Prop)
  (P : X -> Prop) : State S X -> Prop :=
  fun f => forall s, Pre s ->
    P (fst (f s)) /\ Post (snd (f s)).

Lemma weaken_lemma {S X}
  {Pre : S -> Prop}
  (Post : S -> Prop)
  {Post' : S -> Prop}
  (P : X -> Prop)
  {P' : X -> Prop}
  (m : State S X) :
  (forall s, Post s -> Post' s) ->
  (forall x, P x -> P' x) ->
  state_lift Pre Post P m ->
  state_lift Pre Post' P' m.
Proof.
  intros HPostPost' HPP' Hm s Hs.
  split.
  - apply HPP'.
    now apply Hm.
  - apply HPostPost'.
    now apply Hm.
Qed.

Lemma ret_lemma {S X}
  {Pre : S -> Prop}
  {P : X -> Prop}
  {x : X} :
  P x ->
  state_lift Pre Pre P (ret x).
Proof.
  simpl.
  intros p st; simpl.
  tauto.
Qed.

Lemma bind_lemma {S X Y}
  {Pre : S -> Prop}
  (Mid : S -> Prop)
  {Post : S -> Prop}
  (P : X -> Prop)
  {Q : Y -> Prop}
  {mx : State S X}
  {f : X -> State S Y} :
  state_lift Pre Mid P mx ->
  (forall x, P x -> state_lift Mid Post Q (f x)) ->
  state_lift Pre Post Q (bind mx f).
Proof.
  intros Hmx Hf s Hs.
  destruct (Hmx s Hs) as [HP HMid].
  destruct (Hf _ HP _ HMid).
  unfold bind.
  destruct (mx s); simpl in *; now split.
Qed.

Lemma get_lemma {S}
  {Pre : S -> Prop} :
  state_lift Pre Pre Pre get.
Proof.
  intros s; simpl.
  tauto.
Qed.

Lemma put_lemma {S}
  {Pre Pre' : S -> Prop}
  {s : S} :
  Pre' s ->
  state_lift Pre Pre' (fun _ => True) (put s).
Proof.
  intros Hs s' _; simpl.
  tauto.
Qed.

End StateMonad.

Section Map.

Definition Map (K V : Type) : Type :=
  list (K * V).

Definition well_formed {K V} (m : Map K V) : Prop :=
  NoDup (map fst m). (* no repeat keys *)

Class DecEq (X : Type) := {
  dec_eq : forall x x' : X, { x = x' } + { x <> x' }
  }.

Fixpoint insert {K V} `{DecEq K} (k : K) (v : V)
  (m : Map K V) : Map K V :=
  match m with
  | [] => [(k,v)]
  | (k',v') :: m' =>
    match dec_eq k k' with
    | left _ => (k',v) :: m'
    | right _ => (k',v') :: insert k v m'
    end
  end.

Lemma In_insert_invert {K V} `{DecEq K} {p : K * V}
  {k : K} {v : V} {m : Map K V} : In p (insert k v m) ->
  p = (k, v) \/ In p m.
Proof.
  induction m as [|[k' v'] m'].
  - simpl; firstorder.
  - simpl.
    destruct (dec_eq k k').
    + intros [Heq|HIn].
      * left; congruence.
      * tauto.
    + intros [Heq|HIn]; tauto.
Qed.

Lemma well_formed_insert {K V} `{DecEq K} (k : K) (v : V)
  (m : Map K V) : well_formed m -> well_formed (insert k v m).
Proof.
  induction m as [|[k' v'] m].
  - intros _; simpl.
    repeat constructor.
    intros [].
  - intro wf.
    simpl.
    destruct (dec_eq k k').
    + exact wf.
    + unfold well_formed.
      simpl; constructor.
      * rewrite in_map_iff.
        intros [[k'' v''] [Heq HIn]].
        simpl in Heq.
        rewrite Heq in HIn; clear Heq.
        destruct (In_insert_invert HIn) as [Heq|HIn'].
        -- inversion Heq; firstorder.
        -- inversion wf.
           apply H2.
           rewrite in_map_iff.
           exists (k', v'').
           split; [reflexivity|auto].
      * apply IHm.
        now inversion wf.
Qed.

Fixpoint lookup {K V} `{DecEq K} (k : K)
  (m : Map K V) : option V :=
  match m with
  | [] => None
  | (k',v) :: m' =>
    match dec_eq k k' with
    | left _ => Some v
    | right _ => lookup k m'
    end
  end.

Lemma lookup_insert {K V} `{DecEq K} (k : K) (v : V)
  (m : Map K V) : well_formed m -> lookup k (insert k v m) = Some v.
Proof.
  intro wf_m.
  induction m as [|[k' v'] m'].
  - simpl.
    destruct (dec_eq k k); [reflexivity|contradiction].
  - simpl.
    destruct (dec_eq k k').
    + simpl.
      destruct (dec_eq k k'); [reflexivity|contradiction].
    + simpl.
      destruct (dec_eq k k'); [contradiction|].
      apply IHm'.
      now inversion wf_m.
Qed.

End Map.

Module KV_State <: StateMonad.
  Definition state (S X : Type) := prod X S.
  Definition State (S X : Type) := S -> prod X S.
  Definition ret {S} := @ret S.
  Definition bind {S} := @bind S.
  Definition get {S} := @get S.
  Definition put {S} := @put S.
End KV_State.

Module KV_RAM <: RAM (KV_State).
  Import KV_State.

  Parameter K : Type.
  Parameter V : Type.
  Context `{DecEq K}.

  Definition S : Type := Map K V.
  Definition well_formed := @well_formed K V.
  Definition Vw (V : Type) := option V.

  Definition bind {X Y} := @bind S X Y.
  Definition ret {X} := @ret S X.
  Definition get := @get S.
  Definition put := @put S.

  Definition read (k : K) : State S V :=
    bind 
      get
      (fun s => ret (lookup k s)).

  Definition write (k : K) (v : V) : State S (Vw V) :=
    bind 
      get 
      (fun (s : Map K V) =>
        bind
          (put (insert k v s))
          (fun _ => ret None)).

  Definition wrap (v : V) := Some v.

  Definition get_payload (s : state S V) := fst s.

  Definition write_and_read (k : K) (v : V) : State S (Vw V):=
    bind (write k v) (fun _ => read k).

  Lemma write_and_read_lemma (k : K) (v : V) :
    state_lift
      well_formed
      well_formed
      (eq (Some v))
      (write_and_read k v).
  Proof.
    apply (bind_lemma
      (fun st => well_formed st /\ lookup k st = Some v)
      (fun _ => True)).
    - simpl.
      apply (bind_lemma
        well_formed
        well_formed).
      + apply get_lemma.
      + intros st wf_st.
        apply put_lemma.
        split.
        * apply well_formed_insert.
          exact wf_st.
        * apply lookup_insert.
          exact wf_st.
    - intros _ _.
      apply (bind_lemma
        well_formed
        (fun m => Some v = lookup k m)).
      + apply (weaken_lemma
          (fun st => well_formed st /\ lookup k st = Some v)
          (fun st => well_formed st /\ lookup k st = Some v)).
        * tauto.
        * firstorder.
        * apply get_lemma.
      + intros st Hkv.
        apply ret_lemma.
        exact Hkv.
  Qed.

  Theorem write_and_read_correct (k : K) (v : V) (s : S) :
    well_formed s ->
    fst (write_and_read k v s) = Some v.
  Proof.
    intro wf_s.
    destruct (write_and_read_lemma k v s wf_s) as [Hv _].
    symmetry; exact Hv.
  Qed.

  Lemma read_and_read_lemma (k : K) (s : S):
    @state_lift S (Vw V)
      well_formed
      well_formed
      (fun v => eq (get_payload (bind (read k) ret s)) v)
      (bind (read k) (fun _ => read k)).
  Proof.
    admit. (* TODO *)
  Admitted.

  (* RAM laws (TODO move some of the above stuff here) *)
  Theorem read_read :
    forall (k : K) (s : S), 
      well_formed s ->
      get_payload ((bind (read k) (fun _ => read k)) s) =
      get_payload ((bind (read k) (fun v => ret v)) s). 
  Proof.
    intros. pose proof (read_and_read_lemma k s). 
    unfold state_lift in H1. specialize (H1 s H0). 
    destruct H1. auto.
  Qed.

  Theorem read_write :
    forall (k : K) (v : V) (s : S),
      well_formed s ->
      get_payload ((bind (write k v) (fun _ => read k)) s) =
      get_payload ((bind (write k v) (fun _ => ret (wrap v))) s).
  Proof.
  Admitted.

  Theorem read_write_commute :
    forall (k1 k2 : K) (v : V) f (s : S),
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

End KV_RAM.
*)
