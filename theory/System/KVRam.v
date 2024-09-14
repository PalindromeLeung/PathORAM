Require Import List RAM.
Import ListNotations.

Section OptStateMonad.

Definition OptState S X := S -> option (X * S).

Definition ret {S X} : X -> OptState S X :=
  fun x s => Some (x, s).

Definition bind {S X Y} : OptState S X ->
  (X -> OptState S Y) -> OptState S Y :=
  fun m f s =>
    match m s with
    | Some (x, s') => f x s'
    | None => None
    end.

Definition get {S} : OptState S S :=
  fun s => Some (s, s).

Definition put {S} : S -> OptState S unit :=
  fun s _ => Some (tt, s).

Definition opt_lift {X} (P : X -> Prop) : option X -> Prop :=
  fun o =>
    match o with
    | Some x => P x
    | None => True
    end.

Definition opt_lift2 {X Y} (P : X -> Y -> Prop) : option X -> option Y -> Prop :=
  fun o1 o2 =>
    opt_lift (fun x => opt_lift (P x) o2) o1.

Definition opt_state_plift {S X}
  (Pre Post : S -> Prop)
  (P : X -> Prop) : OptState S X -> Prop :=
  fun f => forall s, Pre s ->
    opt_lift (fun p => P (fst p) /\ Post (snd p)) (f s).

Lemma weaken_lemma {S X}
  {Pre : S -> Prop}
  (Post : S -> Prop)
  {Post' : S -> Prop}
  (P : X -> Prop)
  {P' : X -> Prop}
  (m : OptState S X) :
  (forall s, Post s -> Post' s) ->
  (forall x, P x -> P' x) ->
  opt_state_plift Pre Post P m ->
  opt_state_plift Pre Post' P' m.
Proof.
  intros HPostPost' HPP' Hm s Hs.
  unfold opt_state_plift in Hm.
  specialize (Hm s Hs).
  destruct (m s); simpl in *; auto.
  destruct Hm; split.
  - apply HPP'; auto.
  - apply HPostPost'; auto.
Qed.

Lemma ret_lemma {S X}
  {Pre : S -> Prop}
  {P : X -> Prop}
  {x : X} :
  P x ->
  opt_state_plift Pre Pre P (ret x).
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
  {mx : OptState S X}
  {f : X -> OptState S Y} :
  opt_state_plift Pre Mid P mx ->
  (forall x, P x -> opt_state_plift Mid Post Q (f x)) ->
  opt_state_plift Pre Post Q (bind mx f).
Proof.
  intros Hmx Hf s Hs.
  specialize (Hmx s Hs).
  unfold bind.
  destruct (mx s) as [[x s']|]; simpl in *; auto.
  destruct Hmx.
  apply Hf; auto.
Qed.

Lemma get_lemma {S}
  {Pre : S -> Prop} :
  opt_state_plift Pre Pre Pre get.
Proof.
  intros s; simpl.
  tauto.
Qed.

Lemma put_lemma {S}
  {Pre Pre' : S -> Prop}
  {s : S} :
  Pre' s ->
  opt_state_plift Pre Pre' (fun _ => True) (put s).
Proof.
  intros Hs s' _; simpl.
  tauto.
Qed.

End OptStateMonad.

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
  Definition state (S X : Type) := option (prod X S).
  Definition State (S X : Type) := S -> option (prod X S).
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

  Definition bind {X Y} := @bind S X Y.
  Definition ret {X} := @ret S X.
  Definition get := @get S.
  Definition put := @put S.

  Definition lift {X} (o : option X) : OptState S X :=
    fun s =>
      match o with
      | Some x => Some (x, s)
      | None => None
      end.

  Definition read (k : K) : State S V :=
    bind get (fun s =>
    lift (lookup k s)).

  Definition write (k : K) (v : V) : State S unit :=
    bind get (fun s =>
    bind (put (insert k v s)) (fun _ =>
    ret tt)).

Definition prod_rel {X X' Y Y'} (P : X -> X' -> Prop) (Q : Y -> Y' -> Prop) :
  X * Y -> X' * Y' -> Prop :=
  fun p1 p2 =>
    P (fst p1) (fst p2) /\
    Q (snd p1) (snd p2).

  Definition state_equiv (s1 s2 : S) : Prop :=
    forall (k : K), lookup k s1 = lookup k s2.

  Definition equiv {X : Type} (m1 m2 : State S X) : Prop :=
    forall s1 s2, well_formed s1 -> well_formed s2 -> state_equiv s1 s2 ->
    opt_lift2 (prod_rel eq state_equiv) (m1 s1) (m2 s2).

  Theorem read_write : forall (k : K),
    equiv
      (ret tt)
      (bind (read k) (fun v => write k v)).
  Proof.
  Admitted.

  Theorem write_read : forall (k : K) (v : V),
    equiv
      (bind (write k v) (fun _ => ret v))
      (bind (write k v) (fun _ => read k)).
  Proof.
  Admitted.

  Theorem read_read : forall (k : K),
    equiv
      (bind (read k) (fun v => ret v))
      (bind (read k) (fun _ => read k)).
  Proof.
  Admitted.

  Theorem read_commute : forall (k1 k2 : K),
    equiv
      (bind (read k1) (fun v1 =>
        bind (read k2) (fun v2 =>
        ret (v1, v2))))
      (bind (read k2) (fun v2 =>
        bind (read k1) (fun v1 =>
        ret (v1, v2)))).
  Proof.
  Admitted.

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
  Admitted.

  Theorem write_commute : forall (k1 k2 : K) (v1 v2 : V),
    k1 <> k2 ->
    equiv
      (bind (write k1 v1) (fun _ =>
        write k2 v2))
      (bind (write k2 v2) (fun _ =>
        write k1 v1)).
  Proof.
  Admitted.

  Theorem write_absorb : forall (k : K) (v v' : V),
    equiv
      (bind (write k v) (fun _ => write k v'))
      (write k v').
  Proof.
  Admitted.

End KV_RAM.
