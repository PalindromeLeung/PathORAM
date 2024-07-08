Require Import List.
Import ListNotations.

Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import POram.Utils.Tree.
Require Import POram.Utils.Rationals.
Require Import POram.Utils.Distributions.
Require Import POram.System.PathORAM.
Require Import POram.System.PathORAMDef.

Definition empty_dict {K V} : dict K V := Dict [].

Definition empty_position_map : position_map := empty_dict.
Definition empty_stash : stash := [].

Fixpoint empty_oram n : oram :=
  match n with
  | 0 => leaf
  | S m => node None (empty_oram m) (empty_oram m)
  end.

Definition empty_state `{Config} : state := {|
  state_position_map := empty_position_map;
  state_stash := empty_stash;
  state_oram := empty_oram (S LOP);
  |}.

Lemma lookup_empty {K V} `{Ord K} (v_def : V) (k : K) :
  lookup_dict v_def k (empty_dict) = v_def.
Proof.
  reflexivity.
Qed.

Lemma length_makeBoolList b n :
  length (makeBoolList b n) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl; congruence.
Qed.

Lemma get_all_blks_tree_empty n :
  get_all_blks_tree (empty_oram n) = [].
Proof.
  induction n.
  - auto.
  - simpl.
    rewrite IHn; auto.
Qed.

Lemma empty_oram_p_b n :
  is_p_b_tr (empty_oram n) n.
Proof.
  induction n; simpl.
  - auto.
  - split; auto.
Qed.

Lemma empty_state_wf `{C : Config} : well_formed empty_state.
Proof.
  split.
  - constructor.
  - unfold state_oram.
    unfold empty_state.
    rewrite get_all_blks_tree_empty.
    constructor.
  - intros id [Hid1 _].
    unfold state_oram in Hid1.
    unfold empty_state in Hid1.
    rewrite get_all_blks_tree_empty in Hid1.
    destruct Hid1.
  - unfold state_oram.
    unfold empty_state.
    apply empty_oram_p_b.
  - intros.
    unfold o in H.
    unfold state_oram in H.
    unfold empty_state in H.
    rewrite get_all_blks_tree_empty in H.
    destruct H.
  - intros.
    simpl in m.
    unfold m.
    unfold empty_position_map.
    rewrite lookup_empty.
    rewrite length_makeBoolList.
    reflexivity.
Qed.

Fixpoint get_traces_aux `{Config} (acc : list path) (ops : list (block_id * operation)) : Poram (list path) :=
  match ops with
  | [] => mreturn acc
  | (id,op) :: ops' =>
    p <- access id op;;
    get_traces_aux (fst p :: acc) ops'
  end.

Definition get_traces `{Config} (ops : list (block_id * operation)) (init : state) : dist (list path) :=
  p <- get_traces_aux [] ops init;;
  mreturn (fst p).

Fixpoint get_vals_aux `{Config} (acc : list nat) (ops : list (block_id * operation)) : Poram (list nat) :=
  match ops with
  | [] => mreturn acc
  | (id,op) :: ops' =>
    p <- access id op;;
    get_vals_aux (snd p :: acc) ops'
  end.

Definition get_vals `{Config} (ops : list (block_id * operation)) (init : state) : dist (list nat) :=
  p <- get_vals_aux [] ops init;;
  mreturn (List.rev (fst p)).

Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlZInt.
Extraction Language OCaml.

Extract Inductive dist => "Rand.t" [""].
Extract Constant mreturn_dist => "Rand.ret".
Extract Constant mbind_dist => "Rand.bind".
Extract Constant coin_flip => "Rand.coin_flip".

Set Warnings "-extraction-default-directory".

Extraction "POram.ml" empty_state get_traces get_vals.
