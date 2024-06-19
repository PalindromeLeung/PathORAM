Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Classes.EquivDec.
Require Import POram.Utils.Rationals.
Require Import POram.Utils.Tree.
Require Import POram.Utils.Lists.
Require Import POram.Utils.Classes.
Require Import POram.Utils.StateT.
Require Import POram.Utils.Distributions.
(*** PATH ORAM ***)

(** 

  A path ORAM with depth = 2 and bucket size = 3 looks like this:

  CLIENT
2  ↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓

  { ID ↦ PATH, …, ID ↦ PATH } ← POSITION MAP
  {BLOCK, …, BLOCK}           ← STASH

  ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑

  SERVER
  ↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓

                 / [ ID | PAYLOAD ] \
                 | [ ID | PAYLOAD ] |
                 \ [ ID | PAYLOAD ] /
                  /               \
                 /                 \
                /                   \
   / [ ID | PAYLOAD ] \   / [ ID | PAYLOAD ] \  ←
   | [ ID | PAYLOAD ] |   | [ ID | PAYLOAD ] |  ← A BUCKET = N BLOCKS (example: N=3)
   \ [ ID | PAYLOAD ] /   \ [ ID | PAYLOAD ] /  ←
                            ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑  
                          A BLOCK = PAIR of ID and PAYLOAD (encrypted, fixed length, e.g., 64 bits)

   PATH = L (left) or R (right). For depth > 2, PATH = list of L/R (a list of bits) of length = tree depth

   Note: each path is identified by a leaf of the tree

  ↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑↑

  In our model we assume the parameters:
  - tree depth:  notated l
  - bucket size: notated n
  And make some simplifying assumptions:
  - block size = unbounded (PAYLOAD = ℕ)
  - rather than representing data structures using arrays (as a real
    implementation would), we represent directly as inductive data types
  The objects we need to define are then:
  - block_id     ≜ ℕ
  - path         ≜ vector[l](𝔹)
  - position_map ≜ block_id ⇰ path
  - stash        ≜ list(block)
  - bucket       ≜ vector[n](block)
  - oram         ⩴ ⟨bucket⟩ | ⟨bucket | oram ◇ oram⟩
  Note: we will just use association lists to represent dictionaries, e.g., for `block_id ⇰ path`.

 **)

Class Config: Type :=
  {
    LOP : nat;
  }.

Section PORAM.
  Context `{Config}.
  
Definition block_id := nat.
Record block : Type := Block
  { block_blockid : block_id
  ; block_payload : nat
  }.
Definition position_map := dict block_id path.
Definition stash := list block.
Definition bucket := list block.

Definition oram : Type := tree (option bucket).

Record state : Type := State
  { state_position_map : position_map
  ; state_stash : stash
  ; state_oram : oram
  }.

Inductive operation := 
  | Read : operation 
  | Write : nat -> operation.

Definition Poram : Type -> Type :=
  StateT state dist.

Fixpoint lookup_path_oram (o : oram) : path -> list bucket :=
  match o with
  | leaf => fun _ => []
  | node obkt o_l o_r =>
      fun p => 
        match p with
        | [] =>
            match obkt with
            | Some bkt => [bkt]
            | None => []
            end
        | h :: t =>
            match h with
            | true => match obkt with
                     | Some bkt => bkt :: lookup_path_oram o_l t
                     | None => lookup_path_oram o_l t
                     end
            | false => match obkt with
                      | Some bkt => bkt :: lookup_path_oram o_r t
                      | None => lookup_path_oram o_r t
                      end
            end
        end
  end.

Fixpoint clear_path (o : oram ) : path -> oram :=
  match o with
  | leaf => fun _ => leaf
  | node obkt o_l o_r =>
      fun p =>
        match p with
        | [] => node None o_l o_r
        | h :: t =>
            match h with
            | true => node None (clear_path o_l t) o_r
            | false => node None o_l (clear_path o_r t)
            end
        end
  end.

Fixpoint makeBoolList (b : bool) (n : nat) : list bool :=
  match n with
  | O => []
  | S m => b :: makeBoolList b m
  end.

Definition calc_path (id : block_id) (s : state):=
  let l := LOP in 
  lookup_dict (makeBoolList false l) id (state_position_map s).

Definition blk_in_p (id : block_id) (v : nat) (o : oram) (p: path) := 
  let path_blks := concat(lookup_path_oram o p) in
  In (Block id v) path_blks.

Definition blk_in_path (id : block_id) (v : nat) (s : state): Prop :=
  blk_in_p id v (state_oram s) (calc_path id s).

Scheme Equality for list.
Definition isEqvPath (p1 p2 : path) (idx : nat) : bool := list_beq bool Bool.eqb  (takeL idx p1) (takeL idx p2).

Fixpoint get_cand_bs (h : stash)(p : path)(stop : nat)(m : position_map) : list block :=
  match h with
  | [] => []
  | x :: xs =>
      let l := LOP in 
      let rhs_path := lookup_dict (makeBoolList false l) (block_blockid x) m in
      if @isEqvPath p rhs_path stop 
      then x :: get_cand_bs xs p stop m 
      else get_cand_bs xs p stop m 
  end. 

(* n is the capability of each node, the current magic number is 4 based on the original paper *)

Definition get_write_back_blocks (p : path) (h : stash) (n : nat)(lvl : nat) (mp : position_map ) : list block :=
  match (length h) with
  | O => []
  | S m => let cand_bs := get_cand_bs h p lvl mp in
          takeL (Nat.min (length cand_bs) n ) cand_bs
  end.





























End PORAM.
