Require Import Coq.Lists.List.
Import ListNotations.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import Coq.Classes.EquivDec.
Require Import Coq.QArith.QArith.
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


  Scheme Equality for nat.
  
  Fixpoint lookup_ret_data (id : block_id) (lb : list block): nat :=
    match lb with
    | [] => 0
    | h :: t =>
        if Nat.eqb (block_blockid h) id then (block_payload (h%nat))
        else lookup_ret_data id t
    end.

  Definition up_oram_tr (o : oram) (stop : nat) (d_n : bucket)
    (p : path) : oram :=
    update_tree o stop (Some d_n) p.

  Definition block_eqb (b1 b2 : block) : bool :=
    (Nat.eqb (block_blockid b1) (block_blockid b2)) &&
    (Nat.eqb (block_payload b1) (block_payload b2)).
  
  Definition blocks_selection (p : path) (lvl : nat) (s : state ) : state :=
    (* unpack the state *)
    let m := state_position_map s in (* pos_map *) 
    let h := state_stash s in        (* stash *)
    let o := state_oram s in         (* oram tree *)
    let wbs := get_write_back_blocks p h 4 lvl m in (* 4 is the capability of the bucket or equivalently the number of blocks the bucket holds *)
    let up_h := remove_list_sub block_eqb wbs h in 
    let up_o := up_oram_tr o lvl wbs p in
    (State m up_h up_o).

  (* write_back is the last for-loop, searching backwards from the bottom of the tree to seek empty slots to write candidcate blocs back *)

  Fixpoint write_back (s : state) (p : path) (lvl : nat) : state := 
    match lvl with
    | O => s 
    | S m => write_back (blocks_selection p m s) p m
    end.

  Fixpoint iterate_right {X} (start : nat) (p : path) (f : path -> nat -> X -> X) (n : nat) (x : X) : X :=
    match n with
    | O => x
    | S m => f p start (iterate_right (S start) p f m x)
    end.

    Fixpoint get_all_blks_tree (o : oram) : list block :=
    match o with
    | leaf => []
    | node obkt o_l o_r => 
        match obkt with
        | None => get_all_blks_tree o_l ++ get_all_blks_tree o_r
        | Some bkt => bkt ++ (get_all_blks_tree o_l ++ get_all_blks_tree o_r)
        end
    end.

  Definition write_back_r (start : nat) (p : path) (step : nat) (s : state):=
    iterate_right start p blocks_selection step s.

    Definition get_pre_wb_st (id : block_id) (op : operation) (m : position_map) (h : stash ) (o : oram) (p p_new: path) :=
    let m' := update_dict id p_new m in
    let bkts := lookup_path_oram o p in
    let bkt_blocks := concat bkts in
    let h' := bkt_blocks ++ h in
    let h'' := remove_list 
                 (fun blk => (Nat.eqb (block_blockid blk) id)) h' in  
    let h''' :=
      match op with
      | Read => h'
      | Write d => (Block id d) ::  h''
      end in
    let o' := clear_path o p in 
    State m' h''' o'.

  Definition get_post_wb_st (s : state) (id_path : path):=
    write_back_r O id_path (length id_path) s.
  
  Definition get_ret_data (id : block_id)(h : stash)(p : path) (o : oram):=
    let bkts := lookup_path_oram o p in
    let bkt_blocks := concat bkts in
    let h' := bkt_blocks ++ h in
    let ret_data := lookup_ret_data id h' in
    ret_data. 

  Definition access (id : block_id) (op : operation) :
    Poram (path * nat) :=
    PST <- get ;;
    (* unpack the state *)
    let m := state_position_map PST in
    let h := state_stash  PST in
    let o := state_oram PST in 
    (* get path for the index we are querying *)
    let len_m := LOP in
    let p := lookup_dict (makeBoolList false len_m) id m in
    (* flip a bunch of coins to get the new path *)      
    p_new <- liftT (coin_flips len_m) ;;
    (* get the updated path oram state to put and the data to return *)
    let n_st := get_post_wb_st (get_pre_wb_st id op m h o p p_new) p in
    let ret_data := get_ret_data id h p o in
    (* put the updated state back *)
    _ <- put n_st ;;
    (* return the path l and the return value *)
    mreturn((p, ret_data)).

    Record well_formed (s : state ) : Prop := 
    {
      no_dup_stash : NoDup (List.map block_blockid (state_stash s)); 
      no_dup_tree : NoDup (List.map block_blockid (get_all_blks_tree (state_oram s)));
      tree_stash_disj : disjoint_list (List.map block_blockid (get_all_blks_tree (state_oram s)))
                          (List.map block_blockid (state_stash s)); 
      is_pb_tr : is_p_b_tr (state_oram s) (S LOP);
      blk_in_path_in_tree :
      forall id, 
        let m := state_position_map s in
        let p := lookup_dict (makeBoolList false LOP) id m in
        let o := state_oram s in 
        let bkts := lookup_path_oram o p in
        let bkt_blocks := concat bkts in
        In id (List.map block_blockid (get_all_blks_tree o)) ->
        In id (List.map block_blockid bkt_blocks);
      path_length : 
      let m := (state_position_map s) in
      let len_m := LOP in 
      forall id, length(lookup_dict (makeBoolList false len_m) id m) = LOP;
    }.

  Definition read_access (id : block_id) : Poram (path * nat) := access id Read.

  Definition write_access (id : block_id) (v : nat) : Poram (path * nat) :=
    access id (Write v).

  Definition write_and_read_access (id : block_id) (v : nat) : Poram (path * nat) :=
    _ <- write_access id  v;;
    read_access id.

  Definition has_value (v : nat) : (path * nat) -> Prop := fun '(_, val) => v = val.

  Definition get_payload {X} (dist_a : dist (path * X * state)) : X :=
    match peek dist_a with
    | (_, x,_) => x
    end.

  Definition blk_in_stash (id : block_id) (v : nat )(st : state) : Prop :=
    let s := state_stash st in 
    In (Block id v) s.

  (* kv-rel relation should hold whenever we have a write access that has (id, v) into the ORAM.   *)
  Definition kv_rel (id : block_id) (v : nat) (st : state) : Prop :=
    (blk_in_stash id v st) \/ (blk_in_path id v st).
  
  Definition locate_node_in_tr (o : oram) (lvl : nat) (p : path) : option bucket :=
    match lookup_tree o lvl p with
    | None => None
    | Some o => o
    end.

  Definition at_lvl_in_path (o : oram ) (lvl : nat) (p : path) (x : block) : Prop :=
    match locate_node_in_tr o lvl p with
    | None => False
    | Some v => In x v
    end.

  Lemma block_eqb_correct : eqb_correct block_eqb.
  Proof.
    unfold block_eqb.
    intros [id v] [id' v']; simpl.
    split; intro pf.
    - rewrite Bool.andb_true_iff in pf.
      destruct pf.
      rewrite Nat.eqb_eq in *.
      congruence.
    - inversion pf.
      do 2 rewrite Nat.eqb_refl.
      auto.
  Qed.

End PORAM.
