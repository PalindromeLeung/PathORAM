Require Import Coq.Lists.List.
Import ListNotations.
Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import Coq.Classes.EquivDec.
Require Import Coq.QArith.QArith.
Require Import POram.Utils.Dictionary.
Require Import POram.Utils.Tree.
Require Import POram.Utils.Fin.
Require Import POram.Utils.Vec.
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

  (* TODO: better name *)
  Definition Path := path LOP.
  Definition position_map := dict block_id Path.
  Definition stash := list block.
  Definition bucket := list block.

  Definition oram : Type := pb_tree (S LOP) (option bucket).
  Definition level : Type := Fin (S LOP).

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

  (* TODO: move to Tree.v *)
  Fixpoint lookup_path {X} {n} : pb_tree (S n) X -> path n -> list X :=
    match n with
    | 0%nat => fun t p =>
      match t with
      | (x, _, _) => [x]
      end
    | S m => fun t p =>
      match t with
      | (x, t_l, t_r) =>
        match p with
        | (true, p') => x :: lookup_path t_l p'
        | (false, p') => x :: lookup_path t_r p'
        end
      end
    end.

  (* TODO: move to Lists.v *)
  Fixpoint filter_Some {X} (l : list (option X)) : list X :=
    match l with
    | [] => []
    | Some x :: l' => x :: filter_Some l'
    | None :: l' => filter_Some l'
    end.

  Lemma filter_Some_correct {X} (l : list (option X)) : forall x,
    In x (filter_Some l) <-> In (Some x) l.
  Proof.
    intro x; split; intro pf.
    - induction l as [|o l'].
      + destruct pf.
      + destruct o as [x'|].
        * destruct pf.
          -- left; congruence.
          -- right; auto.
        * right; auto.
  - induction l as [|o l'].
    + destruct pf.
    + destruct pf.
      * subst.
        left; reflexivity.
      * destruct o.
        -- right; auto.
        -- auto.
  Qed.

  Definition lookup_path_oram (o : oram) (p : Path) : list bucket :=
    filter_Some (lookup_path o p).

  (* TODO: move to Tree.v *)
  Fixpoint write_on_path {X} {n} : X -> pb_tree (S n) X -> path n -> pb_tree (S n) X :=
    match n with
    | 0%nat => fun x t p =>
      match t with
      | (_, t_l, t_r) => (x, t_l, t_r)
      end
    | S m => fun x t p =>
      match t with
      | (_, t_l, t_r) =>
        match p with
        | (true, p') => (x, write_on_path x t_l p', t_r)
        | (false, p') => (x, t_l, write_on_path x t_r p')
        end
      end
    end.

  Definition clear_path : oram -> Path -> oram :=
    write_on_path None.

  (* TODO: move to vec.v *)
  Fixpoint vec_replicate {X} n (x : X) : vec n X :=
    match n with
    | 0%nat => tt
    | S m => (x, vec_replicate m x)
    end.

  Definition default_path : Path :=
    vec_replicate LOP false.

  Definition calc_path (id : block_id) (s : state):=
    lookup_dict default_path id (state_position_map s).

  Definition blk_in_p (id : block_id) (v : nat) (o : oram) (p: Path) := 
    let path_blks := concat(lookup_path_oram o p) in
    In (Block id v) path_blks.

  Definition blk_in_path (id : block_id) (v : nat) (s : state): Prop :=
    blk_in_p id v (state_oram s) (calc_path id s).

  Fixpoint equiv_up_to {n} : path n -> path n -> Fin (S n) -> bool :=
    match n with
    | 0%nat => fun _ _ _ => true
    | S m => fun p1 p2 i =>
      match i with
      | inl _ => true
      | inr j =>
        match p1, p2 with
        | (b1, p1'), (b2, p2') => Bool.eqb b1 b2 && equiv_up_to p1' p2' j
        end
      end
    end.

  Definition isEqvPath (p1 p2 : Path) (idx : level) : bool :=
    equiv_up_to p1 p2 idx.

  Fixpoint get_cand_bs (h : stash)(p : Path)(stop : level)(m : position_map) : list block :=
    match h with
    | [] => []
    | x :: xs =>
        let l := LOP in 
        let rhs_path := lookup_dict default_path (block_blockid x) m in
        if @isEqvPath p rhs_path stop 
        then x :: get_cand_bs xs p stop m 
        else get_cand_bs xs p stop m 
    end. 

  (* n is the capability of each node, the current magic number is 4 based on the original paper *)

  Definition get_write_back_blocks (p : Path) (h : stash) (n : nat)(lvl : level) (mp : position_map ) : list block :=
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

  Definition up_oram_tr (o : oram) (stop : level) (d_n : bucket)
    (p : Path) : oram :=
    update_tree o stop (Some d_n) p.

  Definition block_eqb (b1 b2 : block) : bool :=
    (Nat.eqb (block_blockid b1) (block_blockid b2)) &&
    (Nat.eqb (block_payload b1) (block_payload b2)).
  
  Definition blocks_selection (p : Path) (lvl : level) (s : state ) : state :=
    (* unpack the state *)
    let m := state_position_map s in (* pos_map *) 
    let h := state_stash s in        (* stash *)
    let o := state_oram s in         (* oram tree *)
    let wbs := get_write_back_blocks p h 4 lvl m in (* 4 is the capability of the bucket or equivalently the number of blocks the bucket holds *)
    let up_h := remove_list_sub block_eqb wbs h in 
    let up_o := up_oram_tr o lvl wbs p in
    (State m up_h up_o).

  (* TODO: Tree.v *)
  Fixpoint flatten_pb_tree {X} {n} : pb_tree n X -> list X :=
    match n with
    | 0%nat => fun _ => []
    | S m => fun t =>
      match t with
      | (x, t_l, t_r) => x :: flatten_pb_tree t_l ++ flatten_pb_tree t_r
      end
    end.

  Definition get_all_blks_tree (o : oram) : list block :=
    concat (filter_Some (flatten_pb_tree o)).

  Definition write_back_r (p : Path) (s : state):=
    Fin_iterate (blocks_selection p) s.

  Definition get_pre_wb_st (id : block_id) (op : operation) (m : position_map) (h : stash ) (o : oram) (p p_new: Path) :=
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

  Definition get_post_wb_st (s : state) (id_path : Path):=
    write_back_r id_path s.

  Definition get_ret_data (id : block_id)(h : stash)(p : Path) (o : oram):=
    let bkts := lookup_path_oram o p in
    let bkt_blocks := concat bkts in
    let h' := bkt_blocks ++ h in
    let ret_data := lookup_ret_data id h' in
    ret_data.

  Definition access (id : block_id) (op : operation) :
    Poram (Path * nat) :=
    PST <- get ;;
    (* unpack the state *)
    let m := state_position_map PST in
    let h := state_stash  PST in
    let o := state_oram PST in 
    (* get path for the index we are querying *)
    let p := lookup_dict default_path id m in
    (* flip a bunch of coins to get the new path *)      
    p_new <- liftT (coin_flips LOP) ;;
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
      blk_in_path_in_tree :
      forall id, 
        let m := state_position_map s in
        let p := lookup_dict default_path id m in
        let o := state_oram s in 
        let bkts := lookup_path_oram o p in
        let bkt_blocks := concat bkts in
        In id (List.map block_blockid (get_all_blks_tree o)) ->
        In id (List.map block_blockid bkt_blocks);
    }.

  Definition read_access (id : block_id) : Poram (Path * nat) := access id Read.

  Definition write_access (id : block_id) (v : nat) : Poram (Path * nat) :=
    access id (Write v).

  Definition write_and_read_access (id : block_id) (v : nat) : Poram (Path * nat) :=
    _ <- write_access id  v;;
    read_access id.

  Definition has_value (v : nat) : (Path * nat) -> Prop := fun '(_, val) => v = val.

  Definition get_payload {X} (dist_a : dist (Path * X * state)) : X :=
    match peek dist_a with
    | (_, x,_) => x
    end.

  Definition blk_in_stash (id : block_id) (v : nat )(st : state) : Prop :=
    let s := state_stash st in 
    In (Block id v) s.

  Definition blk_in_state (id : block_id) (v : nat) (st : state) : Prop :=
    blk_in_stash id v st \/ blk_in_path id v st.

  Definition undef k s :=
    ~ exists v, blk_in_state k v s.

  Definition locate_node_in_tr (o : oram) (lvl : level) (p : Path) : option bucket :=
    lookup_tree o lvl p.

  Definition at_lvl_in_path (o : oram ) (lvl : level) (p : Path) (x : block) : Prop :=
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
