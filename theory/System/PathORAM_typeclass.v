Require Coq.Bool.Bool.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.EquivDec.
Import ListNotations.
(*** CLASSES ***)

(* I'm rolling my own version of lots of datatypes and using typeclasses
 * pervasively. Here are the typeclasses that support the hand-rolled datatype
 * definitions.
 *)
Class Ord (A : Type) := { ord_dec : A -> A -> comparison }.
#[export] Instance NatOrd : Ord nat := { ord_dec := Nat.compare }.

Class Monoid (A : Type) :=
  { null : A
  ; append : A -> A -> A
  }.

Module MonoidNotation.
  Notation "x ++ y " := (append x y) (at level 60, right associativity).
End MonoidNotation.
Import MonoidNotation.

Class Functor (T : Type -> Type) :=
  { map : forall {A B : Type}, (A -> B) -> T A -> T B
  }.

Definition map_on {T : Type -> Type} {A B : Type} `{Functor T} (xT : T A) (f : A -> B) : T B := map f xT.

Class Monad (M : Type -> Type) :=
  { mreturn : forall {A : Type}, A -> M A
  ; mbind   : forall {A B : Type}, M A -> (A -> M B) -> M B
  }.

Module MonadNotation.
  Notation "x <- c1 ;; c2" := (mbind c1 (fun x => c2)) 
    (at level 100, c1 at next level, right associativity).

  Notation "e1 ;; e2" := (_ <- e1 ;; e2)
    (at level 100, right associativity).

  Infix ">>=" := mbind (at level 50, left associativity).
End MonadNotation.
Import MonadNotation.

(* user-defined well-formedness criteria for a datatype, e.g., that a dictionary
 * represented by an association-list has sorted and non-duplicate keys
 *)
Class WF (A : Type) := { wf : A -> Type }.

(* MISSING: correctness criteria, e.g., that `Ord` is an actual total order, etc.
 *)

(*** LISTS ***)

#[export] Instance Functor_list : Functor list := { map := List.map }.
#[export] Instance Monoid_list {A : Type} : Monoid (list A) := { null := nil ; append := @List.app A }.

Fixpoint concat {A : Type} `{Monoid A} (xs : list A) : A :=
  match xs with
  | nil => null
  | cons x xs => x ++ concat xs
  end.

Fixpoint remove_list {A : Type} (x : A) (p : A -> bool) (xs : list A) : A * list A :=
  match xs with
  | [] => (x , xs)
  | x' :: xs' =>
      if p x'
      then (x' , xs')
      else
        let (x'' , xs'') := remove_list x p xs'
        in (x'' , x' :: xs'')
  end.


(*** VECTORS ***)

Definition head_vec {A : Type} {n : nat} (xs : Vector.t A (S n)) : A :=
  match xs with
  | Vector.cons _ x _ _ => x
  end.

Definition tail_vec {A : Type} {n : nat} (xs : Vector.t A (S n)) : Vector.t A n :=
  match xs with
  | Vector.cons _ _ _ xs => xs
  end.

Fixpoint zip_vec {A B : Type} {n : nat} : forall (xs : Vector.t A n) (ys : Vector.t B n), Vector.t (A * B) n :=
  match n with
  | O => fun _ _ => Vector.nil (A * B)
  | S n' => fun xs ys =>
      let x := head_vec xs in
      let xs' := tail_vec xs in
      let y := head_vec ys in
      let ys' := tail_vec ys in
      Vector.cons _ (x , y) _ (zip_vec xs' ys')
  end.

Fixpoint const_vec {A : Type} (x : A) (n : nat) : Vector.t A n :=
  match n with
  | O => Vector.nil A
  | S n' => Vector.cons _ x _ (const_vec x n')
  end.

Fixpoint constm_vec {A : Type} {M : Type -> Type} `{Monad M} (xM : M A) (n : nat) : M (Vector.t A n) :=
  match n with
  | O => mreturn (Vector.nil A)
  | S n' =>
      x <- xM ;;
      xs <- constm_vec xM n' ;;
      mreturn (Vector.cons _ x _ xs)
  end.

Definition to_list_vec {A : Type} {n : nat} := @Vector.to_list A n.
Definition map_vec {A B : Type} {n : nat} f := @Vector.map A B f n.

#[export] Instance Functor_vec {n : nat} : Functor (fun A => Vector.t A n) := { map {_ _} f xs := map_vec f xs }.

(*** RATIONALS ***)
#[export] Instance Monoid_rat : Monoid Q:= { null := 0 / 1 ; append := Qplus}.

(* DICTIONARIES *)

(* Probably switch to `Coq.FSets.FMaps` or `ExtLib.Map.FMapAList` in a real
 * development. Rolling your own is easy enough to do, and if you go this route
 * you may want to enforce well-formedness and/or decideable equality of the key
 * space via type classes.
 *)

Record dict (K V : Type) := Dict { dict_elems : list (K * V) }.
Arguments Dict {K V} _.
Arguments dict_elems {K V} _.

Fixpoint map_alist {K V V' : Type} (f : V -> V') (kvs : list (K * V)) : list (K * V') :=
  match kvs with
  | nil => nil
  | cons (k , v) kvs' => cons (k , f v) (map_alist f kvs')
  end.

Fixpoint lookup_alist {K V : Type} `{Ord K} (v : V) (k : K) (kvs : list (K * V)) :=
  match kvs with
  | nil => v
  | cons (k' , v') kvs' => match ord_dec k k' with
    | Lt => lookup_alist v k kvs'
    | Eq => v'
    | Gt => lookup_alist v k kvs'
    end
  end.

Inductive wf_dict_falist {K V : Type} `{Ord K} : forall (kO : option K) (kvs : list (K * V)), Prop :=
  | nil_WFDict : forall {kO : option K}, wf_dict_falist kO []
  | cons_WFDict : forall {kO : option K} {k : K} {v : V} {kvs : list (K * V)},
      match kO return Set with
      | None => unit
      | Some k' => ord_dec k' k = Lt
      end
      -> wf_dict_falist (Some k) kvs
      -> wf_dict_falist kO ((k , v) :: kvs).

Print wf_dict_falist.

Fixpoint lookup_falist {K V : Type} `{Ord K} (v : V) (k : K) (kvs : list (K * V)) :=
  match kvs with
  | nil => v
  | cons (k' , v') kvs' => match ord_dec k k' with
    | Lt => v
    | Eq => v'
    | Gt => lookup_falist v k kvs'
    end
  end.

Fixpoint update_falist {K V : Type} `{Ord K} (k : K) (v : V) (kvs : list (K * V)) : list (K * V) :=
  match kvs with
  | nil => [ (k , v) ]
  | cons (k' , v') kvs' => match ord_dec k k' with
      | Lt => (k , v) :: (k' , v') :: kvs'
      | Eq => (k , v) :: kvs'
      | Gt => (k' , v') :: update_falist k v kvs'
      end
  end.

#[export] Instance WF_dict {K V : Type} `{Ord K} : WF (dict K V) := { wf kvs := wf_dict_falist None (dict_elems kvs) }.

#[export] Instance Functor_dict {K : Type} : Functor (dict K) :=
  { map {_ _} f kvs := Dict (map_alist f (dict_elems kvs)) }.

Definition lookup_dict {K V : Type} `{Ord K} (v : V) (k : K) (kvs : dict K V) := lookup_falist v k (dict_elems kvs).

Definition update_dict {K V : Type} `{Ord K} (k : K) (v : V) (kvs : dict K V) : dict K V :=
  Dict (update_falist k v (dict_elems kvs)).

(*** DISTRIBUTIONS ***)

(* You may need to just roll your own on this one, and it will be a pain. This
 * representation is mostly just a placeholder. This representation represents
 * the distribution as an association list, so must be a discrete distribution
 * with finite support. We allow multiple keys in the association list (so a
 * multimap) because to restrict otherwise would require an `Ord` restraint on
 * the value type, which makes it more painful to use things like the `Monad`
 * typeclass and notation. Another way to go is to use `dict` instead of a raw
 * association list, which has the dual trade-offs.
 *
 * These are extensional distributions, which make reasoning about conditional
 * probabilities and distribution independence a pain. consider moving to
 * intensional distributions a la the "A Language for Probabilistically
 * Oblivious Computation" paper (Fig 10). 
 *)

Record dist (A : Type) : Type := Dist
  { dist_pmf : list (A * Q)
  }.
Arguments Dist {A} _.
Arguments dist_pmf {A} _.

Definition mreturn_dist {A : Type} (x : A) : dist A := Dist [ (x, 1 / 1) ].

Definition mbind_dist {A B : Type} (xM : dist A) (f : A -> dist B) : dist B :=
  Dist (concat (map_on (dist_pmf xM) (fun (xq : A * Q) => 
    let (x , q) := xq in 
    map_on (dist_pmf (f x)) (fun (yq' : B * Q) => 
      let (y , q') := yq' in
      (y , q ++ q'))))).

#[export] Instance Monad_dist : Monad dist := { mreturn {_} x := mreturn_dist x ; mbind {_ _} := mbind_dist }.

Definition coin_flip : dist bool := Dist [ (true, 1 // 2) ; (false , 1 // 2) ].
(* TODO need a way to express the laws that the distribution needs to obey *)
(* 1. all prob must be greater than 0 *)
Definition getsupp {A} (d: dist A) : list (A * Q) :=
  match d with
  | Dist xs => xs
  end.

Fixpoint fold_l {X Y: Type} (f : X -> Y -> Y) (b : Y)(l : list X) : Y :=
  match l with
  | [] => b
  | h ::t => f h (fold_l f b t)
  end.
      
Definition sum_dist {A} (d: dist A) : Q := fold_l Qplus (0 / 0) (map snd (getsupp d)).


Print map_alist.
Definition norm_dist {A} (d: dist A) : dist A :=
  let supp := dist_pmf d in
  let sum_tot := sum_dist d in
  Dist(map_alist (fun x : Q => x / sum_tot) supp).

Definition event (A : Type) := A -> bool.

(* might collide when you import the List Lib. *)

Fixpoint filter {A} (l: list A) (f: A -> bool): list A :=
  match l with
  | [] => []
  | x :: l => if f x then x::(filter l f) else filter l f 
  end.
Fixpoint map_l {X Y} (f: X -> Y) (l: list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.

Fixpoint length {A} (l : list A) : nat :=
  match l with
    | [] => O
    | _ :: m => S (length m)
  end.

Fixpoint takeL {A} n (l : list A) : list A :=
  match n with
  | O => []
  | S m => match l with
          | [] => []
          | h :: t => h :: takeL m t 
          end
  end.

(* The goal of evalDist is to evaluate the probability when given an event under a certain distribution.      *)

(* 1. get the list -- dist_pmf *)
(* 2. filter a, construct the new list (A, rat) which satisfies event predicate *)
(* 3. reconstruct/repack a dist using this one *)
(* 4. sum it up -- sum_dist *)

 
Fixpoint filter_dist {A} (l: list (A * Q))
  (f: A -> bool): list (A * Q) :=
  match l with
  | [] => []
  | h :: t => 
      match h with
        | pair k v => 
            if f k
            then h :: (filter_dist t f)
            else filter_dist t f
      end
  end.
    
Definition evalDist {A} (x: event A) (d: dist A): Q :=
   sum_dist(Dist(filter_dist (dist_pmf d) x)).

Definition uniform_dist {A} (l: list A) :dist A:=
 norm_dist(Dist(map_l (fun x => (x, 1)) l)).

Fixpoint mk_n_list (n: nat):list nat :=
  match n with
  | O => []
  | S n' => [n'] ++ mk_n_list n'
  end.

Definition coin_flip' := uniform_dist (mk_n_list 2).

(* How to disply the distribution?  *)

Definition cond_dist {A}(p: event A) (d: dist A) : dist A :=
  norm_dist (Dist(filter_dist (dist_pmf d) p)).


(*** PATH ORAM ***)

(** 

  A path ORAM with depth = 2 and bucket size = 3 looks like this:

  CLIENT
  ↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓↓

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

Definition block_id := nat.
Record block : Type := Block
  { block_blockid : block_id
  ; block_payload : nat
  }.
Definition path (l : nat) := Vector.t bool l.
Definition position_map (l : nat) := dict block_id (path l).
Definition stash (n : nat) := list block.
Definition bucket (n : nat) := Vector.t block n.
Inductive oram (n : nat) : forall (l : nat), Type :=
  | Leaf_ORAM : oram n 0
  | Node_ORAM : forall {l : nat}, bucket n -> oram n l -> oram n l -> oram n (S l).
Arguments Leaf_ORAM {n}.
Arguments Node_ORAM {n l} _ _ _.

Definition head_oram {n l : nat} (o : oram n (S l)) : bucket n :=
  match o with
  | Node_ORAM bkt _ _ => bkt
  end.

Definition tail_l_oram {n l : nat} (o : oram n (S l)) : oram n l :=
  match o with
  | Node_ORAM _ o_l _ => o_l
  end.

Definition tail_r_oram {n l : nat} (o : oram n (S l)) : oram n l :=
  match o with
  | Node_ORAM _ _ o_r => o_r
  end.

Record state (n l : nat) : Type := State
  { state_position_map : position_map l
  ; state_stash : stash n
  ; state_oram : oram n l
  }.
Arguments State {n l} _ _ _.
Arguments state_position_map {n l} _.
Arguments state_stash {n l} _.
Arguments state_oram {n l} _.

Fixpoint lookup_path_oram {n l : nat} : forall (p : path l) (o : oram n l), Vector.t (bucket n) l :=
  match l with
  | O => fun _ _ => Vector.nil _
  | S l' => fun p o =>
      let b := head_vec p in
      let p' := tail_vec p in
      let bkt := head_oram o in
      let o_l := tail_l_oram o in
      let o_r := tail_r_oram o in
      Vector.cons _ bkt _ (lookup_path_oram p' (if b then o_l else o_r))
  end.

Inductive operation := 
  | Read : operation 
  | Write : nat -> operation.

Definition dummy_block : block := Block O O.
Definition dummy_path {l : nat} : path l := const_vec false l.


Definition get_cand_bs {n l : nat} (o : oram n l) : list block := []. (* to be implemented *)

(* cap is the capability of each node, the current magic number is 4 based on the original paper *)
Definition get_write_back_blocks {n l : nat} (o : oram n l) (cap : nat)  (h : stash n) (id : nat) : list block :=
  match (length h) with
  | O => []
  | S m => let cand_bs := get_cand_bs o in (* to be implemented *)
          if Nat.leb cap (length(cand_bs))
          then let wbSz := cap in
               takeL cap cand_bs
          else let wbSz := length(cand_bs) in 
               takeL wbSz cand_bs
  end.

Definition remove_list_sub {A} (smL : list A) (p : A -> bool) (toL : list A) : list A := []. (* to be implemented *)

Fixpoint lookup_ret_data (id : block_id) (lb : list block): list nat := [O]. (* to be implemented *)

Definition up_oram_tr {n l : nat} (o : oram n l) (id : block_id) (cand_bs : list block) (lvl : nat) : oram n l := o.
(* to be implemented *)
                                                        
Definition blocks_selection {n l : nat} (id : block_id) (lvl : nat) (*(bc : list block)*) (s : state n l) : state n l :=
  (* unpack the state *)
  let m := state_position_map s in (* pos_map *) 
  let h := state_stash s in        (* stash *)
  let o := state_oram s in         (* oram tree *)
  let wbs := get_write_back_blocks o 4 h id in 
  (* let (pop_bs, up_h) := remove_list_sub wbs  (fun blk => equiv_dec (block_blockid blk) id) h in  *)
  let up_h := remove_list_sub wbs (fun blk => equiv_decb (block_blockid blk) id) h in 
  let up_o := up_oram_tr o id wbs lvl in
  (State m up_h up_o).
                                    
Fixpoint write_back {n l : nat} (s : state n l) (id : block_id) (lvl : nat) : state n l :=
  match lvl with
  | O => blocks_selection id O s
  | S m => write_back (blocks_selection id lvl s) id m
  end.
           
Definition access {n l : nat} (id : block_id) (op : operation) (s : state n l) : dist (path l * list nat * state n l).
refine(
  (* unpack the state *)
  let m := state_position_map s in
  let h := state_stash s in
  let o := state_oram s in
  (* get path for the index we are querying *)
  let p := lookup_dict dummy_path id m in
  (* flip a bunch of coins to get the new path *)
  p_new <- constm_vec coin_flip l;;
  (* update the position map with the new path *)
  let m' := update_dict id p_new m in
  (* read the path for the index from the oram *)
  let bkts := lookup_path_oram p o in
  (* update the stash to include these blocks *)
  let bkt_blocks := concat (map to_list_vec (to_list_vec bkts)) in
  (* look up payload inside the stash *)
  let ret_data := lookup_ret_data id bkt_blocks in 
  let h' := bkt_blocks ++ h in
  (* read the index from the stash *)
  let (blk , h'') := remove_list dummy_block (fun blk => equiv_decb (block_blockid blk) id) h' in
  (* write new data to the stash *)
  let h''' := 
    match op with
    | Read => h'
    | Write d => [Block id d] ++ h''
    end in
  let n_st := write_back (State m' h''' o) id l in
  (* return the path we queried, the data we read from the ORAM, and the next system state *)
  mreturn_dist (p, ret_data , n_st)
  ) ; try typeclasses eauto.
Defined.

(* Definition state_lift {S X} (Pre Post : S -> Prop) *)
(*   (P : X -> Prop) : State S X -> Prop := *)
(*   fun f => forall s, Pre s -> *)
(*     P (fst (f s)) /\ Post (snd (f s)). *)

Definition well_formed {n l : nat } (s : state n l) : Prop := True. (* placeholder for invariant of the state *)

Definition get_payload {A B C Q} (al : list (A * B * C * Q)) : option B :=
  match al with
  | [] => None
  | h :: t => match h with
            | (((a, b), c), q) => Some b 
            end
  end.


Definition get_oram_st (A B C Q: Type) (al : list (A * B * C * Q)) : option C :=
  match al with
  | [] => None
  | h :: t => match h with
            | (((a, b), c), q) => Some c 
            end
  end.
Arguments get_oram_st {A B C Q}.

Class PredLift M `{Monad M} := {
  plift {X} : (X -> Prop) -> M X -> Prop;
  lift_ret {X} : forall x (P : X -> Prop), P x -> plift P (mreturn x);
  lift_bind {X Y} : forall (P : X -> Prop) (Q : Y -> Prop)
    (mx : M X) (f : X -> M Y), plift P mx ->
    (forall x, P x -> plift Q (f x)) ->
    plift Q (mbind mx f)
  }.


Definition state_prob_lift {S} {M} `{Monad M} `{PredLift M} {X} (Pre Post : S -> Prop) (P : X -> Prop) :=
  fun mx =>
    forall s, Pre s -> plift (fun '(x, s') => P x /\ Post s') (mx s). 

Definition state_m {n l: nat}: Type := state n l.

Definition read_access {n l : nat} (id : block_id) (s : state n l) : dist (path l * list nat * state n l) := access id Read s.

Definition write_access {n l: nat} (id : block_id) (v : nat)(s : state n l) : dist (path l * list nat * state n l) := access id (Write v) s.

Definition write_and_read_acces {n l v: nat} (id : block_id) (s : state n l) : dist (path l * list nat * state n l) := Dist [ (dummy_path, [1%nat] , s, 1 / 1) ].
  (* mbind_dist (write_access id v s) (fun st => read_access id (get_oram_st [st])). *)


  
Theorem PathORAM_simulates_RAM {n l : nat} (id : block_id) (v : nat) (s : state n l) :
  well_formed s ->
  forall (s' : state n l), 
    get_oram_st(getsupp (access id (Write v) s )) = Some s' -> 
    get_payload(getsupp (access id Read s')) = Some [v].

Proof.
Admitted.
