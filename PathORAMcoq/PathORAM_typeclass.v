Require Coq.Bool.Bool.
(* Require Import FCF.FCF. *)
(*** CLASSES ***)

(* I'm rolling my own version of lots of datatypes and using typeclasses
 * pervasively. Here are the typeclasses that support the hand-rolled datatype
 * definitions.
 *)

Inductive ord := 
  | LT : ord 
  | EQ : ord 
  | GT : ord.

Class Eq (A : Type) := { eq_dec : A -> A -> bool }.

#[export] Instance Eq_bool : Eq bool := { eq_dec := Coq.Bool.Bool.eqb }.
#[export] Instance Eq_nat : Eq nat := { eq_dec := Coq.Init.Nat.eqb }.

Class Ord (A : Type) := { ord_dec : A -> A -> ord }.

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

(* MISSING: correctness criteria, e.g., that `Eq` is an actual equivalence
 * relation, that `Ord` is an actual total order, etc.
 *)

(*** OPTIONS ***)

(* Probably switch to using `option` from base Coq in a real development.
 * Rolling your own is easy enough to do ; nothing wrong with doing that either.
*)

Inductive option (A : Type) : Type :=
  | None : option A
  | Some : A -> option A.
Arguments None {A}.
Arguments Some {A} _.

(*** LISTS ***)

(* Probably switch to using Coq.Lists.List in a real development. Rolling
 * your own is easy enough to do; nothing wrong with doing that either. 
 *)
(* Require Import Coq.Lists.List. *)

Inductive list (A : Type) : Type :=
  | Nil : list A
  | Cons : A -> list A -> list A.
Arguments Nil {A}.
Arguments Cons {A} _ _.

Module ListNotation.
  Infix "::" := Cons.
  Print "::".
  Notation "[ ]" := Nil.
  Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).
End ListNotation.
Import ListNotation.

Fixpoint map_list {A B : Type} (f : A -> B) (xs : list A) : list B :=
  match xs with
  | Nil => Nil
  | Cons x xs => Cons (f x) (map_list f xs)
  end.

#[export] Instance Functor_list : Functor list := { map := @map_list }.

Fixpoint append_list {A : Type} (xs ys : list A) : list A :=
  match xs with
  | Nil => ys
  | Cons x xs' => Cons x (append_list xs' ys)
  end.

#[export] Instance Monoid_list {A : Type} : Monoid (list A) := { null := Nil ; append := append_list }.

Fixpoint concat {A : Type} `{Monoid A} (xs : list A) : A :=
  match xs with
  | Nil => null
  | Cons x xs => x ++ concat xs
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

(* Probably switch to either `Coq.Vectors.Vector` or `ExtLib.Data.Fin` in a real
 * development. Rolling your own is easy enough to do; nothign wrong with doing
 * that either.
 *)
(* Require Import Coq.Vectors.Vector. *)

Inductive vec (A : Type) : forall (n : nat), Type :=
  | Nil_V : vec A 0
  | Cons_V : forall (n : nat), A -> vec A n -> vec A (S n).
Arguments Nil_V {A}.
Arguments Cons_V {A n} _ _.

Definition head_vec {A : Type} {n : nat} (xs : vec A (S n)) : A :=
  match xs with
  | Cons_V x _ => x
  end.

Definition tail_vec {A : Type} {n : nat} (xs : vec A (S n)) : vec A n :=
  match xs with
  | Cons_V _ xs => xs
  end.

Fixpoint zip_vec {A B : Type} {n : nat} : forall (xs : vec A n) (ys : vec B n), vec (A * B) n :=
  match n with
  | O => fun _ _ => Nil_V
  | S n' => fun xs ys =>
      let x := head_vec xs in
      let xs' := tail_vec xs in
      let y := head_vec ys in
      let ys' := tail_vec ys in
      Cons_V (x , y) (zip_vec xs' ys')
  end.

Fixpoint const_vec {A : Type} (x : A) (n : nat) : vec A n :=
  match n with
  | O => Nil_V
  | S n' => Cons_V x (const_vec x n')
  end.

Fixpoint constm_vec {A : Type} {M : Type -> Type} `{Monad M} (xM : M A) (n : nat) : M (vec A n) :=
  match n with
  | O => mreturn Nil_V
  | S n' =>
      x <- xM ;;
      xs <- constm_vec xM n' ;;
      mreturn (Cons_V x xs)
  end.

Fixpoint to_list_vec {A : Type} {n : nat} (xs : vec A n) : list A :=
  match xs with
  | Nil_V => []
  | Cons_V x xs' => x :: to_list_vec xs'
  end.

Fixpoint map_vec {A B : Type} {n : nat} (f : A -> B) (xs : vec A n) : vec B n :=
  match xs with
  | Nil_V => Nil_V
  | Cons_V x xs' => Cons_V (f x) (map_vec f xs')
  end.

#[export] Instance Functor_vec {n : nat} : Functor (fun A => vec A n) := { map {_ _} f xs := map_vec f xs }.

(*** RATIONALS ***)

(* Probably switch to `Coq.QArith.QArith` in a real development. If you're going
 * to roll your own, make sure you include a proof in the representation that
 * `ratNum` and `ratDen` are greatest-common-denominator-reduced so that
 * semantically equal rationals are syntactically equal (i.e., equal via `=`).
 *)
(* Require Import Coq.QArith.QArith. *)

Record rat : Type := Rat
  { rat_num : nat
  ; rat_den : nat
  }.

Definition divide_nat_rat (q1 q2 : nat) : rat := Rat q1 q2.

Module RatNotation.
  Infix "//" := divide_nat_rat (at level 40, left associativity).
End RatNotation.
Import RatNotation.

Definition plus_rat : rat -> rat -> rat. Admitted.

#[export] Instance Monoid_rat : Monoid rat := { null := 0 // 1 ; append := plus_rat }.

(*** DICTIONARIES ***)

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
  | Nil => Nil
  | Cons (k , v) kvs' => Cons (k , f v) (map_alist f kvs')
  end.

Fixpoint lookup_alist {K V : Type} `{Ord K} (v : V) (k : K) (kvs : list (K * V)) :=
  match kvs with
  | Nil => v
  | Cons (k' , v') kvs' => match ord_dec k k' with
    | LT => lookup_alist v k kvs'
    | EQ => v'
    | GT => lookup_alist v k kvs'
    end
  end.

Inductive wf_dict_falist {K V : Type} `{Ord K} : forall (kO : option K) (kvs : list (K * V)), Prop :=
  | Nil_WFDict : forall {kO : option K}, wf_dict_falist kO []
  | Cons_WFDict : forall {kO : option K} {k : K} {v : V} {kvs : list (K * V)},
      match kO with
      | None => unit
      | Some k' => ord_dec k' k = LT
      end
      -> wf_dict_falist (Some k) kvs
      -> wf_dict_falist kO ((k , v) :: kvs).

Fixpoint lookup_falist {K V : Type} `{Ord K} (v : V) (k : K) (kvs : list (K * V)) :=
  match kvs with
  | Nil => v
  | Cons (k' , v') kvs' => match ord_dec k k' with
    | LT => v
    | EQ => v'
    | GT => lookup_falist v k kvs'
    end
  end.

Fixpoint update_falist {K V : Type} `{Ord K} (k : K) (v : V) (kvs : list (K * V)) : list (K * V) :=
  match kvs with
  | Nil => [ (k , v) ]
  | Cons (k' , v') kvs' => match ord_dec k k' with
      | LT => (k , v) :: (k' , v') :: kvs'
      | EQ => (k , v) :: kvs'
      | GT => (k' , v') :: update_falist k v kvs'
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
 * probabilities and distribution independence a pain. Consider moving to
 * intensional distributions a la the "A Language for Probabilistically
 * Oblivious Computation" paper (Fig 10). 
 *)

Record dist (A : Type) : Type := Dist
  { dist_pmf : list (A * rat)
  }.
Arguments Dist {A} _.
Arguments dist_pmf {A} _.

Definition mreturn_dist {A : Type} (x : A) : dist A := Dist [ (x, 1 // 1) ].

Definition mbind_dist {A B : Type} (xM : dist A) (f : A -> dist B) : dist B :=
  Dist (concat (map_on (dist_pmf xM) (fun (xq : A * rat) => 
    let (x , q) := xq in 
    map_on (dist_pmf (f x)) (fun (yq' : B * rat) => 
      let (y , q') := yq' in
      (y , q ++ q'))))).

#[export] Instance Monad_dist : Monad dist := { mreturn {_} x := mreturn_dist x ; mbind {_ _} := mbind_dist }.

Definition coin_flip : dist bool := Dist [ (true, 1 // 2) ; (false , 1 // 2) ].
(* TODO need a way to express the laws that the distribution needs to obey *)
(* 1. all prob must be greater than 0 *)
Definition getsupp {A} (d: dist A) : list (A * rat) :=
  match d with
  | Dist xs => xs
  end.

Fixpoint fold_l {X Y: Type} (f : X -> Y -> Y) (b : Y)(l : list X) : Y :=
  match l with
  | [] => b
  | h ::t => f h (fold_l f b t)
  end.
      
Definition sum_dist {A} (d: dist A) : rat := fold_l plus_rat (O // O) (map snd (getsupp d)).


(* How to create a rat using something like rat // nat?  *)
(* Definition norm_dist {A} (d: dist A) : dist A := *)
(*   let supp := getsupp d in *)
(*   let sum_tot := sum_dist d in *)
(*   concat (map_on supp (fun (x : rat) => ( x // sum_tot))). *)

Definition event (A : Type) := A -> bool.

(* might collide when you import the List Lib. *)

Fixpoint filter {A} (l: list A) (f: A -> bool): list A :=
  match l with
  | [] => []
  | x :: l => if f x then x::(filter l f) else filter l f 
  end.

(* The goal of evalDist is to evaluate the probability when given an event under a certain distribution.      *)

(* 1. get the list -- dist_pmf *)
(* 2. filter a, construct the new list (A, rat) which satisfies event predicate *)
(* 3. reconstruct/repack a dist using this one *)
(* 4. sum it up -- sum_dist *)

 
Fixpoint filter_dist {A} (l: list (A * rat))
  (f: A -> bool): list (A * rat) :=
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
    
Definition evalDist {A} (x : event A) (d : dist A) : rat :=
   sum_dist(Dist(filter_dist (dist_pmf d) x)).








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
Definition path (l : nat) := vec bool l.
Definition position_map (l : nat) := dict block_id (path l).
Definition stash (n : nat) := list block.
Definition bucket (n : nat) := vec block n.
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

Fixpoint lookup_path_oram {n l : nat} : forall (p : path l) (o : oram n l), vec (bucket n) l :=
  match l with
  | O => fun _ _ => Nil_V
  | S l' => fun p o =>
      let b := head_vec p in
      let p' := tail_vec p in
      let bkt := head_oram o in
      let o_l := tail_l_oram o in
      let o_r := tail_r_oram o in
      Cons_V bkt (lookup_path_oram p' (if b then o_l else o_r))
  end.

Inductive operation := 
  | Read : operation 
  | Write : nat -> operation.

Definition dummy_block : block := Block 0 0.
Definition dummy_path {l : nat} : path l := const_vec false l.

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
  let h' := bkt_blocks ++ h in
  (* read the index from the stash *)
  let (blk , h'') := remove_list dummy_block (fun blk => eq_dec (block_blockid blk) id) h' in
  (* write new data to the stash *)
  let h''' := 
    match op with
    | Read => h''
    | Write d => [Block id d] ++ h''
    end in
  (* update the oram with data along path `p` using data from (and updating) stash `h'''` *)
  (* TODO *)
  (* return the path we queried, the data we read from the ORAM, and the next
   * system state 
   *)
  (* TODO *)
   _
) ; try typeclasses eauto.
Abort.

