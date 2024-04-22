Require Coq.Bool.Bool.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.Classes.EquivDec.
Import ListNotations.
Require Import Coq.Program.Equality.
Require Import Lia.
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

(* #[export] Instance Functor_list : Functor list := { map := List.map }. *)
#[export] Instance Monoid_list {A : Type} : Monoid (list A) := { null := nil ; append := @List.app A }.

Fixpoint remove_list {A : Type} (x : A) (p : A -> bool) (xs : list A) : list A :=
  match xs with
  | [] => xs
  | x' :: xs' =>
      if p x'
      then xs'
      else
        x' :: remove_list x p xs'
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

Fixpoint constm_vec {A : Type} {M : Type -> Type} `{Monad M} (xM : M A) (n : nat) : M (list A) :=
  match n with
  | O => mreturn (@nil A)
  | S n' =>
      x <- xM ;;
      xs <- constm_vec xM n' ;;
      mreturn (cons x xs)
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
  Dist (concat (List.map (fun (xq : A * Q) => 
    let (x , q) := xq in 
    List.map (fun (yq' : B * Q) => 
           let (y , q') := yq' in
           (y , q ++ q')) (dist_pmf (f x))) (dist_pmf xM))).

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
      
Definition sum_dist {A} (d: dist A) : Q := fold_l Qplus (0 / 0) (List.map snd (getsupp d)).


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
  | h :: t => (f h) :: (List.map f t)
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
Definition path := list bool.
Definition position_map := dict block_id path.
Definition stash := list block.
Definition bucket := list block.

Inductive oram : Type :=
| leaf
| node (payload: option bucket) (o_l o_r : oram). 

Fixpoint bound_pred (o : oram) (n : nat) : Prop :=
  match o with 
  | leaf => True
  | node obkt g_l g_r =>
      match obkt with
      | Some bkt => (Nat.le (List.length bkt) n) /\ bound_pred g_l n /\ bound_pred g_r n
      | None => bound_pred g_l n /\ bound_pred g_r n
      end
  end.   

Definition Poram_st S M A : Type := S -> M (A * S)%type.

Definition retT {S} {M} `{Monad M} {X} :
  X -> Poram_st S M X :=
  fun x s => mreturn (x, s).

Definition bindT {S} {M} `{Monad M} {X Y} :
  Poram_st S M X ->
  (X -> Poram_st S M Y) ->
  Poram_st S M Y.
Proof.
  unfold Poram_st.
  intros mx f s.
  apply (mbind (mx s)).
  intros [x s'].
  exact (f x s').
Defined.

Definition head_oram (o : oram) : option (list block) :=
  match o with
  | leaf => None
  | node obkt _ _ => obkt
  end.

Definition tail_l_oram (o : oram) : oram :=
  match o with
  | leaf => leaf
  | node  _ o_l _ => o_l
  end.

Definition tail_r_oram (o : oram) : oram :=
  match o with
  | leaf => leaf
  | node _ _ o_r => o_r
  end.

Record state : Type := State
  { state_position_map : position_map
  ; state_stash : stash
  ; state_oram : oram
  }.
  
Definition Poram_st_get {S M} `{Monad M}: Poram_st S M S :=
  fun s => mreturn(s,s). 

Definition Poram_st_put {S M} `{Monad M} (st : S) :
  Poram_st S M unit := fun s => mreturn(tt, st).

Fixpoint get_height (o : oram) : nat :=
  match o with
  | leaf => 0
  | node  _ l r => S (max (get_height l) (get_height r))
  end.


Fixpoint is_p_b_tr (o : oram) : Prop :=
  match o with
  | leaf => True
  | node _ l r => get_height l = get_height r
                 /\ (is_p_b_tr l) /\( is_p_b_tr r)
  end.    

Fixpoint lookup_path_oram (o : oram) : path -> list bucket :=
  match o with
  | leaf => fun _ => []
  | node obkt o_l o_r =>
      fun p => 
        match p with
        | [] => []
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
        | [] => o
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
  let l := length (dict_elems (state_position_map s)) in
  lookup_dict (makeBoolList false l) id (state_position_map s).

Definition blk_in_p (id : block_id) (v : nat) (o : oram) (p: path) := 
  let path_blks := concat(lookup_path_oram o p) in
  In (Block id v) path_blks.

Definition blk_in_path (id : block_id) (v : nat) (s : state): Prop :=
  blk_in_p id v (state_oram s) (calc_path id s).

#[global] Instance PoramM {S M } `{Monad M} : Monad (Poram_st S M) :=
  {|mreturn A := retT; mbind X Y := bindT |}.

Definition get_State : Poram_st(state) dist(state) := Poram_st_get.

Inductive operation := 
  | Read : operation 
  | Write : nat -> operation.

Scheme Equality for list.
Scheme Equality for prod.

Print list_beq.

Definition isEqvPath (p1 p2 : path) (idx : nat) : bool := list_beq bool Bool.eqb  (takeL idx p1) (takeL idx p2).
  


Definition dummy_block : block := Block O O.

Fixpoint get_cand_bs (h : stash)(p : path)(stop : nat)(m : position_map) : list block :=
  match h with
  | [] => []
  | x :: xs =>
      let l := length (dict_elems m) in 
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

Fixpoint remove_aux (lst : list block) (x : block) : list block :=
  match lst with
  | [] => []
  | h :: t => 
      if andb (Nat.eqb (block_blockid h) (block_blockid x))
           (Nat.eqb (block_payload h) (block_payload x))
      then t 
      else h :: (remove_aux t x)
  end.

Fixpoint remove_list_sub (sublist : list block) (lst : list block) : list block :=
    match sublist with
    | [] => lst
    | h :: t => remove_list_sub t (remove_aux lst h)
    end.
                 
Fixpoint lookup_ret_data (id : block_id) (lb : list block): nat :=
  match lb with
  | [] => 0
  | h :: t =>
      if Nat.eqb (block_blockid h) id then block_payload (h%nat)
      else lookup_ret_data id t
  end.

Fixpoint up_oram_tr (o : oram) (stop : nat) (d_n : bucket) :
  path -> oram :=
  match o in oram return path -> oram with
  | leaf => fun _ => leaf
  | node d_o o_l o_r =>
      fun p =>
        match stop with
        | O => node (Some d_n) o_l o_r
        | S stop' =>
            match p with
            | [] => node d_o o_l o_r
            | x :: xs =>
                match x with
                | true => node d_o (up_oram_tr o_l stop' d_n xs ) o_r
                | false => node d_o o_l(up_oram_tr o_r stop' d_n xs)
                end
            end
        end
  end.
             
(* --- BEGIN Talia's equivalent definition of nth to reuse later --- *)
Fixpoint nth_error_opt {A : Type} {m : nat} (v : Vector.t A m) (n : nat) : option A :=
  match n with
  | O =>
    match v with
    | Vector.nil _ => None
    | Vector.cons _ h _ _ => Some h
    end
  | S p =>
    match v with
    | Vector.nil _ => None
    | Vector.cons _ _ n1 t0 => nth_error_opt t0 p
    end
  end.

Lemma nth_error_opt_some:
  forall {A : Type} {m : nat} (v : Vector.t A m) (n : nat) (a : A),
    nth_error_opt v n = Some a -> Nat.lt n m.
Proof.
  intros A m v n. revert A m v.
  induction n; destruct v; intros; inversion H.
  - auto with arith.
  - specialize (IHn A n0 v a H1). auto with arith.
Qed.

Lemma fin_of_lt_irrel:
  forall {m n : nat} (H1 H2 : Nat.lt n m), Fin.of_nat_lt H1 = Fin.of_nat_lt H2.
Proof.
  induction m; destruct n; intros; auto.
  - inversion H1.
  - inversion H1.
  - simpl. f_equal. apply IHm.
Qed.

Lemma nth_error_OK:
  forall {A : Type} {m : nat} (v : Vector.t A m) (n : nat) (a : A) (H : nth_error_opt v n = Some a),
    nth_order v (nth_error_opt_some v n a H) = a.
Proof.
  intros A m v n. revert A m v. induction n; destruct v; intros; inversion H.
  - subst. reflexivity.
  - specialize (IHn A n0 v a H).
    unfold nth_order in *. simpl in *. rewrite <- IHn. 
    f_equal. apply fin_of_lt_irrel.
Qed.
(* --- END Talia's equivalent definition of nth to reuse later --- *)

Definition blocks_selection (p : path) (lvl : nat) (s : state ) : state :=
  (* unpack the state *)
  let m := state_position_map s in (* pos_map *) 
  let h := state_stash s in        (* stash *)
  let o := state_oram s in         (* oram tree *)
  let wbs := get_write_back_blocks p h 4 lvl m in (* 4 is the capability of the bucket or equivalently the number of blocks the bucket holds *)
  let up_h := remove_list_sub wbs h in 
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

Definition write_back_r (start : nat) (p : path) (step : nat) (s : state):=
  iterate_right start p blocks_selection step s.
                        
Lemma iterate_right_split {X} n : forall (start k : nat) (f : path -> nat -> X -> X) (p : path) (x : X),
  iterate_right start p f (n+k) x =
  iterate_right start p f n
  (iterate_right (n + start) p f k x).
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite plus_n_Sm.
    reflexivity.
Qed.

Lemma factor_lemma {X} (L k : nat) (p : path) (f : path -> nat -> X -> X) (x : X) : (k < L)%nat ->
  iterate_right 0 p f L x =
    iterate_right 0 p f k
      (f p k
         (iterate_right (S k) p f (L - 1 - k) x)
      ).
Proof.
  intro.
  assert (L = k + S ((L - 1) - k))%nat by lia.
  rewrite H0 at 1.
  rewrite iterate_right_split.
  rewrite <- (plus_n_O).
  simpl.
  reflexivity. 
Qed.


Definition dist2Poram {S X} (dx : dist X) : Poram_st S dist X :=
  fun st =>
    a <- dx ;; mreturn (a, st).

Fixpoint concat_option (l : list (option bucket)) : list block :=
  match l with
  | [] => []
  | h :: t => match h with
            | None => concat_option t
            | Some v => v ++ concat_option t
            end
  end.

Definition get_pre_wb_st (id : block_id) (op : operation) (m : position_map) (h : stash ) (o : oram) (p p_new: path) :=
  let m' := update_dict id p_new m in
  let bkts := lookup_path_oram o p in
  let bkt_blocks := concat bkts in
  let h' := bkt_blocks ++ h in
  let h'' := remove_list dummy_block 
               (fun blk => equiv_decb (block_blockid blk) id) h' in  
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
  Poram_st state dist (path * nat) :=
  PST <- get_State ;;
  (* unpack the state *)
  let m := state_position_map PST in
  let h := state_stash  PST in
  let o := state_oram PST in 
  (* get path for the index we are querying *)
  let len_m := length (dict_elems m) in 
  let p := lookup_dict (makeBoolList false len_m) id m in
  (* flip a bunch of coins to get the new path *)      
  p_new <- dist2Poram (constm_vec coin_flip len_m) ;;
  (* get the updated path oram state to put and the data to return *)
  let n_st := get_post_wb_st (get_pre_wb_st id op m h o p p_new) p in
  let ret_data := get_ret_data id h p o in
  (* put the updated state back *)
  _ <- Poram_st_put n_st ;;
  (* return the path l and the return value *)
  mreturn((p, ret_data)).

Definition well_formed (s : state ) : Prop := True. (* placeholder for invariant of the state *)

Class PredLift M `{Monad M} := {
  plift {X} : (X -> Prop) -> M X -> Prop;
  lift_ret {X} : forall x (P : X -> Prop), P x -> plift P (mreturn x);
  lift_bind {X Y} : forall (P : X -> Prop) (Q : Y -> Prop)
    (mx : M X) (f : X -> M Y), plift P mx ->
    (forall x, P x -> plift Q (f x)) ->
    plift Q (mbind mx f)
  }.

(* WARNING: distribution should contain non-zero weighted support *)
Definition dist_lift {X} (P : X -> Prop) (d : dist X) : Prop.
Proof.   
  destruct d.
  eapply (Forall P (List.map fst dist_pmf0)).
Defined.

#[export] Instance Pred_Dist_Lift : PredLift dist.
refine 
  {|
    plift {X} := dist_lift;
    lift_ret := _;
    lift_bind := _;
                          
  |}.
Proof.
  - intros. simpl mreturn. unfold mreturn_dist. unfold dist_lift. simpl. constructor.
    + assumption.
    + constructor.
  - intros. simpl mbind. unfold mbind_dist.
    unfold dist_lift. rewrite Forall_map. rewrite Forall_concat. rewrite Forall_map.
    eapply Forall_impl.
    2:{destruct mx. simpl in *. rewrite Forall_map in H. exact H. }
    intros (k,v) pk. simpl. rewrite Forall_map.
    specialize (H0 k pk). destruct (f k). simpl in *. rewrite Forall_map in H0. eapply Forall_impl.
    2:{exact H0. }
    intros (a, b) pa. exact pa.
Defined. 


Definition state_prob_lift {S} {M} `{Monad M} `{PredLift M} {X} (Pre Post : S -> Prop) (P : X -> Prop) :=
  fun mx =>
    forall s, Pre s -> plift (fun '(x, s') => P x /\ Post s') (mx s). 

Lemma state_prob_lift_weaken {S M X} `{Monad M} `{PredLift M}{Pre : S -> Prop} (Post : S -> Prop) {Post' : S -> Prop}
  (P : X -> Prop) (m : Poram_st S M X) :
  (forall s, Post s -> Post' s) ->
  state_prob_lift Pre Post P m ->
  state_prob_lift Pre Post' P m.
Proof.
  Admitted.
                             

Definition read_access (id : block_id) :
  Poram_st state dist (path * nat) := access id Read.

Definition write_access (id : block_id) (v : nat) :
  Poram_st state dist (path * nat) := access id (Write v).

Definition write_and_read_access (id : block_id) (v : nat) :
  Poram_st state dist (path * nat) :=
  bindT (write_access id v ) (fun _ => read_access id).


Definition has_value (v : nat) : path * nat -> Prop := fun '(_, val) => v = val.

(*
 * state_prob_bind is analogous to the sequencing rule in Hoare Logic
 *)
Lemma state_prob_bind {S X Y} {M} `{Monad M} `{PredLift M} {Pre : S -> Prop}
      (Mid : S -> Prop) {Post : S -> Prop} (P: X -> Prop) {Q: Y -> Prop}
      {mx : Poram_st S M X} {f : X -> Poram_st S M Y} : 
  state_prob_lift Pre Mid P mx ->
  (forall x, P x -> state_prob_lift Mid Post Q (f x)) ->
  state_prob_lift Pre Post Q (bindT mx f). 
Admitted.

Lemma state_prob_ret {S X} {M} `{Monad M} `{PredLift M} {Pre : S -> Prop} {P : X -> Prop} {x : X}:
  P x -> state_prob_lift Pre Pre P (retT x).
Admitted.

(* Definition retT_lemma {S} {M} `{Monad M} *)
(*   `{PredLift M} {X} {P : X -> Prop} {Pre : S -> Prop} : *)
(*   forall x, P x -> state_lift Pre Pre P (retT x). *)
(* Proof. *)
(*   intros. *)
(*   unfold state_lift. *)
(*   intros s Pr_s. *)
(*   apply lift_ret. *)
(*   tauto. *)
(* Defined. *)

(* Definition bindT_lemma {S} {M} `{Monad M} *)
(*   `{PredLift M} {X Y} {P : X -> Prop} {Q : Y -> Prop} *)
(*   {Pre Mid Post : S -> Prop} : *)
(*   forall (mx : StateT S M X) (f : X -> StateT S M Y), *)
(*     state_lift Pre Mid P mx -> *)
(*     (forall x, P x -> state_lift Mid Post Q (f x)) -> *)
(*     state_lift Pre Post Q (bindT mx f). *)
(* Proof. *)
(*   intros. *)
(*   unfold state_lift. *)
(*   intros. *)
(*   eapply lift_bind. *)
(*   - exact (H2 s H4). *)
(*   - intros [x s'] [Px G]. *)
(*     apply H3; auto. *)
(* Qed. *)

Lemma get_State_wf {Pre : state-> Prop} :
  state_prob_lift Pre Pre Pre get_State.
Admitted.

Lemma dist2Poram_wf {X} (dx : dist X) {Pre : state -> Prop}:
  state_prob_lift Pre Pre (fun _ => True) (dist2Poram dx).
Proof.
  unfold state_prob_lift.
  intros. unfold plift. unfold Pred_Dist_Lift. unfold dist_lift.
  unfold dist2Poram. simpl. 
  rewrite Forall_map.
  rewrite Forall_concat.
  rewrite Forall_map.
  destruct dx; simpl.
  rewrite Forall_forall; intros.
  rewrite Forall_forall; intros.
  destruct x0; simpl.
  destruct p; simpl.
  split. exact I.
  destruct x.
  inversion H1.
  - inversion H2. rewrite H5 in H. auto.
  - simpl in H2. exfalso. auto.
Qed.

Lemma coin_flip_wf {Pre : state -> Prop} (l : nat):
  state_prob_lift Pre Pre (fun _ => True) (dist2Poram (constm_vec coin_flip l)).
Proof.
  eapply dist2Poram_wf.
Qed.

Lemma put_wf {Pre Pre' : state -> Prop} {s : state}:
  Pre' s -> state_prob_lift Pre Pre' (fun _ => True) (Poram_st_put s).
Admitted.


Definition get_payload (dist_a : dist (path * nat * state)): option nat :=
  match dist_pmf dist_a with 
  | [] => None
  | h :: t => match h with
            | (((_,v),_), _)  => Some v
            end
  end.
             
Definition blk_in_stash (id : block_id) (v : nat )(st : state) : Prop :=
  let s := state_stash st in 
  In (Block id v) s.

(* kv-rel relation should hold whenever we have a write access that has (id, v) into the ORAM.   *)
Definition kv_rel (id : block_id) (v : nat) (st : state) : Prop :=
  (blk_in_stash id v st) \/ (blk_in_path id v st). (* "Come back to me" -- The bone dog in Shogun Studio *)

 
Lemma remove_aux_lemma : forall (lst : list block) (a blk: block),
    In blk lst ->
    In blk (remove_aux lst a) \/ a = blk.
Proof.
  intros.
  induction lst; intuition.
  simpl.
  destruct andb eqn: eq_cond; simpl.
  - destruct H.
    + right.
      rewrite andb_true_iff in eq_cond.
      do 2 rewrite Nat.eqb_eq in eq_cond.
      rewrite <- H. destruct a, a0; f_equal; simpl in *; firstorder.
    + tauto.
  - destruct H.
    + do 2 left; auto.
    + apply IHlst in H. tauto.
Qed.
      
Lemma remove_list_sub_lemma : forall (x : block) (sub : list block) (lst : list block),
    In x lst ->
    In x (remove_list_sub sub lst) \/ In x sub.
Proof.
  intros blk s_lst.
  induction s_lst. 
  - simpl.  intros. left; auto.
  - intros. simpl remove_list_sub.
    pose proof (IHs_lst (remove_aux lst a))%list.
    destruct (remove_aux_lemma _ a _ H).
    + apply H0 in H1. destruct H1.
      * left. auto.
      * right. right; auto.
    + right. left; auto.
Qed.
        
Lemma kv_in_list_partition:
  forall (id : block_id) (v : nat) (s : state) (del : list block),
    blk_in_stash id v s ->
    (In (Block id v)
       (remove_list_sub del (state_stash s))  \/
    (In (Block id v) del)).
Proof.
  intros.
  unfold blk_in_stash in H.
  apply remove_list_sub_lemma.
  auto.
Qed.  

Fixpoint coord_in_bound (o : oram) (p : path) (stop: nat) : Prop :=
  match o with
  | leaf => False 
  | node d_o o_l o_r =>
      match stop with
      | 0%nat => True 
      | S stop' =>
          match p with
          | [] => False 
          | true :: xs => coord_in_bound o_l xs stop' 
          | false :: xs => coord_in_bound o_r xs stop'
          end
      end
  end.

Lemma kv_in_delta_to_tree :
  forall (s : state) (id : block_id) (v : nat) (del : list block)
    (lvl: nat )(p :path),
    In (Block id v) del ->
    coord_in_bound (state_oram s) p lvl ->
    In (Block id v)
      (concat (lookup_path_oram (up_oram_tr (state_oram s) lvl del p)p)).
Proof.
  (* current *)
  intros s.
  induction (state_oram s); intros ; simpl. try contradiction.
  - (* node case  *)
    simpl in H0.
    destruct lvl; simpl in *.
    + (* lvl is O *)
      simpl.
      unfold blk_in_path. simpl.
      rewrite in_concat. 
      destruct p.
      *  admit.
      (* we are in node of height 1,
         so the length of this list should not be empty *)
      * destruct b.
        -- exists del. split; auto. left; auto.
        -- exists del. split; auto. left; auto.
    + destruct p; simpl; auto.
      destruct b; simpl.
      * destruct payload.
        -- rewrite in_concat.
           pose proof (IHo1 id v del lvl p H H0).
           rewrite in_concat in H1. destruct H1. exists x. split.
           destruct H1.
           right. auto. tauto.
        -- rewrite in_concat. 
           pose proof (IHo1 id v del lvl p H H0).
           rewrite in_concat in H1. destruct H1. exists x. split.
           destruct H1. auto. tauto.
      * destruct payload.
        -- rewrite in_concat.
           pose proof (IHo2 id v del lvl p H H0).
           rewrite in_concat in H1. destruct H1. exists x. split.
           destruct H1.
           right. auto. tauto.
        -- rewrite in_concat. 
           pose proof (IHo2 id v del lvl p H H0).
           rewrite in_concat in H1. destruct H1. exists x. split.
           destruct H1. auto. tauto.
Admitted.

Lemma stash_path_combined_rel_Rd : forall (id : block_id) (v : nat) (s : state) (p_new : path),
    kv_rel id v s ->
    blk_in_stash id v ((get_pre_wb_st id Read (state_position_map s)
                          (state_stash s)
                          (state_oram s)
                          (calc_path id s) p_new)).
Proof.
  intros.
  unfold get_pre_wb_st. simpl.
  apply in_or_app.
  destruct H.
  - right; auto.
  - unfold blk_in_path in H. auto.
Qed.


Lemma stash_path_combined_rel_Wr : forall (id : block_id) (v : nat) (s : state) (p_new : path),
    blk_in_stash id v ((get_pre_wb_st id (Write v) (state_position_map s)
                          (state_stash s)
                          (state_oram s)
                          (calc_path id s) p_new)).
Proof.
  intros.
  unfold get_pre_wb_st;
  unfold blk_in_stash; simpl.
  left; auto.
Qed.


Lemma write_back_split : forall lvl k p (s : state),
    (k < lvl)%nat -> 
    write_back_r O p lvl s =
      write_back_r O p k 
      ((blocks_selection p k 
         (write_back_r (S k) p (lvl - 1 - k) s))).
Proof.
  unfold write_back_r.
  intros. apply factor_lemma. auto.
Qed.

Fixpoint locate_node_in_tr (o : oram) (lvl : nat) : path -> (option bucket):=
  match o in oram return path -> (option bucket) with
  | leaf => fun _ => None
  | node d o_l o_r =>
      fun p =>
        match lvl with
        | O => d
        | S lv =>
            match p with
            | [] => None
            | x :: xs =>
                match x with
                | true => locate_node_in_tr o_l lv xs
                | false => locate_node_in_tr o_r lv xs
                end
            end
        end
  end.

Definition at_lvl_in_path (o : oram ) (lvl : nat) (p : path) (x : block) : Prop :=
  match locate_node_in_tr o lvl p with
  | None => False
  | Some v => In x v
  end.

Fixpoint get_max_prf_idx (x : list bool) (y : list bool) : nat :=
  match x, y with
  | [], [] => O
  | h :: t, [] => O 
  | [], a :: b => O 
  | h :: t, a :: b =>
      if eqb h a then S (get_max_prf_idx t b )
      else get_max_prf_idx t b
  end.

Compute get_max_prf_idx [true; false] [true; true].
Compute get_max_prf_idx [true; false] [true; false].

Lemma pos_map_stable_across_blk_sel : forall p lvl s,
    state_position_map s = state_position_map (blocks_selection p lvl s).
Proof.
  reflexivity.
Qed.

Lemma pos_map_stable_across_wb : forall n p s start,
    state_position_map s = state_position_map (write_back_r start p n s).
Proof.
  unfold write_back_r.
  induction n; simpl; auto.
Qed. 

Lemma calc_path_pos_map_same : forall id s s',
    state_position_map s = state_position_map s' ->
    calc_path id s = calc_path id s'.
Proof.
  intros.
  unfold calc_path.
  congruence.
Qed.

Lemma calc_path_write_bk_r_stable : forall start id s n p ,
    calc_path id (write_back_r start p n s) = calc_path id s.
Proof.
  intros.
  apply calc_path_pos_map_same.
  symmetry.
  apply pos_map_stable_across_wb.
Qed.

Lemma at_lvl_in_path_blocks_selection :
  forall p p' lvl lvl' s b,
  (lvl < lvl')%nat ->
  at_lvl_in_path (state_oram s) lvl' p b ->
  at_lvl_in_path (state_oram (blocks_selection p' lvl s)) lvl' p b.
Proof.
  intros.
  unfold at_lvl_in_path in *.
  destruct locate_node_in_tr eqn:?.
  - admit.
  - destruct H0.
Admitted.

Lemma kv_in_delta_in_tree :
  forall (o : oram) (id : block_id) (v : nat) (del : list block) (lvl: nat )(p :path),
    In (Block id v) del ->
    coord_in_bound o p lvl ->
    at_lvl_in_path (up_oram_tr o lvl del p) lvl p (Block id v).
Admitted.

Lemma path_conversion : forall o lvl p p' b,
    isEqvPath p p' lvl = true -> 
    at_lvl_in_path o lvl p b -> at_lvl_in_path o lvl p' b.
Admitted.


Lemma takeL_in : forall {X} (x : X) n l,
   In x (takeL n l) -> In x l. 
Proof.
Admitted.

Lemma path_eq_get_cand_bs : forall id v h p stop m,
    In (Block id v) (get_cand_bs h p stop m) ->
    isEqvPath p (lookup_dict (makeBoolList false (length (dict_elems m))) id m) stop = true.
Admitted.              
  
Lemma stash_block_selection : forall p s id v lvl,
  blk_in_stash id v s ->
  blk_in_stash id v (blocks_selection p lvl s) \/
  (at_lvl_in_path (state_oram
                     (blocks_selection p lvl s)) lvl p (Block id v) /\
     at_lvl_in_path (state_oram
                       (blocks_selection p lvl s)) lvl (calc_path id s) (Block id v) 
  ).

Proof.
  intros.
  remember (blocks_selection p lvl s) as s'.
  unfold blocks_selection in Heqs'.
  unfold blk_in_stash in Heqs'.
  unfold blk_in_stash.
  rewrite Heqs'.
  simpl.
  remember (get_write_back_blocks p (state_stash s) 4 lvl (state_position_map s)) as dlt.
  apply kv_in_list_partition with (del := dlt) in H.
  destruct H.
  - left; auto.
  - right.
    split.
    + apply kv_in_delta_in_tree; auto. admit.                  (* coord in bound *)
    + apply path_conversion with (p := p).
      * rewrite Heqdlt in H. unfold get_write_back_blocks in H.
        destruct (length (state_stash s)); try contradiction.
        apply takeL_in in H.
        unfold calc_path.
        apply path_eq_get_cand_bs with (v := v )(h := state_stash s); auto.
      * apply kv_in_delta_in_tree; auto.
        admit.                  (* coord in bound *)
 Admitted.

Lemma write_back_in_stash_kv_rel_aux : forall n s p id v start,
  blk_in_stash id v s ->
  blk_in_stash id v (write_back_r start p n s) \/
  exists k, (start <= k /\ 
        at_lvl_in_path (state_oram (write_back_r start p n s)) k p (Block id v) /\
         at_lvl_in_path (state_oram (write_back_r start p n s)) k (calc_path id s) (Block id v))%nat.
Proof.
  induction n; intros.
  - left; auto.
  - destruct (IHn s p id v (S start) H).
    + unfold write_back_r at 1.
      simpl iterate_right at 1.
      destruct (stash_block_selection p _ id v start H0).
      * left; auto.
      * right.
        exists start; auto.
        repeat split; auto ; try tauto.
        destruct H1. rewrite calc_path_write_bk_r_stable in H2.
        exact H2.
    + destruct H0 as [k [Hk1 Hk2]].
      right; exists k.
      split; [lia|].
      unfold write_back_r; simpl iterate_right.
      split; destruct Hk2.
      * apply at_lvl_in_path_blocks_selection; auto.
      * apply at_lvl_in_path_blocks_selection; auto.
Qed.

Lemma locate_node_in_path : forall o lvl p b,
    locate_node_in_tr o lvl p = Some b ->
    In b (lookup_path_oram o p).
Proof.
  induction o.
  - intros.
    destruct p.
    + inversion H.
    + destruct b0; simpl in *; discriminate.
  - intros.
    destruct p.
    + admit.                    (* locate node on an empty path should be false  *)
    + destruct lvl; simpl in *.
      destruct b0; simpl.
      destruct payload; simpl.
      * left. inversion H. reflexivity.
      * discriminate.
      * destruct payload; simpl.
        -- left. inversion H. reflexivity.
        -- discriminate.
      * destruct b0; simpl in *.
        destruct payload; simpl.
        -- right. eapply IHo1; eauto.
        -- eapply IHo1; eauto.
        -- destruct payload; simpl.
           ++ right.  eapply IHo2; eauto.
           ++ eapply IHo2; eauto.
Admitted.           
      
Lemma weaken_at_lvl_in_path : forall o lvl p id v,
  at_lvl_in_path o lvl p (Block id v) ->
  blk_in_p id v o p.
Proof.
  intros.
  unfold at_lvl_in_path in *.
  destruct locate_node_in_tr eqn:?; [|tauto].
  unfold blk_in_path.
  unfold blk_in_p.
  rewrite in_concat.
  exists b. split; auto.
  apply locate_node_in_path with (lvl := lvl); auto.
Qed.
  
Lemma write_back_in_stash_kv_rel : forall s id v p,
    blk_in_stash id v s ->
    (* get_max_prf_idx p (calc_path id s) >= lvl *)
    kv_rel id v (write_back_r O p (length p) s).
Proof.
  intros.
  destruct (write_back_in_stash_kv_rel_aux (length p) s p id v 0 H).
  - left; auto.
  - destruct H0 as [k [_ Hk]].
    right.
    eapply weaken_at_lvl_in_path.
    rewrite calc_path_write_bk_r_stable.
    destruct Hk.
    eauto.
Qed.

Lemma distribute_via_get_post_wb_st : forall (id : block_id) (v : nat) (s : state) (p : path),
    blk_in_stash id v s -> 
    kv_rel id v (get_post_wb_st s p).
Proof.
  intros.
  unfold get_post_wb_st.
  apply write_back_in_stash_kv_rel; simpl; auto. 
Qed.    

Lemma zero_sum_stsh_tr_Wr
  (s : state) (id : block_id) (v : nat) (p p_new : path):
  kv_rel id v
    (get_post_wb_st
       (get_pre_wb_st id (Write v)
          (state_position_map s) (state_stash s) (state_oram s)
          (calc_path id s) p_new) p).
Proof.
  apply distribute_via_get_post_wb_st.
  apply stash_path_combined_rel_Wr.
Qed.

Lemma blk_in_path_in_lookup_oram : forall (id : block_id) (v : nat) (s : state) ,
    blk_in_path id v s -> 
    In (Block id v)
      (concat
         (lookup_path_oram (state_oram s)
            (calc_path id s)
         )
      ).
Proof.
  intros.
  unfold blk_in_path in H.
  unfold calc_path. auto.
Qed.

        
Lemma zero_sum_stsh_tr_Rd_rev :
  forall (id : block_id) (v : nat) (s : state) (p p_new : path), 
    kv_rel id v s  -> 
    kv_rel id v (get_post_wb_st
      (get_pre_wb_st id Read (state_position_map s)
         (state_stash s)
         (state_oram s)
         (calc_path id s) p_new) p). 
Proof.
  intros.
  apply distribute_via_get_post_wb_st. apply stash_path_combined_rel_Rd.
  apply H.
Qed.
  
Lemma lookup_ret_data_block_in_list (id : block_id) (v : nat) (l : list block) :
  NoDup (List.map block_blockid l) ->
  In (Block id v) l -> lookup_ret_data id l = v.
Proof.
  intro ND.
  intros.
  induction l; simpl; try contradiction.
  destruct (block_blockid a =? id) eqn: id_cond.
  - destruct H; simpl in *.
    + rewrite H; auto.
    + inversion ND; subst.
      rewrite Nat.eqb_eq in id_cond.
      rewrite id_cond in H2. Search In List.map.
      apply List.in_map with (f := block_blockid) in H.
      simpl in *. contradiction.
  - apply IHl.
    + inversion ND; auto.
    + destruct H; auto.
      rewrite H in id_cond. simpl in *. rewrite Nat.eqb_neq in id_cond.
      contradiction.
Qed.

Lemma zero_sum_stsh_tr_Rd (id : block_id) (v : nat) (m : position_map) (h : stash) (o : oram) :
  kv_rel id v (State m h o) ->
  get_ret_data id h (calc_path id (State m h o)) o = v.
Proof.
  simpl.
  intros.
  destruct H. 
  - (* assume in stash *)
    apply lookup_ret_data_block_in_list.
    + admit.              (* NoDup evidence *)
    + apply in_or_app. right. auto.
  - (* assume in path *)
    apply lookup_ret_data_block_in_list.
    + admit.                    (* NoDup evidence *)
    + unfold blk_in_path in H. simpl in *.
    apply in_or_app. left. auto.
Admitted.
        
Lemma read_access_wf (id : block_id)(v : nat) :
  state_prob_lift (fun st => @well_formed st /\ kv_rel id v st) (fun st => @well_formed st /\ kv_rel id v st) (has_value v) (read_access id).
Proof.
  remember (fun st : state => well_formed st /\ kv_rel id v st) as Inv. 
  apply (state_prob_bind Inv Inv).
  - apply get_State_wf.
  - intros.
    apply (state_prob_bind Inv (fun _ => True)).
    + apply coin_flip_wf.
    + intros. simpl.
      apply (state_prob_bind Inv (fun _ => True)).
      * apply put_wf. rewrite HeqInv in H; destruct H.
        rewrite HeqInv. split. exact H.
        apply zero_sum_stsh_tr_Rd_rev. auto.
      * intros. rewrite HeqInv. apply state_prob_ret.
        rewrite HeqInv in H. destruct H. simpl.
        symmetry. apply zero_sum_stsh_tr_Rd.
        auto. 
Qed.

Lemma write_access_wf (id : block_id) (v : nat) :
  state_prob_lift (fun st => @well_formed st) (fun st => @well_formed st /\ kv_rel id v st) (fun _ => True) (write_access id v).
Proof.
  remember (fun st : state => well_formed st) as Inv.
  apply (state_prob_bind Inv Inv).
  - apply get_State_wf.
  - intros.
    apply (state_prob_bind Inv (fun _ => True)).
    + apply coin_flip_wf.
    + intros. simpl.
      apply (state_prob_bind (fun st => @well_formed st /\ kv_rel id v st) (fun _ => True)).
      * apply put_wf; simpl; split. rewrite HeqInv in H. exact H.  
        apply zero_sum_stsh_tr_Wr.
      * intros. rewrite HeqInv. eapply state_prob_ret. auto.
Qed.

(*
 * this lemma is saying that the write_and_read_access preserves the well-formedness invariant
 * and returns the correct value
 *)

Lemma write_and_read_access_lift (id : block_id)(v : nat):
  state_prob_lift (@well_formed) well_formed (has_value v)
                  (write_and_read_access id v).
Proof.
  apply (state_prob_bind
           (fun st => well_formed st /\ kv_rel id v st)
           (fun _ => True)).
  - eapply write_access_wf.
  - intros _ _.
    apply (state_prob_lift_weaken (fun st : state => well_formed st /\ kv_rel id v st)).
    + tauto.
    + apply read_access_wf.
Qed.

Lemma extract_payload (id : block_id) (v: nat) (s : state) : 
  plift (fun '(x, s') => has_value v x /\ well_formed s') (write_and_read_access id v s) -> 
  get_payload (write_and_read_access id v s) = Some v.
Proof.
  intros ops_on_s.
  destruct (write_and_read_access id v s). unfold get_payload.
  simpl in *. destruct dist_pmf0.
  - simpl in *. admit.         (* need distribution well-formedness. i.e. all Qs add up to 1.0 *)
  - simpl in *.  destruct p.  destruct p.  destruct p. simpl in ops_on_s. inversion ops_on_s.
    destruct H1. simpl in H1. congruence.
Admitted.

Theorem PathORAM_simulates_RAM (id : block_id) (v : nat) (s : state) :
  well_formed s ->
    get_payload(write_and_read_access id v s) = Some v.
Proof.
  intros wf_s.
  apply extract_payload.
  apply write_and_read_access_lift. auto.
Qed.
