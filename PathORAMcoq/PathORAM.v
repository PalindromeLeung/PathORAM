Require Import List.
Import ListNotations.
From Coq Require Import Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Even.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat. 
Require Import Coq.Program.Wf.
Require Import Streams.
Require Import Coq.ZArith.Zdiv.

Section Utils.

End Utils.

Section Tree.
  
  Inductive PBTree (A: Type) : Type :=
  | Leaf (idx: nat) (val: A)
  | Node (idx: nat) (val: A) (l r: PBTree A).

  Arguments Leaf {_} _ _.
  Arguments Node {_} _ _ _ _.

  Fixpoint getHeight {A: Type} (root: PBTree A) : nat :=
    match root with
    | Leaf _ _ => 0
    | Node _ _ l r => S (max (getHeight l) (getHeight r))
    end.

  Fixpoint buildPBTlevelOrder {A} (def_a : A) (label : nat) (ht : nat) : PBTree A :=
    match ht with
    | 0 => Leaf label def_a
    | S ht' => Node label def_a
                      (buildPBTlevelOrder def_a (2 * label + 1) ht')
                      (buildPBTlevelOrder def_a (2 * label + 2) ht')
    end.

  Definition PBTree1 {A} : PBTree (list A) := buildPBTlevelOrder [] 0 3.

  Compute PBTree1.
  
  Inductive Dir := L | R.

  (* path needed to reach lfIdx in a BFS-numbered binary tree *)
  (* Definition getPath (lfIdx : nat) : list Dir.  *)



  (* 1 goal (ID 92) *)
  
  (* idx : nat *)

  (* ============================ *)
  (* Nat.pred (Nat.div idx 2) < S idx *)

  Lemma div2 : forall (n : nat), PeanoNat.Nat.div2 n  < S n.
  Proof.
    fix IH 1.
    intro n. case n.
    - constructor.
    - intro n0. case n0.
      + constructor. constructor.
      + intro n1. specialize (IH n1). simpl.
        apply Lt.lt_n_S.
        apply PeanoNat.Nat.lt_lt_succ_r. apply IH.
  Defined.

  Program Fixpoint getPath (lfIdx : nat) {measure lfIdx} : list Dir :=
    match lfIdx with
    | 0 => []
    | S idx => if Nat.even idx
              then [L] ++ getPath (PeanoNat.Nat.div2 idx)
              else [R] ++ getPath (PeanoNat.Nat.div2 idx)
    end.
  Next Obligation.
    apply div2.
    Qed.
  Next Obligation.
  apply div2.
  Defined.

  Definition p9 := getPath 9.

  Definition p12 := getPath 12.

  Fixpoint buildNodeLevelDict {A} (root: PBTree A) (currL : nat) : list (prod nat nat) :=
    match root with
    | Leaf idx val => [pair idx currL]
    | Node idx val l r =>
        [pair idx currL] ++ buildNodeLevelDict l (S currL)  ++ buildNodeLevelDict r (S currL)
    end.

  Compute buildNodeLevelDict PBTree1 0.

  Fixpoint writeAtPath {A} (root : PBTree A) (path : list Dir) (data : A) : PBTree A :=
    match root with
    | Leaf idx val => match path with
                     | [] => Leaf idx data
                     | _ => Leaf idx val (* path longer than height of tree*)
                     end
    | Node idx val l r => match path with
                         | [] => Node idx data l r
                         | L :: path' => Node idx val (writeAtPath l path' data) r
                         | R :: path' => Node idx val l (writeAtPath r path' data)
                         end
    end.

  Compute writeAtPath PBTree1 p12 [1;2;3].
  Compute writeAtPath PBTree1 p9 [4;5;6].

  
  Definition writeToNode {A} (root : PBTree A) (lfIdx : nat) (tgtl : nat) (data : A) : PBTree A :=
    writeAtPath root (firstn tgtl (getPath lfIdx)) data. 

  Compute PBTree1.
  Compute writeToNode PBTree1 9 2 [0; 1; 2].

  (* Definition of rand comes from Yves Bertot *)
  CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
    let seed' := Zmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).           

  Fixpoint take {X} n (str : Stream X) : list X :=
    match n with
    | 0 => []
    | S m => match str with
            | Cons x str' => x :: take m str'
            end
    end.

  Definition first60 := take 60(rand 475 919 953).

  Definition md_tot := fun x => Zmod x 15.

  Definition randSeq := List.map Z.to_nat (List.map md_tot first60).

  Fixpoint modNodesTotal (randList : list Z) : list nat :=
    List.map Z.to_nat(List.map md_tot randList).

  Fixpoint indexed_list {X} (start : nat) (l : list X) : list (nat * X) :=
    match l with
    | [] => []
    | h :: t => (start, h) :: indexed_list (S start) t
    end.

  Compute indexed_list 0 randSeq.

  Fixpoint aggregation_helper (key : nat)(val : nat)(l : list (nat * (list nat))):
    list (nat * (list nat)) :=
    match l with
    | [] => [(key, [val])]
    | (n, al) :: t => if Nat.eqb n key
                  then (key, val :: al) :: t 
                  else (n, al) :: aggregation_helper key val t
    end.

(*   defaultdict(<class 'int'>, 
{1: 7, 2: 13, 3: 8, 4: 13, 5: 14, 6: 12, 7: 7, 8: 7, 9: 8, 10: 13, 11: 9, 12: 3, 13: 2, 14: 12, 15: 8, 16: 7, 17: 10, 18: 9, 19: 12, 20: 2, 21: 1, 22: 7, 23: 4, 24: 2, 25: 1, 26: 8, 27: 12, 28: 14}) *)


(* defaultdict(<class 'list'>, 
{7: [1, 7, 8, 16, 22], 13: [2, 4, 10], 8: [3, 9, 15, 26], 14: [5, 28], 12: [6, 14, 19, 27], 9: [11, 18], 3: [12], 2: [13, 20, 24], 10: [17], 1: [21, 25], 4: [23]}) *)
           
  Fixpoint aggregation (l : list (nat * nat)): list (nat * (list nat)):=
    match l with
    | [] =>  []
    | (b, n) :: t => aggregation_helper n b (aggregation t)
    end.

  Compute aggregation [(1, 3); (2,3); (8, 3); (4, 4); (5,4)].

  Fixpoint makeNZeros (n : nat) : list nat :=
    match n with
    | O => []
    | S n' => O :: makeNZeros n'
    end.
  
  Check prod.
  Fixpoint pairGen (l : list(nat * list  nat)) : list (nat * nat) :=
    match l with 
    | nil => []
    | (n, al) :: t => List.combine al (makeNZeros (List.length al))
    end.

  (* Fixpoint initialize_tree {A} {B} {C}(root : PBTree A) (stsh : list (prod B C)) : PBTree A := *)
  (*   match root with *)
  (*   | Leaf idx val =>  *)
  (*   | Node idx val l r =>  *)
  
End Tree.



Section STASH.
  Definition concatStash {A} (stsh : list (prod nat A)) (a : list (prod nat A)) := stsh ++ a.
  
  
End STASH.


Section PathORAM.
  Definition nodesTotal := 60.
  Definition nodeCap := 4.
  Definition stashInit := [].

  Inductive Op :=
  | Rd
  | Wr.

  
End PathORAM.


Section PathORAM.
  Fixpoint ValEq (a : nat) (b : nat): Prop := eq_nat a b.
  Definition dataNone := 45.

  Fixpoint access (op : Op) (blockId : nat) (data: nat): nat . Admitted.

  Theorem PathORAMValid: forall (data: nat)(blockId: nat),
    AccessStream (access Wr blockId data) (access Rd blockId dataNone),
    ValEq data (access Rd blockId dataNone).
    
  Admitted.

  
  
  Theorem PathORAMSecure :
    forall (i: nat) (oplista: list Operation)(oplistb: list Operation)
      (datalista: list nat) (datalistb: list nat) 
      (blocklista: list nat) (blocklistb list nat)
      (a : list (access (fetchlist oplista i) (fetchlist blocklista i ) (fetchlist datalista i)))
      (b : list (access (fetchlist oplistb i) (fetchlist blocklistb i ) (fetchlist datalistb i))), comp_indistinguish a b.

    
  
End PathORAM.
