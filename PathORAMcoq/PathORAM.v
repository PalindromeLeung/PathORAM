Require Import List.
Import ListNotations.
From Coq Require Import Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.
Require Import Coq.Init.Datatypes.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat. 

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

  Inductive Dir := L | R.

  (* path needed to reach lfIdx in a BFS-numbered binary tree *)
  Definition getPath (lfIdx : nat) : list Dir.
  Admitted.

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

  Definition writeToNode {A} (root : PBTree A) (lfIdx : nat) (tgtl : nat) (data : A) : PBTree A := writeAtPath root (firstn tgtl (getPath lfIdx)) data.

  (*
  Fixpoint writeToNode {A} (root : PBTree A) (lfIdx : nat) (tgtl : nat) (data : A) : PBTree A :=
    match tgtl with
    | 0 => match root with
          | Leaf idx _ => Leaf idx data
          | Node idx _ l r => Node idx data l r
          end
    | S tgtl => match root with
               | Leaf _ _ => root
               | Node idx val l r => if isLeft lfIdx tgtl 
    *)  
End Tree.





Section PathORAM.
  Definition nodesTotal := 28.
  Definition nodecap := 4.

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
