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

Require Import  ExtLib.Data.Monads.StateMonad ExtLib.Structures.Monads.
    


Section Utils.

End Utils.

Section Tree.
(* (***************************************) *)
(* (*************** STASH *****************) *)
(* (***************************************) *)


(* Section STASH. *)
  Definition concatStash {A} (stsh : list (prod nat A)) (a : list (prod nat A)) := stsh ++ a.

  Fixpoint readBlockFromStash (stsh : list(nat * nat)) (bID : nat) : option nat :=
    match stsh with
    | [] => None
    | h :: t => if Nat.eqb (fst h) bID
              then Some(snd h)
              else readBlockFromStash t bID
    end.
     
  
(* End STASH. *)



  
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


  Fixpoint isPBTree {A} (t : PBTree A) : Prop :=
    match t with
    | Leaf _ _ => True
    | Node _ _ l r => getHeight l = getHeight r
                     /\ (isPBTree l) /\( isPBTree r)
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

  Compute getPath 9.
  Definition p9 := getPath 9.

  Compute getPath 12.
  Definition p12 := getPath 12.

  Fixpoint buildNodeLevelDict {A} (root: PBTree A) (currL : nat) : list (prod nat nat) :=
    match root with
    | Leaf idx val => [pair idx currL]
    | Node idx val l r =>
        [pair idx currL] ++ buildNodeLevelDict l (S currL)  ++ buildNodeLevelDict r (S currL)
    end.

  Compute buildNodeLevelDict PBTree1 0.

  Fixpoint writeAtPath {A} (root : PBTree A)
           (path : list Dir) (data : A) : PBTree A :=
    match root with
    | Leaf idx val =>
        match path with
        | [] => Leaf idx data
        | _ => Leaf idx val (* path longer than height of tree*)
        end
    | Node idx val l r =>
        match path with
        | [] => Node idx data l r
        | L :: path' => Node idx val (writeAtPath l path' data) r
        | R :: path' => Node idx val l (writeAtPath r path' data)
        end
    end.

  Compute writeAtPath PBTree1 p12 [1;2;3].
  Compute writeAtPath PBTree1 p9 [4;5;6].
  Compute writeAtPath PBTree1 (getPath 4) [5;5;5]. (* 4 and 5 seem to be flipped *)
  
  Definition writeToNode {A} (root : PBTree A) (lfIdx : nat) (tgtl : nat) (data : A) : PBTree A :=
    writeAtPath root (firstn tgtl (getPath lfIdx)) data. 

  Compute PBTree1.
  Compute writeToNode PBTree1 9 2 [0; 1; 2].

  (* Definition of rand comes from Yves Bertot *)
  CoFixpoint rand (seed n1 n2 : Z) : Stream Z :=
    let seed' := Zmod seed n2 in Cons seed' (rand (seed' * n1) n1 n2).           

  Fixpoint takeS {X} n (str : Stream X) : list X :=
    match n with
    | 0 => []
    | S m => match str with
            | Cons x str' => x :: takeS m str'
            end
    end.

  Definition first60 := takeS 60(rand 475 919 953).

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
  Definition position_map := indexed_list 0 randSeq.
  
  Fixpoint aggregation_helper (key : nat)(val : nat)(l : list (nat * (list nat))):
    list (nat * (list nat)) :=
    match l with
    | [] => [(key, [val])]
    | (n, al) :: t => if Nat.eqb n key
                  then (key, val :: al) :: t 
                  else (n, al) :: aggregation_helper key val t
    end.
           
  Fixpoint aggregation (l : list (nat * nat)): list (nat * (list nat)):=
    match l with
    | [] =>  []
    | (b, n) :: t => aggregation_helper n b (aggregation t)
    end.

  Compute aggregation [(1, 3); (2,3); (8, 3); (4, 4); (5,4)].
  Definition n_bl_pair := aggregation [(1, 3); (2,3); (8, 3); (4, 4); (5,4)].

  Fixpoint makeNZeros (n : nat) : list nat :=
    match n with
    | O => []
    | S n' => O :: makeNZeros n'
    end.

  Compute makeNZeros 10.


  Fixpoint takeL {A} n (l : list A) : list A :=
    match n with
    | O => []
    | S m => match l with
            | [] => []
            | h :: t => h :: takeL m t 
            end
    end.

  Compute takeL 4 [1;2;3].
  
  Fixpoint takeFromIdx {A} (n : nat) (l : list A)  : list A :=
    match l with
    | [] => []
    | h :: t => match n with
              | O => h :: t
              | S m => takeFromIdx m t
              end
    end.

  Compute takeFromIdx 2 [1; 2; 3;4].
  
  
  Fixpoint pairGen {A} (l : list(nat * list nat)) (rt : PBTree A ): list (nat * nat) :=
    match l with
    | [] => []
    | (n, bs) :: t => match rt with
                    | Leaf idx _ => if Nat.eqb n idx
                                   then List.combine bs (makeNZeros (List.length bs))
                                                     (* expand this n's bs *)
                                   else pairGen t rt (* recurse  *)
                    | Node idx _ l r => if Nat.eqb n idx
                                       then List.combine bs (makeNZeros (List.length bs))
                                                         (* expand this n's bs *)
                                       else pairGen t rt  (* recurse  *)
                    end
    end.

  Compute pairGen n_bl_pair (Leaf 3 3).
  Compute takeL 2 (pairGen n_bl_pair (Leaf 3 3)). 

  Check writeAtPath.

  Definition initialT A := (PBTree A, list(nat * nat)).

  Print option.

  (* define type of the initialzation function; needs to talk to Big T*)
  Inductive initialType A : Type :=
  | TreeStash : PBTree A -> list(nat * nat) -> initialType A.
    
  
  Fixpoint initializeTree (rt : PBTree (list (nat * nat))) (stsh : list (nat * nat))
           (l : list(nat * list nat)): option(initialType (list (nat * nat))) :=
    
    match rt with
    | Leaf idx val =>
        let data := pairGen l rt in
        match data with
        | [] => None
        | h :: t => let dataH := takeL 4 data in
                  let dataT := takeFromIdx 4 data in
                  let newStsh := stsh ++ dataT in
                  Some(TreeStash (list(nat * nat))(writeAtPath rt (getPath idx) dataH) newStsh)
        end
    | Node idx val lc rc =>
        let data := pairGen l rt in
        match data with
        | [] => let dataH := takeL 4 data in
               let dataT := takeFromIdx 4 data in
               let newStsh := stsh ++ dataT in
               Some(TreeStash (list (nat * nat))(writeAtPath rt (getPath idx) dataH) newStsh)
        | h :: t => match initializeTree lc stsh l with
                  | Some x => Some x 
                  | None => initializeTree rc stsh l
                  end
        end
    end.

  Program Fixpoint getPath' (lfIdx : nat) {measure lfIdx} : list nat :=
    match lfIdx with
    | 0 => [0]
    | S idx => if Nat.even idx
              then [S idx] ++ getPath' (PeanoNat.Nat.div2 idx)
              else [S idx] ++ getPath' (PeanoNat.Nat.div2 idx)
    end.
  Next Obligation.
    apply div2.
    Qed.
  Next Obligation.
    apply div2.
    Defined.

  Compute rev(getPath' 11).                

  Fixpoint clearPath (rt: PBTree (list (nat * nat ))) (l : list nat): PBTree (list(nat * nat)) := 
    match l with
    | [] => rt
    | h :: t => match rt with
              | Leaf idx val => if Nat.eqb h idx
                             then Leaf idx []
                             else Leaf idx val
                                       
              | Node idx val lc rc => if Nat.eqb h idx
                                     then Node idx [] (clearPath lc t) (clearPath rc t)
                                     else Node idx val (clearPath lc t) (clearPath rc t) 
              end
    end.
  
  Compute writeAtPath PBTree1 (getPath 5) [5;5;5].
  Compute clearPath PBTree1 (rev(getPath' 11)).
  Compute rev(getPath' 11).  

  Inductive  NodeData: Type := Data:(nat * list(nat * nat)) -> NodeData .

  Fixpoint getNodeAtLevel (lvl: nat) (l: list nat) (rt: PBTree (list (nat * nat))): option NodeData:=
    match lvl with
    | O => match l with
          | [] => None
          | h :: t => match rt with
                    | Leaf idx val => if Nat.eqb idx h
                                     then Some (Data (idx, val))
                                     else None
                    | Node idx val lc rc => if Nat.eqb idx h
                                           then Some (Data (idx, val))
                                           else
                                             match getNodeAtLevel lvl t lc with
                                             | None => getNodeAtLevel lvl t rc
                                             | Some x => Some x
                                             end
                    end
          end
    | S m => match l with
            | [] => None
            | h :: t => match rt with
                      |Leaf idx val => if Nat.eqb idx h
                                      then Some (Data (idx, val))
                                      else None
                      |Node idx val lc rc => if Nat.eqb idx h
                                            then Some (Data(idx, val))
                                            else
                                              match getNodeAtLevel lvl t lc with
                                              | None => getNodeAtLevel lvl t rc
                                              | Some x => Some x
                                              end
                      end
            end
    end.

  Fixpoint ReadnPopNodes (rt: PBTree (list (nat * nat))) (l: list nat) (stsh: list (nat * nat)) : list (nat * nat) :=
    match l with
    | [] => []
    | h :: t => match rt with
              | Leaf idx val => if Nat.eqb h idx
                               then stsh ++ val 
                               else stsh 
              | Node idx val lc rc => if Nat.eqb h idx
                                     then stsh ++ val 
                                     else stsh 
              end
    end.

  Scheme Equality for list.

  Print list_beq.

  Fixpoint posMapLookUp (bID : nat) (posMap : list(nat * nat)) :option nat :=
    match posMap with
    | [] => None
    | h :: t => if Nat.eqb (fst h) bID
              then Some (snd h)
              else posMapLookUp bID t
    end.
                
  Fixpoint retSomeVal (x : option nat) : nat :=
    match x with
    | None => 0
    | Some n => n
    end.

  Fixpoint eqListPair (l1 : list (nat * nat)) (l2 :  list (nat * nat)) : bool :=
    match l1 with
    | [] => match l2 with
           | [] => true
           | h :: t => false
           end
    | x :: xs => match l2 with
               | [] => false 
               | h :: t => if (andb (Nat.eqb (fst x) (fst h)) (Nat.eqb (snd x) (snd h)))
                         then eqListPair xs t
                         else false
               end
    end.
               
      
  Fixpoint NodeDataEq (n1: NodeData) (n2: NodeData) : bool :=
    match n1 with
    | Data (x, y) =>
        match n2 with
        | Data (a, b) => if Nat.eqb x a
                        then eqListPair y b
                        else false
        end
    end.
  
  Inductive BlockEntry : Type := BV: (nat * nat) -> BlockEntry.

  Fixpoint getCandidateBlocksHelper (rt: PBTree(list(nat * nat))) (l: list nat)
           (lvl: nat)(bID: nat)(stsh: list(nat * nat)): option BlockEntry:=
    match getNodeAtLevel lvl l rt with (* P(x, l) *)
    | None => None
    | Some val =>
        match getNodeAtLevel lvl (getPath' (retSomeVal(posMapLookUp bID position_map))) rt with (* P(position[a'],l) *)
        | None => None
        | Some val' => if NodeDataEq val val'
                      then match readBlockFromStash stsh bID with
                           | Some n => Some(BV(bID, n))
                           | _ => None
                           end
                      else None
        end
    end.
                                 
  Fixpoint getCandidateBlocks (rt: PBTree(list(nat * nat))) (l: list nat) (lvl: nat) (stsh: list(nat * nat)) : list BlockEntry :=
    match stsh with
    | [] => []
    | (bid,bdata) :: t =>
        match getCandidateBlocksHelper rt l lvl bid stsh with
        | None =>  (getCandidateBlocks rt l lvl t)
        | Some v => v :: (getCandidateBlocks rt l lvl t)
        end                     
    end.

                                       
                                                              
                                       
                                 
                                                        

  
End Tree.







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

  (* S -> S * X *)
  (*           proj_2 () *)
            
  Theorem PathORAM_simulates_RAM: forall (data: nat)(blockId: nat),
    bind (access Wr blockId data) (access Rd blockId dataNone) ->
    ValEq data getData(access Rd blockId dataNone).
    
  Admitted.

  
  
  Theorem PathORAMIsSecure :
    forall (y : list Access) (z : list Access), 
     comp_indistinguish (getPos(fold_LM y)) (getPos(fold_LM z)). 


    
    forall (i: nat) (oplista: list Operation)(oplistb: list Operation)
      (datalista: list nat) (datalistb: list nat) 
      (blocklista: list nat) (blocklistb list nat)
      (a : list (access (fetchlist oplista i) (fetchlist blocklista i ) (fetchlist datalista i)))
      (b : list (access (fetchlist oplistb i) (fetchlist blocklistb i ) (fetchlist datalistb i))), comp_indistinguish a b.

    
  
End PathORAM.
