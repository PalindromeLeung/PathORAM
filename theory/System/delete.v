Class Eq A := 
{
    eqb : A -> A -> bool;
}

Notation "x =? y" := (eqb x y) (at level 70). 

#[export] Instance eqBool : Eq bool := 
{
    eqb := fun (b c : bool) => 
    match b,c with 
    | true, true => true
    | true, false => false 
    | false, true => false 
    | false, false => true 
    end 
}.

#[export] Instance eqNat : Eq nat :=
{
    eqb := Nat.eqb 
}. 

#[export] Instance eqPair {A B: Type} `{Eq A} `{Eq B} : Eq (A * B) := 
{
    eqb p1 p2 := 
    let (p1a, p1b) := p1 in 
    let (p2a, p2b) := p2 in 
    andb (p1a =? p2a) (p1b =? p2b) 
}. 

Fixpoint EqList_aux {A : Type} (l1 : list A) (l2 : list A) : bool := 
    match l1, l2 with 
    | [],[] => true 
    | h :: t, [] => false 
    | [], h :: t => false 
    | h :: t, x :: xs => if eqNat h x 
                         then EqList_aux t xs  
                         else false 
    end. 


#[export] Instance eqList {A: Type} `{Eq A} : Eq (list A) :=
{
    eqb l1 l2 := EqList_aux l1 l2     
}.

Fixpoint EqOption_aux {A : Type} `{Eq A} (o1: Option A)(o2: Option A) : bool := 
match o1, o2 with 
| None, None => true
| None, Some _ => false
| Some _, None => false 
| Some a, Some b => if eqb a b 
                    then true 
                    else false
end. 


