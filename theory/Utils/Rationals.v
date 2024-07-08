Require Import POram.Utils.Classes.
Import MonadNotation.
Require Import Coq.QArith.QArith.
Require Import Coq.Lists.List.
Import ListNotations.
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
