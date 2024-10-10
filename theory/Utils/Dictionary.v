Require Import POram.Utils.Classes.
Require Import Coq.Lists.List.
Import ListNotations.

Record dict (K V : Type) := Dict { dict_elems : list (K * V) }.
Arguments Dict {K V} _.
Arguments dict_elems {K V} _.

Fixpoint lookup_falist {K V : Type} `{Ord K} (v : V) (k : K) (kvs : list (K * V)) :=
  match kvs with
  | [] => v
  | (k' , v') :: kvs' =>
    match ord_dec k k' with
    | Lt => v
    | Eq => v'
    | Gt => lookup_falist v k kvs'
    end
  end.

Fixpoint update_falist {K V : Type} `{Ord K} (k : K) (v : V) (kvs : list (K * V)) : list (K * V) :=
  match kvs with
  | [] => [ (k , v) ]
  | (k' , v') :: kvs' =>
    match ord_dec k k' with
    | Lt => (k , v) :: (k' , v') :: kvs'
    | Eq => (k , v) :: kvs'
    | Gt => (k' , v') :: update_falist k v kvs'
    end
  end.

Definition lookup_dict {K V : Type} `{Ord K} (v : V) (k : K) (kvs : dict K V) := 
  lookup_falist v k (dict_elems kvs).

Definition update_dict {K V : Type} `{Ord K} (k : K) (v : V) (kvs : dict K V) : dict K V :=
  Dict (update_falist k v (dict_elems kvs)).

Lemma lookup_update_diffid {K V} `{Ord K} : forall (k k' : K) (v v_def : V) m,
  k <> k' ->
  lookup_dict v_def k (update_dict k' v m) =
  lookup_dict v_def k m.
Proof.
  intros.
  unfold lookup_dict.
  unfold update_dict.
  destruct m as [m]; simpl.
  induction m as [|[k0 v0] tl]; simpl.
  - destruct ord_dec eqn:id_cond; auto.
    apply ord_eq in id_cond; contradiction.
  - destruct (ord_dec k' k0) eqn:id_cond; simpl.
    + apply ord_eq in id_cond; subst.
      destruct (ord_dec k k0) eqn:id_cond; auto.
      apply ord_eq in id_cond; contradiction.
    + destruct (ord_dec k k') eqn:id_cond'.
      * apply ord_eq in id_cond'; subst; contradiction.
      * rewrite ord_lt_trans with (y := k'); auto.
      * reflexivity.
    + rewrite IHtl; auto.
Qed.

Lemma lookup_update_sameid {K V} `{Ord K} : forall (k : K) (v v_def : V) m, 
  lookup_dict v_def k (update_dict k v m) = v.
Proof.
  intros.
  unfold lookup_dict.
  unfold update_dict.
  destruct m as [m]; simpl.
  induction m as [|[k0 v0] tl]; simpl.
  - rewrite ord_refl; auto.
  - destruct (ord_dec k k0) eqn:id_cond; simpl.
    + rewrite ord_refl; auto.
    + rewrite ord_refl; auto.
    + rewrite id_cond.
      exact IHtl.
Qed.
