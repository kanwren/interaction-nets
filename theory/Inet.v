Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Vector.
Import List.ListNotations.
From Inet Require Import Map.

Open Scope string_scope.
Open Scope list_scope.

(* Default notation for vectors overrides list notation. Redefine it *)
Notation "'<<' '>>'" := (Vector.nil _) (at level 60, right associativity).
Notation "h <::> t" := (Vector.cons _ h _ t) (at level 60, right associativity).
Notation "<< x >>" := (x <::> <<>>).
Notation "<< x ; y ; .. ; z >>" := 
  (Vector.cons _ x _ (Vector.cons _ y _ .. (Vector.cons _ z _ 
  (Vector.nil _)) ..)).
Infix "<++>" := (Vector.append) (at level 60, right associativity).

Check <<>>.
Check 1 <::> <<>>.
Check 1 <::> 2 <::> <<>>.
Check << 1; 2 >>.
Check <<1;2>> <++> <<3;4>>.

(* Arity-indexed family of agents *)

Definition name : Type := string.
Definition agent (arity : nat) : Type := name.

Check "alpha" : agent 1.

(* Terms *)
Inductive term : Type :=
  | leaf : name -> term
  (* Arity-indexed tree *)
  | tree : forall arity : nat,
      agent arity -> VectorDef.t term arity -> term.

Arguments tree {arity}.

Check leaf "alpha".
Check tree "alpha" << leaf "beta"; leaf "gamma" >>.
Fail Check @tree 3 "alpha" << leaf "beta"; leaf "gamma" >>.

Fixpoint names_of_term (t : term) : list string :=
  match t with
  | leaf n => [n]
  | tree  _ terms => 
      List.concat (Vector.to_list (Vector.map names_of_term terms))
  end.

Compute names_of_term (leaf "alpha").
Compute names_of_term (tree "alpha" << leaf "beta"; leaf "gamma" >>).

(* Renaming and Substitution *)
Reserved Notation "'[[' x ':=' u ']]' t" (at level 20).
Fixpoint subst (t : term) (x : string) (u : term) : term :=
  match t with
  | leaf n =>
      if eqb_string n x then
        u
      else
        t
  | tree agent terms =>
      tree agent (Vector.map (fun t =>
        [[x := u]] t
      ) terms)
  end
where "'[[' x ':=' u ']]' t" := (subst t x u).

Compute [["x" := leaf "y"]] (leaf "x").
Compute [["x" := tree "x" << leaf "y"; leaf "z" >>]] (
  tree "alpha" <<
    leaf "x";
    tree "beta" <<
      leaf "x";
      leaf "y";
      leaf "z"
    >>
  >>
).

Compute [["y" := leaf "v"]] ([["x" := leaf "u"]] (leaf "y")).
Compute [["x" :=  [["y" := leaf "v"]] leaf "u"]] (leaf "y").

(* Rules *)
Inductive interacts_with : term -> term -> Prop :=
  | rule : forall t1 t2, interacts_with t1 t2.
Notation "t1 '⋈' t2" := (interacts_with t1 t2) (at level 60, right associativity).

Check (leaf "alpha") ⋈ (leaf "beta").
Check (tree "alpha" << leaf "beta"; leaf "gamma" >>) ⋈ (leaf "beta").
  
(* Define some agents *)
Definition x := leaf "x".
Definition y := leaf "y".
Definition t := leaf "t".
Definition O := tree "O" (<<>>).
Definition S (n : term) := tree "S" <<n>>.
Definition add (x : term) (y : term) := tree "add" << x ; y >>.

Definition add_O := O ⋈ add y y.
Definition add_S := S (add y t) ⋈ add y (S t).

Inductive unify : term -> term -> Prop :=
  | goal : forall t1 t2, unify t1 t2.
Notation "t1 ~= t2" := (unify t1 t2) (at level 60, right associativity).

Definition eqn : Type := term * term.

Fixpoint combine_vecs_to_list {X : Type} {n : nat} (a : VectorDef.t X n)
  (b : VectorDef.t X n) :=
  let xs := Vector.to_list a in
  let ys := Vector.to_list b in
  List.combine xs ys.

Notation "xs <*> ys" := (combine_vecs_to_list xs ys) (at level 60, right associativity).

Inductive steps_to : list eqn -> list eqn -> Prop :=
  | interaction :
      forall m n a b xs xs' ys ys' (Γ : list eqn),
      @tree m a xs ⋈ @tree n b ys ->
      @tree m a xs' ~= @tree n b ys' ->
      steps_to ((@tree m a xs', @tree n b ys') :: Γ)
      ((xs <*> xs') ++ (ys <*> ys') ++ Γ).

Lemma steps_to_example : 
  add_O ->
  O ~= add (leaf "1") (leaf "1") ->
  steps_to 
    [(O, add (leaf "1") (leaf "1"))]
    (
      (<<>> <*> <<>>) ++
      (<<leaf "y"; leaf "y">> <*> <<leaf "1"; leaf "1">>) ++
      []
    ).
Proof.
  intros.
  apply interaction.
  - unfold add_O in H. apply H.
  - apply H0.
Qed.
