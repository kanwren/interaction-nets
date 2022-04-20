Require Import Coq.Strings.String.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Sorting.Permutation.
Require Vector.
Import List.ListNotations.

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

Definition names_of_terms (ts : list term) : list string :=
  List.flat_map names_of_term ts.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

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
  | rule : forall t1 t2, interacts_with t1 t2
  | interacts_with_symm : 
      forall t1 t2,
      interacts_with t1 t2 -> interacts_with t2 t1.
Notation "t1 '⋈' t2" := (interacts_with t1 t2) (at level 60, right associativity).

Check (leaf "alpha") ⋈ (leaf "beta").
Check (tree "alpha" << leaf "beta"; leaf "gamma" >>) ⋈ (leaf "beta").
  
(* Define some terms *)
Definition x := leaf "x".
Definition y := leaf "y".
Definition z := leaf "z".
Definition t := leaf "t".
Definition a := leaf "a".

(* Define some agents *)
(* Note: The steps_to relation only supports interaction between trees.
 * Therefore any agent must be defined as a tree. "O", for example, is defined as a tree that takes in zero terms (the empty vector) *)
Definition O := tree "O" (<<>>).
Definition S (n : term) := tree "S" <<n>>.
Definition add (x : term) (y : term) := tree "add" << x ; y >>.

Definition add_O := add x x ⋈ O.
Definition add_S := add (S x) y ⋈ S (add x y).

(* Define multi step relation *)
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall x, multi R x x
  | multi_step :
      forall x y z,
      R x y ->
      multi R y z ->
      multi R x z.

Definition eqn : Type := term * term.

Inductive eqns_equiv : list eqn -> list eqn -> Prop :=
  | eqns_perm :
      forall xs ys,
      Permutation xs ys -> eqns_equiv xs ys
  | eqn_symm :
      forall x y xs,
      eqns_equiv ((x,y) :: xs) ((y,x) :: xs).
Notation "xs ≡ ys" := (eqns_equiv xs ys) (at level 60, right associativity).
Notation "xs ≡* ys" := ((multi eqns_equiv) xs ys) (at level 60, right associativity).

Example eqn_equiv_example: [(x, y); (z, t)] ≡ [(z, t); (x, y)].
Proof.
  apply eqns_perm.
  apply perm_swap.
Qed.

Fixpoint combine_vecs_to_list {X : Type} {n : nat} (a : VectorDef.t X n)
  (b : VectorDef.t X n) :=
  let xs := Vector.to_list a in
  let ys := Vector.to_list b in
  List.combine xs ys.

Notation "xs <*> ys" := (combine_vecs_to_list xs ys) (at level 60, right associativity).

Record net := mknet {
  iface : list term;
  eqns  : list eqn;
}.
Notation "'<%' iface | eqns '%>'" := (
    {| iface := iface; eqns := eqns |}
  ) (at level 60, right associativity).

Reserved Notation "n '-->' n'" (at level 40).
Inductive steps_to : net -> net -> Prop :=
  | interaction :
      forall m n a b xs xs' ys ys' Γ iface,
      @tree m a xs ⋈ @tree n b ys ->
      <% iface | (@tree m a xs', @tree n b ys') :: Γ %> -->
      <% iface | (xs <*> xs') ++ (ys <*> ys') ++ Γ %>
  | indirection :
      forall x u v t Γ iface,
      List.In x (names_of_term u) ->
      <% iface | [(leaf x, t); (u, v)] ++ Γ %> -->
      <% iface | [([[x := t]] u, v)] ++ Γ %>
  | collect :
      forall x u Γ iface,
      List.In x (names_of_terms iface) ->
      <% iface | (leaf x,u) :: Γ %> -->
      <% List.map (fun t => [[x := u]] t) iface | Γ %>
  | multiset :
      forall t1 t2 Θ Θ' Δ Δ',
      Θ ≡* Θ' ->
      (<% t1 | Θ' %> --> <% t2 | Δ' %>) ->
      Δ' ≡* Δ ->
      (<% t1 | Θ %> --> <% t2 | Δ %>)
where "n '-->' n'" := (steps_to n n').

Notation "n '-->*' n'" := ((multi steps_to) n n') (at level 40).

Lemma steps_to_example :
  add_O -> add_S ->
  <% [ a ] | [(add a O, S O)] %> -->*
  <% [S O] | [] %>.
Proof.
  intros H1 H2.
  eapply multi_step.
  apply interaction.
  apply H2.
  simpl.
  eapply multi_step.
  - apply multiset with
      (Θ' := [(y, O); (add x y, O); (S x, a)])
      (Δ' := [([["y" := O]] (add x y), O); (S x, a)]).
    + eapply multi_step.
      apply eqns_perm.
      apply perm_swap.
      eapply multi_step.
      apply eqns_perm.
      apply perm_skip.
      apply perm_swap.
      apply multi_refl.
    + change [(y, O); (add x y, O); (S x, a)] with 
        ([(y, O); (add x y, O)] ++ [(S x, a)]).
      change [([["x" := y]] add x y, O); (S x, a)] with
        ([([["x" := y]] add x y, O)] ++ [(S x, a)]).
      apply indirection.
      simpl.
      right.
      left.
      reflexivity.
    + apply multi_refl.
  - eapply multi_step.
    apply multiset with
      (Θ' := [(a, S x); ([["y" := O]] (add x y), O) ])
      (Δ' := [(add x O, O)]).
    + eapply multi_step.
      apply eqns_perm.
      apply perm_swap.
      eapply multi_step.
      apply eqn_symm.
      apply multi_refl.
    + apply collect with (Γ := [([["y" := O]] add x y, O)]). 
      simpl.
      left.
      reflexivity.
    + apply multi_refl.
    + simpl.
      eapply multi_step.
      apply interaction.
      apply H1.
      simpl.
      eapply multi_step.
      apply indirection.
      simpl.
      left. reflexivity.
      simpl.
      eapply multi_step.
      apply collect.
      simpl.
      left. reflexivity.
      simpl.
      eapply multi_refl.
Qed.
      
      
    
    
