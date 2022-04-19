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
Notation "< x >" := (x <::> <<>>).
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

Check leaf "alpha".
Check tree 2 "alpha" << leaf "beta"; leaf "gamma" >>.
Fail Check tree 1 "alpha" << leaf "beta"; leaf "gamma" >>.

Fixpoint names_of_term (t : term) : list string :=
  match t with
  | leaf n => [n]
  | tree _ _ terms => 
      List.concat (Vector.to_list (Vector.map names_of_term terms))
  end.

Compute names_of_term (leaf "alpha").
Compute names_of_term (tree 2 "alpha" << leaf "beta"; leaf "gamma" >>).

(* Renaming and Substitution *)
Reserved Notation "'[' x ':=' u ']' t" (at level 60).
Fixpoint subst (t : term) (x : string) (u : term) : term :=
  match t with
  | leaf n =>
      if eqb_string n x then
        u
      else
        t
  | tree arity agent terms =>
      tree arity agent (Vector.map (fun t =>
        [x := u] t
      ) terms)
  end
where "'[' x ':=' u ']' t" := (subst t x u).

Compute ["x" := leaf "y"] (leaf "x").
Compute ["x" := tree 2 "x" << leaf "y"; leaf "z" >>] (
  tree 2 "alpha" <<
    leaf "x";
    tree 3 "beta" <<
      leaf "x";
      leaf "y";
      leaf "z"
    >>
  >>
).

(* Rules *)
Axiom rule : relation term.
Definition interacts_with (t1 : term) (t2 : term) : Prop := rule t1 t1.

Notation "t1 '⋈' t2" := (interacts_with t1 t2) (at level 60, right associativity).

Check (leaf "alpha") ⋈ (leaf "beta").
Check (tree 2 "alpha" << leaf "beta"; leaf "gamma" >>) ⋈ (leaf "beta").
Check [ (leaf "alpha") ⋈ (leaf "beta");
        (tree 2 "alpha" << leaf "beta"; leaf "gamma" >>) ⋈ (leaf "beta")
      ].
  

(* Equations *)
Definition eqn (X : Type) : Type := X -> X -> Prop.

(* Configurations *)
Record conf : Type := mkconf {
  interface : list term;
  equations: list (eqn term);
}.

(* Interaction rules *)
(* TODO *)

(* Nets *)
(* TODO *)

(* Steps-to relation on configurations *)
(*
Inductive steps_to : conf -> conf -> Prop :=
  | interaction
  | indirection
  | collect
  | multiset.
*)
