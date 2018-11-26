Require Import Program.Basics.
Require Import Strings.String.
Require Import Sect2.

Open Scope program_scope.


(*****************)
(* Lens approach *)
(*****************)

(* Here, we show the simplified version of the university example, which only
   requires lenses (Sect. 3.1). The traversal-based example serves us as
   motivation to introduce the rich set of optic abstractions, but doesn't add
   value to the rest of the paper. *)

(* Data layer *)

Record department := mkDepartment
{ budget : nat }.

Record university := mkUniversity
{ name : string
; mathDep : department
}.

Definition budgetLn : lens department nat :=
  mkLens budget (fun _ b' => mkDepartment b').

Definition mathDepLn : lens university department :=
  mkLens mathDep (fun u d' => mkUniversity (name u) d').

(* Business logic *)

Definition doubleDepBudget : department -> department :=
  budgetLn %~ (fun b => b * 2).

Definition doubleUnivBudget : university -> university :=
  mathDepLn %~ doubleDepBudget.

Definition doubleUnivBudget' : university -> university :=
  (mathDepLn ▷ budgetLn) %~ (fun b => b * 2).


(*******************************)
(* Algebraic theories approach *)
(*******************************)

(* Repository algebras *)

Class UniversityAlg (p : Type -> Type) :=
{ getName : p string
; modifyName (f : string -> string) : p unit
; getMathDep : p department
; modifyMathDep (f : department -> department) : p unit
(* ... *)
}.

