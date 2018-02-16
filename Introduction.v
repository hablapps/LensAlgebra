Require Import Coq.Program.Basics. 
Require Import Coq.Strings.String.
Require Import Background.

Open Scope program_scope.


(* Zip Code Example *)

(******************)
(* Optic approach *)
(******************)

(* Data layer *)

Record address : Type := mkAddress
{ zip : nat
; region : option string
}.

Definition zipLn : lens address nat :=
  mkLens zip (fun a z' => mkAddress z' (region a)).

Definition regionLn : lens address (option string) :=
  mkLens region (mkAddress ∘ zip).


(* Business logic *)

Definition modifyZip (f : nat -> nat) : address -> address :=
  zipLn !~ f.

Definition modifyRegion (f : string -> string) : address -> address :=
  (regionLn ▶ somePr) ?~ f.


(**********************)
(* Algebraic approach *)
(**********************)

(* Ad hoc algebras *)

Class Address (p : Type -> Type) : Type :=
{ getZip : p nat
; modZip (f : nat -> nat) : p unit
; getRegion : p (option string)
; modRegion (f : string -> string) : p unit
}.

Class Address' (p : Type -> Type) `{Monad p} : Type :=
{ zip' : MonadState nat p
; getRegion' : p (option string)
; modRegion' (f : string -> string) : p unit
}.
