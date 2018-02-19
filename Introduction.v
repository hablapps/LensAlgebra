Require Import Program.Basics. 
Require Import Strings.String.
Require Import Background.

Open Scope program_scope.


(******************)
(* Optic approach *)
(******************)

(* Data layer *)

Record address := mkAddress
{ zip : nat
; region : option string
}.

Definition zipLn : lens address nat :=
  mkLens zip (fun a z' => mkAddress z' (region a)).

Definition regionLn : lens address (option string) :=
  mkLens region (mkAddress ∘ zip).


(* Business logic *)

Definition modifyZip (f : nat -> nat) : address -> address :=
  zipLn %~ f.

Definition modifyRegion (f : string -> string) : address -> address :=
  (regionLn ▶ somePr) ?~ f.


(**********************)
(* Algebraic approach *)
(**********************)

(* Ad hoc algebras *)

Class Address (p : Type -> Type) `{Monad p} :=
{ getZip : p nat
; modZip (f : nat -> nat) : p unit
; getRegion : p (option string)
; modRegion (f : string -> string) : p unit
}.

Class Address' (p : Type -> Type) `{Monad p} :=
{ zip' : MonadState nat p
; getRegion' : p (option string)
; modRegion' (f : string -> string) : p unit
}.

Definition modifyZip' {p} `{Address' p} (f : nat -> nat) : p unit :=
  @modify _ _ _ zip' f.
