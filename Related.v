Set Warnings "-notation-overridden,-parsing".
Require Import Program.Basics.
Require Import FunctionalExtensionality.
Require Import Background.


(*********************)
(* Profunctor Lenses *)
(*********************)

Class Profunctor (p : Type -> Type -> Type) :=
{ dimap : forall A A' B B', (A' -> A) -> (B -> B') -> p A B -> p A' B' }.
Arguments dimap [p] [_] [_ _ _ _].

Class ProfunctorLaws (p : Type -> Type -> Type) `{Profunctor p} :=
{ profunctor_id : forall A B (h : p A B), dimap id id h = id h
; profunctor_assoc : forall A A' A'' B B' B'' 
                            (f : A'' -> A') (f' : A' -> A)
                            (g : B' -> B'') (g' : B -> B'), 
                            dimap (f' ∘ f) (g ∘ g') = dimap f g ∘ dimap f' g'
}.

Class Cartesian (p : Type -> Type -> Type) `{Profunctor p} :=
{ first  : forall A B C, p A B -> p (A * C)%type (B * C)%type
; second : forall A B C, p A B -> p (C * A)%type (C * B)%type
}.
Arguments first [p _] [_] [_ _ _].
Arguments second [p _] [_] [_ _ _].

Definition runit  {A} (a1 : A * unit) : A := fst a1.
Definition runit' {A} (a : A) : A * unit := (a, tt).
Definition assoc  {A B C} (a_bc : A * (B * C)) : (A * B) * C :=
  match a_bc with | (a, (b, c)) => ((a, b), c) end.
Definition assoc' {A B C} (ab_c : (A * B) * C) : A * (B * C) :=
  match ab_c with | ((a, b), c) => (a, (b, c)) end.

Class CartesianLaws (p : Type -> Type -> Type) `{Cartesian p} :=
{ cartesian_id    : forall A B (h : p A B), 
                           dimap runit runit' h = first h
; cartesian_assoc : forall A B C (h : p A A),
                           dimap (@assoc A B C) assoc' (first (first h)) = first h
}.

Definition pLens S T A B := forall p `{Cartesian p}, p A B -> p S T.

Definition lens'' S A := pLens S S A A.


(******************)
(* Monadic lenses *)
(******************)

Record mLens (S A : Type) (m : Type -> Type) `{Monad m} := mkMLens
{ mview : S -> A
; mupdate : S -> A -> m S
}.
Arguments mview [S A m _ _].
Arguments mupdate [S A m _ _].
Arguments mkMLens [S A m _ _].

Record mLensLaws {S A m} `{Monad m} (mln : mLens S A m) := mkMLensLaws
{ mview_mupdate : forall s, mupdate mln s (mview mln s) = ret s
; mupdate_mview : forall B (k : S -> A -> m B) s a,
                         mupdate mln s a >>= (fun s' => k s' (mview mln s')) =
                         mupdate mln s a >>= (fun s' => k s' a)
}.


(**************************)
(* Entangled State Monads *)
(**************************)

Record BX (m : Type -> Type) (A B : Type) := mkBX
{ getL : m A
; getR : m B
; putL : A -> m unit
; putR : B -> m unit
}.
