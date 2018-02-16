Require Import Coq.Program.Basics. 

Open Scope program_scope.


(**********)
(* Optics *)
(**********)

(* Lens datatype and definitions *)

Record lens (S A : Type) : Type := mkLens
{ view : S -> A
; update : S -> A -> S
}.
Arguments mkLens [S A].
Arguments view [S A].
Arguments update [S A].

Definition composeLn {S A B} (ln1 : lens S A) (ln2 : lens A B) : lens S B := 
  mkLens ((view ln2) ∘ (view ln1)) 
         (fun s => update ln1 s ∘ update ln2 (view ln1 s)).
Notation "ln1 ▷ ln2" := (composeLn ln1 ln2) (at level 40, left associativity).

Definition modifyLn {S A} (ln : lens S A) (f : A -> A) : S -> S :=
  fun s => update ln s (f (view ln s)).
Notation "ln !~ f" := (modifyLn ln f) (at level 40, no associativity).


(* Prism datatype and definitions *)

Record prism (S A : Type) : Type := mkPrism
{ preview : S -> option A
; build : A -> S
}.
Arguments mkPrism [S A].
Arguments preview [S A].
Arguments build [S A].

Definition somePr {A} : prism (option A) A :=
  mkPrism id Some.


(* Affine datatype and definitions *)

Record affine (S A : Type) : Type := mkAffine
{ getOption : S -> option A
; set : S -> A -> S
}.
Arguments mkAffine [S A].
Arguments getOption [S A].
Arguments set [S A].

Definition modifyAf {S A} (af : affine S A) (f : A -> A) : S -> S :=
  fun s => match getOption af s with
            | Some a => set af s (f a)
            | none => s
           end.
Notation "af ?~ f" := (modifyAf af f) (at level 40, no associativity).


(* Heterogeneous combinators *)

Definition composeLnPr {S A B} (ln : lens S A) (pr : prism A B) : affine S B :=
  mkAffine (preview pr ∘ view ln) 
           (fun s b => match preview pr (view ln s) with
                       | Some _ => update ln s (build pr b)
                       | none => s
                       end).
Notation "ln ▶ pr" := (composeLnPr ln pr) (at level 40, left associativity).


(***************)
(* Typeclasses *)
(***************)

(* Monad *)

(* Pattern to describe `Monad` laws with a nicer notation *)
Class monad_bind (m : Type -> Type) := 
  monad_bind_ : forall {A B}, m A -> (A -> m B) -> m B.
Notation "ma >>= f" := (monad_bind_ ma f) (at level 50, left associativity).
Notation "ma >> mb" := (ma >>= fun _ => mb) (at level 50, left associativity).

Class Monad (m : Type -> Type)
            (bind : monad_bind m) : Type :=
{ ret : forall {A}, A -> m A
; left_id : forall {A B} (a : A) (f : A -> m B), ret a >>= f = f a
; right_id : forall {A} (ma : m A), ma >>= ret = ma
; assoc : forall {A B C} (ma : m A) (f : A -> m B) (g : B -> m C),
                 ma >>= f >>= g = ma >>= (fun x => f x >>= g)
}.


(* MonadState *)

Class MonadState (A : Type) (m : Type -> Type) `{Monad m} :=
{ get : m A
; put : A -> m unit
; get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2
}.
