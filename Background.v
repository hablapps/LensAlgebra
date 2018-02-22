Require Import Program.Basics.
Require Import FunctionalExtensionality.

Open Scope program_scope.


(***************)
(* Typeclasses *)
(***************)

(* Natural Transformation *)

Class natTrans (f g : Type -> Type) : Type := mkNatTrans
{ runNatTrans {X} : f X -> g X }.
Arguments mkNatTrans [f g].
Arguments runNatTrans [f g] _ [X].
Notation "f ~> g" := (natTrans f g) (at level 50, left associativity).

Definition composeNT {f g h : Type -> Type} 
                     (nt1 : g ~> h) (nt2 : f ~> g) : f ~> h :=
  mkNatTrans (fun _ fx => runNatTrans nt1 (runNatTrans nt2 fx)).
Notation "f • g" := (composeNT f g) (at level 40, left associativity).

(* Monad *)

Class Monad (m : Type -> Type) : Type :=
{ ret : forall {X}, X -> m X
; bind : forall {A B}, m A -> (A -> m B) -> m B
}.
Notation "ma >>= f" := (bind ma f) (at level 50, left associativity).
Notation "ma >> mb" := (ma >>= fun _ => mb) (at level 50, left associativity).

Class MonadLaws (m : Type -> Type) `{Monad m} :=
{ left_id : forall {A B} (a : A) (f : A -> m B), ret a >>= f = f a
; right_id : forall {A} (ma : m A), ma >>= ret = ma
; assoc : forall {A B C} (ma : m A) (f : A -> m B) (g : B -> m C),
                 ma >>= f >>= g = ma >>= (fun x => f x >>= g)
}.

Definition monad_morphism {f g : Type -> Type} 
                         `{Monad f, Monad g} 
                          (morph : f ~> g) : Prop :=
  (forall X (x : X), runNatTrans morph (ret x) = ret x) /\
  (forall A B (fa : f A) (f : A -> f B),
    runNatTrans morph (fa >>= f) = 
    runNatTrans morph fa >>= (fun a => runNatTrans morph (f a))).

(* MonadState *)

Class MonadState (A : Type) (m : Type -> Type) `{Monad m} :=
{ get : m A
; put : A -> m unit
; modify : (A -> A) -> m unit := fun f => get >>= (put ∘ f)
}.

Class MonadStateLaws (A : Type) (m : Type -> Type) `{MonadState A m} :=
{ get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2
}.

Ltac unwrap_layer := 
  apply f_equal;
  apply functional_extensionality;
  intros.

Lemma general_getget : 
    forall {M : Type -> Type} {A : Type}
          `{MSL : MonadStateLaws A M} {ML : MonadLaws M} {X : Type} 
           (p : A * A -> M X),
           get >>= (fun x1 => get >>= (fun x2 => p (x1, x2))) = 
           get >>= (fun x1 => p (x1, x1)).
Proof.
  intros.
  destruct ML.
  destruct MSL.
  assert (G : get >>= (fun x1 : A => p (x1, x1)) =
              get >>= (fun x1 : A => ret (x1, x1) >>= p)).
  { unwrap_layer. now rewrite left_id0. }
  rewrite G.
  rewrite <- assoc0.
  rewrite <- get_get0.
  rewrite -> assoc0.
  unwrap_layer.
  rewrite -> assoc0.
  unwrap_layer.
  now rewrite left_id0.
Qed.

Lemma non_eff_get : 
    forall  {m : Type -> Type} {A : Type}
           `{M : Monad m}
            {ML : @MonadLaws m M}
            {MS : @MonadState A m M}
            {MSL : @MonadStateLaws A m M MS} {X : Type} (p : m X),
    get >> p = p.
Proof.
  intros.
  pose proof (@general_getget m A M MS MSL ML) as J.
  destruct ML.
  destruct MSL.
  rewrite <- (left_id0 unit _ tt (fun _ => p)).
  rewrite <- get_put0.
  repeat rewrite assoc0.
  now rewrite (J X (fun pair => put (snd pair) >> p)).
Qed.


(*********)
(* State *)
(*********)

Record state (S A : Type) := mkState
{ runState : S -> A * S }.
Arguments mkState [S A].
Arguments runState [S A].

Definition evalState {S A} (st : state S A) (s : S) : A :=
  fst (runState st s).

Definition execState {S A} (st : state S A) (s : S) : S :=
  snd (runState st s).

Ltac state_reason :=
  match goal with
  | [ |- context [bind _]] => unfold bind
  | [ |- context [execState] ] => unfold execState
  | [ |- context [evalState] ] => unfold evalState
  | [ |- {| runState := _ |} = {| runState := _ |} ] => apply f_equal
  | [ |- (fun _ => _) = _ ] => apply functional_extensionality; intros
  | [ |- {| runState := _ |} = ?x ] => destruct x as [rs]
  | [ |- context [ let (_, _) := ?rs ?x in _ ] ] => destruct (rs x)
  end; simpl; auto.

Ltac i_state_reason := intros; repeat state_reason.

Instance Monad_state {S : Type} : Monad (state S) :=
{ ret := fun X x => mkState (fun s => (x, s))
; bind := fun A B m f => mkState (fun s => let (a, s') := runState m s
                                           in runState (f a) s')
}.

Instance MonadLaws_state {S : Type} : MonadLaws (state S).
Proof.
  constructor; intros; repeat state_reason.
Qed.

Instance MonadState_state {S : Type} : MonadState S (state S) :=
{ get := mkState (fun s => (s, s))
; put := fun s => mkState (fun _ => (tt, s))
}.

Instance MonadStateLaws_state {S : Type} : MonadStateLaws S (state S).
Proof. constructor; auto. Qed.

Lemma execexec_is_execgtgt : 
    forall {S A B} (s : S) (st1 : state S A) (st2 : state S B),
           execState st2 (execState st1 s) = execState (st1 >> st2) s.
Proof. i_state_reason. Qed.

Lemma execeval_is_evalgtgt :
    forall {S A B} (s : S) (st1 : state S A) (st2 : state S B),
           evalState st2 (execState st1 s) = evalState (st1 >> st2) s.
Proof. i_state_reason. Qed.

Lemma execevalexec_is_execbind :
    forall {S A B} (s : S) (st1 : state S A) (f : A -> state S B),
           execState (f (evalState st1 s)) (execState st1 s) = 
           execState (st1 >>= f) s.
Proof. i_state_reason. Qed.

Lemma eval_ma_gtgt_retx_is_x : 
    forall {S A X} (m : state S A) (s : S) (x : X),
           evalState (m >> ret x) s = x.
Proof. i_state_reason. Qed.

Lemma exec_ma_gtgt_retx_is_exec_ma :
    forall {S A X} (m : state S A) (s : S) (x : X),
           execState (m >> ret x) s = execState m s.
Proof. i_state_reason. Qed.

Lemma exec_ret_is_s :
    forall {S X} (s : S) (x : X),
           execState (ret x) s = s.
Proof. i_state_reason. Qed.

Theorem get_leaves_s_as_is : 
    forall {S A}
           {ms : MonadState A (state S)} 
           {msl : @MonadStateLaws A (state S) _ ms} (s : S),
           execState get s = s.
Proof.
  intros.
  rewrite <- (exec_ret_is_s s tt).
  assert (G : execState get (execState (ret tt) s) =
              execState get s).
  { now rewrite (exec_ret_is_s s tt). }
  rewrite G.
  rewrite <- (non_eff_get (ret tt)).
  now rewrite exec_ma_gtgt_retx_is_exec_ma.
Qed.


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

Record lensLaws {S A} (ln : lens S A) : Type :=
{ view_update : forall s, update ln s (view ln s) = s
; update_view : forall s a, view ln (update ln s a) = a
; update_update : forall s a1 a2, update ln (update ln s a1) a2 = update ln s a2
}.

Definition composeLn {S A B} (ln1 : lens S A) (ln2 : lens A B) : lens S B := 
  mkLens ((view ln2) ∘ (view ln1)) 
         (fun s => update ln1 s ∘ update ln2 (view ln1 s)).
Notation "ln1 ▷ ln2" := (composeLn ln1 ln2) (at level 40, left associativity).

Definition modifyLn {S A} (ln : lens S A) (f : A -> A) : S -> S :=
  fun s => update ln s (f (view ln s)).
Notation "ln %~ f" := (modifyLn ln f) (at level 40, no associativity).

Definition identityLn A : lens A A := 
  mkLens id (fun _ => id).


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


(* Utilities to deal with functional extensionality and monads *)

Ltac functional_extensionality_i := apply functional_extensionality; intros.

Theorem monadic_extensionality_1 : forall {m A B} `{Monad m}
                           {ma : m A} 
                           (f : A -> m B)
                           (g : A -> m B), 
    (forall (a : A), f a = g a) -> (ma >>= f = ma >>= g).
Proof.
  intros.
  unwrap_layer.
  auto.
Qed.

Theorem monadic_extensionality_2 : forall {m A B C} `{Monad m}
                           {ma : m A} {f : A -> m B} 
                           (k1 : A * B -> m C)
                           (k2 : A * B -> m C), 
    (forall (a : A) (b : B), k1 (a, b) = k2 (a, b)) ->
    (ma >>= (fun a => f a >>= (fun b => k1 (a, b))) =
     ma >>= (fun a => f a >>= (fun b => k2 (a, b)))).
Proof.
  intros.
  repeat unwrap_layer.
  auto.
Qed.
