Require Import Program.Basics.
Require Import FunctionalExtensionality.
Require Import Background.
Require Import Towards.


(* stateT *)

Record stateT (S : Type) (m : Type -> Type) `{Monad m} (A : Type) := mkStateT
{ runStateT : S -> m (A * S)%type }.
Arguments mkStateT [S m _ _ A].
Arguments runStateT [S m _ _ A].

Instance Functor_stateT (S : Type) (m : Type -> Type)
                       `{Monad m} : Functor (stateT S m) :=
{ fmap _ _ f sa := mkStateT (fun s =>
    fmap (fun pair => (f (fst pair), snd pair)) (runStateT sa s))
}.

Instance FunctorLaws_stateT (S : Type) (m : Type -> Type)
                            {f : Functor m}
                            {fl : @FunctorLaws m f}
                            {M : @Monad m f} : FunctorLaws (stateT S m).
Proof.
  destruct fl.
  constructor; simpl; intros.

  - destruct fa.
    simpl.
    unwrap_layer.
    assert (G : (fun pair : A * S => (id (fst pair), snd pair)) = id).
    { apply functional_extensionality. intros. now destruct x0. }
    rewrite G.
    auto.

  - unfold Basics.compose.
    unwrap_layer.
    simpl.
    assert (G : (fun pair : A * S => (g (h (fst pair)), snd pair)) =
                ((fun pair => (g (fst pair), snd pair)) ∘ (fun pair => (h (fst pair), snd pair)))).
    { auto. }
    rewrite G.
    rewrite <- functor_comp.
    auto.
Qed.

Instance Monad_stateT (S : Type) (m : Type -> Type)
                     `{Monad m} : Monad (stateT S m) :=
{ ret _ x       := mkStateT (fun s => ret (x, s))
; bind _ _ mx f := mkStateT (fun s => runStateT mx s >>=
                                      (fun p => runStateT (f (fst p)) (snd p)))
}.

Instance MonadLaws_stateT (S : Type) (m : Type -> Type)
                         `{MonadLaws m} : MonadLaws (stateT S m).
Proof.
  destruct H1.
  constructor; simpl; intros; try unwrap_layer; auto.

  - (* left id *)
    rewrite (functional_extensionality_1
      (fun s => ret (a, s) >>= (fun p : A * S => runStateT (f (fst p)) (snd p)))
      (runStateT (f a))
      (fun s => left_id _ _ _ _)).
    destruct (f a).
    auto.

  - (* right id *)
    destruct ma.
    unwrap_layer.
    simpl.
    assert (G : forall A B (p : A * B), ret (fst p, snd p) = ret p).
    { now destruct p. }
    rewrite (monadic_extensionality_1
      (fun p => ret (fst p, snd p)) _ (fun _ => G _ _ _)).
    auto.

  - (* functor_rel *)
    rewrite functor_rel.
    auto.
Qed.

Instance MonadState_stateT (S : Type) (m : Type -> Type)
                          `{Monad m} : MonadState S (stateT S m) :=
{ get    := mkStateT (fun s => ret (s, s))
; put s' := mkStateT (fun _ => ret (tt, s'))
}.

Instance MonadStateLaws_stateT (S : Type) (m : Type -> Type)
                              `{MonadLaws m} : MonadStateLaws S (stateT S m).
Proof.
  destruct H1.
  constructor; simpl; intros.

  - (* get_get *)
    unwrap_layer.
    now repeat rewrite left_id.

  - (* get_put *)
    unwrap_layer.
    now rewrite left_id.

  - (* put_get *)
    now repeat rewrite left_id.

  - (* put_put *)
    now rewrite reta_gtgt_retb_is_retb.
Qed.


(* Monadic lenses *)

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
  (* too much restrictive *)
; mupdate_mupdate : forall s a1 a2,
                           mupdate mln s a1 >>= (fun s' => mupdate mln s' a2) =
                           mupdate mln s a2
}.


(* Connection between lens algebras and monadic lenses *)

Definition mLens_2_lensAlgStateT {S A m} `{Monad m}
                                 (mln : mLens S A m) : lensAlg (stateT S m) A :=
{| view      := mkStateT (fun s => ret (mview mln s, s))
;  update a' := mkStateT (fun s => fmap (fun s' => (tt, s')) (mupdate mln s a'))
|}.

Theorem mLens_induces_lensAlgStateT :
    forall {S A m}
           {f : Functor m}
           {fl : @FunctorLaws m f}
           {M : @Monad m f}
           {ml : @MonadLaws m f M}
           (mln : mLens S A m),
           mLensLaws mln ->
           lensAlgLaws (mLens_2_lensAlgStateT mln).
Proof.
  intros.
  destruct fl.
  destruct ml.
  destruct H.
  constructor; simpl; intros; unwrap_layer.

  - (* get_get *)
    now repeat rewrite left_id.

  - (* get_put *)
    rewrite left_id.
    simpl.
    rewrite mview_mupdate0.
    rewrite functor_rel.
    now rewrite left_id.

  - (* put_get *)
    repeat rewrite assoc.
    rewrite <- (functor_rel _ _
                  (fmap (fun s' : S => (tt, s')) (mupdate mln x s))
                  (fun pair => (mview mln (snd pair), snd pair))).
    unfold compose in *.
    rewrite (functor_comp _ _ _
               (fun s' : S => (tt, s'))
               (fun pair : unit * S => (mview mln (snd pair), snd pair))
               (mupdate mln x s)).
    simpl.
    repeat rewrite functor_rel.
    rewrite (mupdate_mview0 _ (fun s a => ret (a, s)) _ _).
    rewrite assoc.
    unwrap_layer.
    now rewrite left_id.

  - (* put_put *)
    repeat rewrite functor_rel.
    unfold compose.
    rewrite assoc.
    rewrite (monadic_extensionality_1
      (fun s => ret (tt, s) >>= 
                (fun p => fmap (fun s' : S => (tt, s')) (mupdate mln (snd p) s2)))
      _
      (fun _ => left_id _ _ _ _)).
    rewrite (monadic_extensionality_1
      (fun s : S => fmap (fun s' : S => (tt, s')) (mupdate mln s s2))
      _
      (fun _ => functor_rel _ _ _ _)).
    unfold compose.
    rewrite <- assoc.
    now rewrite mupdate_mupdate0.
Qed.


(* bx *)

Record BX (m : Type -> Type) (A B : Type) := mkBX
{ getL : m A
; getR : m B
; putL : A -> m unit
; putR : B -> m unit
}.
Arguments mkBX [m A B].

Definition lens_2_bx {S A} (ln : lens S A) : BX (state S) S A :=
  mkBX (mkState (fun s => (s, s)))
       (mkState (fun s => (Background.view ln s, s)))
       (fun s' => mkState (fun _ => (tt, s')))
       (fun a' => mkState (fun s => (tt, Background.update ln s a'))).

Definition mLens_2_bx {S A m} `{Monad m} (mln : mLens S A m) : BX (stateT S m) S A :=
  mkBX (mkStateT (fun s => ret (s, s)))
       (mkStateT (fun s => ret (mview mln s, s)))
       (fun s' => mkStateT (fun _ => ret (tt, s')))
       (fun a' => mkStateT (fun s => mupdate mln s a' >>= (fun s' => ret (tt, s')))).


(* profunctor lenses *)

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

Record indexedStateT S1 S2 m A `{Monad m} := mkIndexedStateT
{ runIndexedStateT : S1 -> m (A * S2)%type }.
Arguments mkIndexedStateT [S1 S2 m A _ _].
Arguments runIndexedStateT [S1 S2 m A _ _].

Definition indexedStateT_X m `{Monad m} X : Type -> Type -> Type :=
  fun S1 S2 => indexedStateT S1 S2 m X.

Instance Profunctor_indexedStateT m `{Monad m} X : Profunctor (indexedStateT_X m X) :=
{ dimap _ _ _ _ f g h := 
    mkIndexedStateT (fun a' => 
      fmap (fun pair => (fst pair, g (snd pair))) (runIndexedStateT h (f a')))
}.

Instance ProfunctorLaws_indexedStateT m 
                                      {f : Functor m}
                                      {fl : @FunctorLaws m f}
                                      {M : @Monad m f}
                                      {ml : @MonadLaws m f M}
                                      X : ProfunctorLaws (indexedStateT_X m X).
Proof.
  destruct fl.
  split; simpl; intros.
  
  - (* id *)
    destruct h.
    unfold id.
    unwrap_layer.
    simpl.
    assert (H : (fun pair : X * B => (fst pair, snd pair)) = id).
    { functional_extensionality_i. now destruct x0. }
    rewrite H.
    now rewrite functor_id. 

  - (* assoc *)
    unfold compose.
    functional_extensionality_i.
    unwrap_layer.
    simpl.
    unfold compose in functor_comp.
    now rewrite functor_comp.
Qed.

Instance Cartesian_indexedStateT m `{Monad m} X : Cartesian (indexedStateT_X m X) :=
{ first  _ _ _ h := 
    mkIndexedStateT (fun pair => fmap (fun pair' => (fst pair', (snd pair', snd pair))) 
                                      (runIndexedStateT h (fst pair)))
; second _ _ _ h :=
    mkIndexedStateT (fun pair => fmap (fun pair' => (fst pair', (fst pair, snd pair'))) 
                                      (runIndexedStateT h (snd pair)))
}.

Instance CartesianLaws_indexedStateT m 
                                     {f : Functor m}
                                     {fl : @FunctorLaws m f}
                                     {M : @Monad m f}
                                     {ml : @MonadLaws m f M} X : CartesianLaws (indexedStateT_X m X).
Proof.
    split; simpl; intros.

  - (* id *)
    unwrap_layer.
    destruct x.
    now destruct u.

  - (* assoc *)
    unwrap_layer.
    destruct x.
    destruct p.
    simpl.
    destruct fl.
    unfold compose in functor_comp.
    now repeat rewrite functor_comp.
Qed.

Definition pLens S T A B := forall p `{Cartesian p}, p A B -> p S T.

Definition lens'' S A := pLens S S A A.
