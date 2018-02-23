Require Import Program.Basics.
Require Import FunctionalExtensionality.
Require Import Strings.String.
Require Import Background.


(* `MonadState_state` is `identityLn` *)

Definition MonadState_state_2_lens A : lens A A :=
  mkLens (fun a => evalState get a) (fun a a' => execState (put a') a).

Lemma MonadState_state_is_identity_lens : forall A,
    MonadState_state_2_lens A = identityLn A.
Proof. auto. Qed.


(* Broadly, `MonadState` generalizes `lens` *)

Definition ms_2_lens {S A} (ms : MonadState A (state S)) : lens S A :=
{| view s     := evalState get s
;  update s a := execState (put a) s
|}.

Instance lens_2_ms {S A} (ln : lens S A) : MonadState A (state S) :=
{ get   := mkState (fun s => (view ln s, s))
; put a := mkState (fun s => (tt, update ln s a))
}.

Theorem ms_iso_lens : forall {S A} 
                             (ln : lens S A)
                             (ms : MonadState A (state S)),
    lensLaws ln ->
    @MonadStateLaws _ _ _ ms ->
    ((ms_2_lens ∘ lens_2_ms) ln = ln) /\ 
    ((lens_2_ms ∘ ms_2_lens) ms = ms).
Proof.
  unfold ms_2_lens. unfold lens_2_ms. 
  unfold compose.
  intros.
  split; simpl.

  - (* ms_2_lens ∘ lens_2_ms *)
    destruct ln.
    auto.

  - (* lens_2_ms ∘ ms_2_lens *)
    assert (G0 : (fun s : S => (evalState get s, s)) =
                 (fun s : S => (evalState get s, execState get s))).
    { functional_extensionality_i.
      apply f_equal.
      now rewrite get_leaves_s_as_is. }
    rewrite G0.
    destruct ms.
    simpl.
    assert (G1 : 
      {| runState := fun s : S => (evalState get s, execState get s) |} = get).
    { destruct get.
      unfold evalState. unfold execState.
      unwrap_layer.
      simpl.
      now destruct (runState x). }
    rewrite G1.
    assert (G2 : 
      (fun a : A => {| runState := fun s : S => (tt, execState (put a) s) |}) = put).
    { functional_extensionality_i.
      destruct (put x).
      unwrap_layer.
      unfold execState.
      simpl.
      destruct (runState x0).
      now destruct u. }
    now rewrite G2.
Qed.

Theorem MonadState_state_s_induces_lens : 
    forall {S A : Type} (ms : MonadState A (state S)),
           @MonadStateLaws A (state S) _ ms -> lensLaws (ms_2_lens ms).
Proof.
  intros.
  unfold ms_2_lens.
  assert (F : forall s, put (evalState get s) = get >> put (evalState get s)).
  { intros.
    rewrite <- (non_eff_get (put (evalState get s))).
    now rewrite (general_getget (fun _ => put (evalState get s))). }
  destruct H.
  constructor; intros; simpl.

  - (* view_update *)
    rewrite F.
    rewrite <- execexec_is_execgtgt.
    rewrite execevalexec_is_execbind.
    now rewrite get_put.

  - (* update_view *)
    rewrite execeval_is_evalgtgt.
    rewrite put_get.
    now rewrite eval_ma_gtgt_retx_is_x.

  - (* updte_update *)
    rewrite execexec_is_execgtgt.
    now rewrite put_put.
Qed.

Theorem lens_induces_MonadState_state_s :
    forall {S A : Type} (ln : lens S A),
           lensLaws ln -> @MonadStateLaws A (state S) _ (lens_2_ms ln).
Proof.
  intros.
  destruct H.
  split; 
    simpl; 
    intros; 
    repeat state_reason; 
    [rewrite view_update | rewrite update_view | rewrite update_update];
    auto.
Qed.


(* Lens Algebra definition, just a record *)

Record lensAlg (p : Type -> Type) (A : Type) `{M : Monad p} : Type :=
{ view : p A
; update : A -> p unit
; modify (f : A -> A) : p unit := view >>= (update ∘ f)
}.
Arguments view [p A _].
Arguments update [p A _].
Arguments modify [p A _].
Notation "ln ~ f" := (modify ln f) (at level 40, no associativity).

Record lensAlgLaws {p A} `{Monad p} (ln : lensAlg p A) : Type :=
{ view_view : view ln >>= (fun s1 => view ln >>= (fun s2 => ret (s1, s2))) =
              view ln >>= (fun s => ret (s, s))
; view_update : view ln >>= update ln = ret tt
; update_view : forall s, update ln s >> view ln = update ln s >> ret s
; update_update : forall s1 s2, update ln s1 >> update ln s2 = update ln s2
}.

Lemma general_viewview : 
    forall {p : Type -> Type} {A X : Type}
          `{ml : MonadLaws p}
           (ln : lensAlg p A)
           (lnl : lensAlgLaws ln)
           (k : A * A -> p X),
           view ln >>= (fun x1 => view ln >>= (fun x2 => k (x1, x2))) = 
           view ln >>= (fun x1 => k (x1, x1)).
Proof.
  intros.
  destruct ml.
  destruct lnl.
  assert (G : view ln >>= (fun x1 : A => k (x1, x1)) =
              view ln >>= (fun x1 : A => ret (x1, x1) >>= k)).
  { unwrap_layer. now rewrite left_id. }
  rewrite G.
  rewrite <- assoc.
  rewrite <- view_view0.
  rewrite -> assoc.
  unwrap_layer.
  rewrite -> assoc.
  unwrap_layer.
  now rewrite left_id.
Qed.

Lemma non_eff_view : 
    forall  {p : Type -> Type} {A}
           `{ml : MonadLaws p}
            (ln : lensAlg p A)
            (lnl : lensAlgLaws ln)
            {X}
            (k : p X),
    view ln >> k = k.
Proof.
  intros.
  pose proof (@general_viewview p A X H ml ln lnl) as J.
  destruct ml.
  destruct lnl.
  rewrite <- (left_id unit _ tt (fun _ => k)).
  rewrite <- view_update0.
  repeat rewrite assoc.
  now rewrite (J (fun pair => update ln (snd pair) >> k)).
Qed.


(* Zip example *)

Record Address (p : Type -> Type) `{Monad p} := mkAddress
{ zip  : lensAlg p nat
; city : lensAlg p string
}.
Arguments zip [p _].
Arguments city [p _].

Definition modifyZip (f : nat -> nat) 
                     {p} `{Monad p} (data : Address p) : p unit :=
  (zip data) ~ f.

Definition getCity {p} `{Monad p} (data : Address p) : p string :=
  view (city data).
