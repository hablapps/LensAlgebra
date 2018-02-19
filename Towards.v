Require Import Coq.Program.Basics. 
Require Import Strings.String.
Require Import Background.


(* `MonadState` generalizes `lens` *)

Definition MonadState_state_2_lens A : lens A A :=
  mkLens (fun a => evalState get a) (fun a a' => execState (put a') a).

Lemma MonadState_state_is_identity_lens : forall A,
    MonadState_state_2_lens A = identityLn A.
Proof. auto. Qed.

Definition ms_2_lens {S A} (ms : MonadState A (state S)) : lens S A :=
{| view s     := evalState get s
;  update s a := execState (put a) s
|}.

Instance lens_2_ms {S A} (ln : lens S A) : MonadState A (state S) :=
{ get   := mkState (fun s => (view ln s, s))
; put a := mkState (fun s => (tt, update ln s a))
}.

Ltac i_unfold_behavedness :=
  unfold very_well_behaved; unfold well_behaved; 
  unfold view_update; unfold update_view; unfold update_update;
  unfold get; unfold put;
  unfold ms_2_lens; unfold lens_2_ms;
  intros.

Theorem MonadState_state_s_induces_lens : 
    forall {S A : Type} (ms : MonadState A (state S)),
           @MonadStateLaws A (state S) _ ms -> very_well_behaved (ms_2_lens ms).
Proof.
  i_unfold_behavedness.
  assert (F : forall s, put (evalState get s) = get >> put (evalState get s)).
  { intros.
    rewrite <- (non_eff_get (put (evalState get s))).
    now rewrite (general_getget (fun _ => put (evalState get s))). }
  destruct H.
  repeat split; intros; simpl.

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
           very_well_behaved ln -> @MonadStateLaws A (state S) _ (lens_2_ms ln).
Proof.
  i_unfold_behavedness.
  destruct H as [[view_update update_view] update_update].
  split; 
    simpl; 
    intros; 
    repeat state_reason; 
    [rewrite view_update | rewrite update_view | rewrite update_update];
    auto.
Qed.


(* Lens Algebra definition *)

Record lensAlg (p : Type -> Type) (A : Type) `{M : Monad p} : Type :=
{ (* abstract definitions *)
  get : p A
; put : A -> p unit

  (* laws *)
; get_get : get >>= (fun s1 => get >>= (fun s2 => ret (s1, s2))) =
            get >>= (fun s => ret (s, s))
; get_put : get >>= put = ret tt
; put_get : forall s, put s >> get = put s >> ret s
; put_put : forall s1 s2, put s1 >> put s2 = put s2

  (* derived methods *)
; modify (f : A -> A) : p unit := get >>= (put ∘ f)
}.
Arguments get [p A _].
Arguments put [p A _].
Arguments modify [p A _].


(* Zip example *)

Class Address'' (p : Type -> Type) `{Monad p} :=
{ zip'' : lensAlg p nat
; getRegion'' : p (option string)
; modRegion'' (f : string -> string) : p unit
}.

Definition modifyZip (f : nat -> nat) {p} `{Address'' p} : p unit :=
  modify zip'' f.

Definition getZip {p} `{Address'' p} : p nat :=
  get zip''.
