Require Import Coq.Program.Basics. 
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
{ get : p A
; put : A -> p unit
; modify (f : A -> A) : p unit := get >>= (put ∘ f)
}.
Arguments get [p A _].
Arguments put [p A _].
Arguments modify [p A _].

Record lensAlgLaws {p A} `{Monad p} (ln : lensAlg p A) : Type :=
{ get_get : get ln >>= (fun s1 => get ln >>= (fun s2 => ret (s1, s2))) =
            get ln >>= (fun s => ret (s, s))
; get_put : get ln >>= put ln = ret tt
; put_get : forall s, put ln s >> get ln = put ln s >> ret s
; put_put : forall s1 s2, put ln s1 >> put ln s2 = put ln s2
}.


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
