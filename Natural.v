Require Import Program.Basics.
Require Import Background.
Require Import Towards.


(* Alternative lens algebra (or MonadState) definition *)

Definition lensAlg' (p : Type -> Type) (A : Type) :=
  state A ~> p.

Definition lensAlg'_2_lensAlg {p A} `{Monad p} 
                              (ln' : lensAlg' p A) : lensAlg p A :=
{| view := runNatTrans ln' get
;  update a := runNatTrans ln' (put a)
|}.

Definition lensAlg_2_lensAlg' {p A} `{Monad p}
                              (ln : lensAlg p A) : lensAlg' p A :=
  mkNatTrans (fun X sax => view ln >>= (fun a => let (x, a') := runState sax a
                                                 in update ln a' >> ret x)).

Lemma lensAlg_iso_lensAlg' : forall (ln : lensAlg p A) (ln' : lensAlg' p A),
    ((lensAlg'_2_lensAlg ∘ lensAlg_2_lensAlg') ln = ln) /\
    ((lensAlg_2_lensAlg' ∘ lensAlg'_2_lensAlg) ln' = ln').
Lemma lensAlg_induces_lensAlg' : 
    forall {p A} `{MonadLaws p} (ln : lensAlg p A),
           lensAlgLaws ln -> monad_morphism (lensAlg_2_lensAlg' ln).
Proof.
  intros.
  unfold lensAlg_2_lensAlg'.
  unfold monad_morphism.
  destruct H0.
  destruct H1.
  split; intros; simpl.

  - (* maps ret to ret *)
    rewrite <- assoc.
    rewrite view_update.
    now rewrite left_id.

  - (* distributes over >>= *)
    rewrite assoc.
    unwrap_layer.
    destruct (runState fa x).
    rewrite assoc.
    rewrite left_id.
    rewrite <- assoc.
    rewrite update_view.
    rewrite assoc.
    rewrite left_id.
    destruct (runState (f a) a0).
    rewrite <- assoc.
    now rewrite update_update.
Qed.

Lemma lensAlg'_induces_lensAlg : 
    forall {p A} `{MonadLaws p} (ln' : lensAlg' p A),
           monad_morphism ln' -> lensAlgLaws (lensAlg'_2_lensAlg ln').
Proof.
  intros.
  unfold lensAlg'_2_lensAlg.
  destruct H0.
  destruct H1.
  split; simpl; intros.

  - (* get_get *)
    symmetry in H0.
    rewrite (monadic_extensionality_2
               _
               (fun pair => runNatTrans ln' (ret pair))
               (fun a b => H0 _ (a, b))).
    symmetry in H1.
    rewrite (monadic_extensionality_1 _ _ (fun _ => H1 _ _ _ _)).
    rewrite H1.
    rewrite (monadic_extensionality_1 _ _ (fun _ => H0 _ _)).
    now rewrite H1.

  - (* get_put *)
    rewrite <- H1.
    now rewrite <- H0.

  - (* put_get *)
    rewrite <- H0.
    now repeat rewrite <- H1.

  - (* put_put *)
    now rewrite <- H1.
Qed.


(* Lens algebra homomorphism *)


(* Composition example *)
