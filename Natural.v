Require Import Program.Basics.
Require Import Strings.String.
Require Import Background.
Require Import Towards.
Require Import FunctionalExtensionality.


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

Lemma lensAlg_iso_lensAlg' : 
    forall {p A} `{MonadLaws p} (ln : lensAlg p A) (ln' : lensAlg' p A),
           lensAlgLaws ln -> 
           monad_morphism ln' ->
           ((lensAlg'_2_lensAlg ∘ lensAlg_2_lensAlg') ln = ln) /\
           ((lensAlg_2_lensAlg' ∘ lensAlg'_2_lensAlg) ln' = ln').
Proof.
  intros.
  unfold lensAlg'_2_lensAlg.
  unfold lensAlg_2_lensAlg'.
  unfold compose.
  pose proof (@non_eff_view p A H H0 ln H1) as K.
  destruct H0.
  split; simpl.

  - (* lensAlg'_2_lensAlg ∘ lensAlg_2_lensAlg' *)
    destruct H1.
    rewrite <- (monadic_extensionality_1 _ _ update_view).
    rewrite <- assoc.
    rewrite view_update.
    rewrite left_id.
    assert (G : (fun a : A => view ln >> (update ln a >> ret tt)) = update ln).
    { functional_extensionality_i.
      assert (G1 : update ln x >> ret tt = update ln x >>= ret).
      { unfold bind.
        apply f_equal.
        functional_extensionality_i.
        now destruct x0. }
      rewrite G1.
      rewrite right_id.
      now rewrite K. }
    rewrite G.
    now destruct ln.

  - (* lensAlg_2_lensAlg' ∘ lensAlg'_2_lensAlg *)
    destruct H2.
    destruct ln'.
    simpl in *.
    apply f_equal.
    extensionality X.
    extensionality sax.
    assert (G : runNatTrans A {| runState := fun s : A => (s, s) |} >>=
                (fun a : A => let (x, a') := runState sax a in
                runNatTrans unit {| runState := fun _ : A => (tt, a') |} >> 
                ret x) =
                runNatTrans A {| runState := fun s : A => (s, s) |} >>=
                (fun a : A => let (x, a') := runState sax a in
                runNatTrans unit {| runState := fun _ : A => (tt, a') |} >> 
                runNatTrans X (ret x))).
    { unwrap_layer. 
      simpl.
      destruct (runState sax x).
      unwrap_layer.
      now rewrite H0. }
    rewrite G.
    assert (G1 : runNatTrans A {| runState := fun s : A => (s, s) |} >>=
                 (fun a : A => let (x, a') := runState sax a in
                 runNatTrans unit {| runState := fun _ : A => (tt, a') |} >> 
                 runNatTrans X (ret x)) =
                 runNatTrans A {| runState := fun s : A => (s, s) |} >>=
                 (fun a : A =>
                 runNatTrans unit {| runState := fun _ : A => (tt, execState sax a) |} >> 
                 runNatTrans X (ret (evalState sax a)))).
    { unwrap_layer.
      unfold evalState.
      unfold execState.
      simpl.
      now destruct (runState sax x). }
    rewrite G1.
    rewrite <- (monadic_extensionality_1 _ _ (fun _ => H2 _ _ _ _)).
    simpl.
    rewrite <- H2.
    simpl.
    unfold evalState. unfold execState.
    simpl.
    apply f_equal.
    destruct sax.
    simpl.
    unwrap_layer.
    now destruct (runState x).
Qed.

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

Definition lensAlgHom (p q : Type -> Type) (A : Type) 
                     `{Monad p} `{MonadState A q} :=
  q ~> p.

Definition view' {p q A} `{Monad p} `{MonadState A q} 
                 (φ : lensAlgHom p q A) : p A :=
  runNatTrans φ get.

Definition update' {p q A} `{Monad p} `{MonadState A q} 
                   (φ : lensAlgHom p q A)
                   (a : A) : p unit :=
  runNatTrans φ (put a).

Definition modify' {p q A} `{Monad p} `{MonadState A q} 
                   (φ : lensAlgHom p q A)
                   (f : A -> A) : p unit :=
  runNatTrans φ (mod f).
Notation "φ ~ f" := (modify' φ f) (at level 40, no associativity).

Definition composeLnAlgHom {p q r A B}
   `{MonadState B r} `{MonadState A q} `{Monad p}
    (φ : lensAlgHom p q A) (ψ : lensAlgHom q r B) : lensAlgHom p r B := 
  φ • ψ.

Theorem closed_under_composeLnAlgHom : 
    forall  {p q r A B}
           `{MonadState B r} `{MonadState A q} `{Monad p}
            (φ : lensAlgHom p q A)
            (ψ : lensAlgHom q r B),
            monad_morphism φ ->
            monad_morphism ψ ->
            monad_morphism (φ • ψ).
Proof.
  unfold monad_morphism.
  intros.
  destruct H4 as [QP1 QP2].
  destruct H5 as [RQ1 RQ2].
  split; intros; simpl; [rewrite RQ1 | rewrite RQ2]; auto.
Qed.

Definition lensAlgHom_2_lensAlg {p q A} `{Monad p} `{MonadState A q} 
                                (φ : lensAlgHom p q A) : lensAlg p A :=
{| view := runNatTrans φ get
;  update a := runNatTrans φ (put a)
|}.

Theorem lensAlgHom_induces_lensAlg :
    forall {p q A} 
          `{Monad p} `{MonadStateLaws A q}
           (φ : lensAlgHom p q A),
           monad_morphism φ -> 
           lensAlgLaws (lensAlgHom_2_lensAlg φ).
Proof.
  unfold monad_morphism.
  unfold lensAlgHom_2_lensAlg.
  intros.
  destruct H2 as [GG GP PG PP].
  destruct H3 as [QP1 QP2].
  split; simpl; intros.

  - (* get_get *)
    symmetry in QP1.
    rewrite (monadic_extensionality_2 
               _
               (fun pair => runNatTrans φ (ret pair)) 
               (fun a1 a2 => QP1 _ (a1, a2))).
    symmetry in QP2.
    rewrite (monadic_extensionality_1 _ _ (fun _ => QP2 _ _ _ _)).
    rewrite QP2.
    rewrite GG.
    rewrite (monadic_extensionality_1 _ _ (fun _ => QP1 _ _)).
    auto.

  - (* get_put *)
    rewrite <- QP2.
    rewrite GP.
    now rewrite QP1.

  - (* put_get *)
    rewrite <- QP2.
    rewrite PG.
    rewrite -> QP2.
    now rewrite QP1.

  - (* put_put *)
    rewrite <- QP2.
    now rewrite PP.
Qed.


(* Zip example *)

Record Address (p : Type -> Type) `{Monad p} := mkAddress
{ zip  : lensAlg' p nat
; city : lensAlg' p string
}.
Arguments zip [p _].
Arguments city [p _].

(* 1st approach *)

Record Person (p : Type -> Type) `{Monad p} := mkPerson
{ name : lensAlg' p string
; q : Type -> Type
; Add : Type
; M : Monad q
; MS : MonadState Add q
; address_ev : Address q
; address : lensAlgHom p q Add
}.
Arguments address [p _].
Arguments address_ev [p _ _].

Definition modifyPersonZip (f : nat -> nat) {p} `{Monad p}
                           (data : Person p) : p unit :=
  (address data • zip address_ev) ~ f.

Definition getPersonCity {p} `{Monad p}
                         (data : Person p) : p string :=
  view' (address data • city address_ev).

(* 2nd approach *)

Record Person' (p q : Type -> Type) (Add : Type) 
              `{Monad p} `{MonadState Add q} := mkPerson'
{ name' : lensAlg' p string
; address_ev' : Address q
; address' : lensAlgHom p q Add
}.
Arguments address' [p _ _ _ _ _].
Arguments address_ev' [p _ _ _ _ _].

Definition modifyPersonZip' (f : nat -> nat) 
                            {p q Add} `{Monad p} `{MonadState Add q}
                            (data : Person' p q Add) : p unit :=
  (address' data • zip (address_ev' data)) ~ f.

Definition getPersonCity' {p q Add} `{Monad p} `{MonadState Add q}
                         (data : Person' p q Add) : p string :=
  view' (address' data • city (address_ev' data)).
