Set Warnings "-notation-overridden,-parsing".
Require Import Program.Basics.
Require Import Strings.String.
Require Import Background.
Require Import Towards.
Require Import FunctionalExtensionality.


(*************************)
(* Natural Lens Algebras *)
(*************************)

(* Alternative lens algebra (or MonadState) definition *)

Definition lensAlg' (p : Type -> Type) `{Monad p} (A : Type) :=
  state A ~> p.


(* There is an isomorphism between [lensAlg'] and [lensAlg] *)

Definition lensAlg'_2_lensAlg {p A} `{Monad p}
                              (ln' : lensAlg' p A) : lensAlg p A :=
{| view := runNatTrans ln' get
;  update a := runNatTrans ln' (put a)
|}.

Definition lensAlg_2_lensAlg' {p A} `{Monad p}
                              (ln : lensAlg p A) : lensAlg' p A :=
  mkNatTrans (fun X sax => view ln >>= (fun a => let (x, a') := runState sax a
                                                 in update ln a' >> ret x)).

Lemma lensAlg_induces_lensAlg' :
  forall {p A} `{MonadLaws p} (ln : lensAlg p A),
    lensAlgLaws ln -> monad_morphism (lensAlg_2_lensAlg' ln).
Proof.
  intros.
  unfold lensAlg_2_lensAlg'.
  unfold monad_morphism.
  destruct H1.
  destruct H2.
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
  destruct H1.
  destruct H2.
  split; simpl; intros.

  - (* get_get *)
    symmetry in H1.
    rewrite (monadic_extensionality_2
               _
               (fun pair => runNatTrans ln' (ret pair))
               (fun a b => H1 _ (a, b))).
    symmetry in H2.
    rewrite (monadic_extensionality_1 _ _ (fun _ => H2 _ _ _ _)).
    rewrite H2.
    rewrite (monadic_extensionality_1 _ _ (fun _ => H1 _ _)).
    now rewrite H2.

  - (* get_put *)
    rewrite <- H2.
    now rewrite <- H1.

  - (* put_get *)
    rewrite <- H1.
    now repeat rewrite <- H2.

  - (* put_put *)
    now rewrite <- H2.
Qed.

Theorem lensAlg_iso_lensAlg' :
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
  pose proof (@non_eff_view p A H H0 H1 ln) as K.
  destruct H1.
  split; simpl.

  - (* lensAlg'_2_lensAlg ∘ lensAlg_2_lensAlg' *)
    destruct H2.
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
    destruct H3; simpl in *.
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
      now rewrite H1. }
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


(* Lens algebra homomorphism abstracts away `state A` from `lensAlg'`. *)

Definition lensAlgHom (p q : Type -> Type) (A : Type)
                     `{Monad p} `{MonadState A q} :=
  q ~> p.

(* This is exactly [lensAlg'], but defined in terms of the new abstraction. 
   We'll be using this representation further on to reuse [lensAlgHom]
   definitions. *)
Definition lensAlg'' (p : Type -> Type) (A : Type) `{Monad p} :=
  lensAlgHom p (state A) A.


(* Lens algebra homomorphisms induce lens algebra. *)

Definition lensAlgHom_2_lensAlg {p q A} `{Monad p} `{MonadState A q}
                                (φ : lensAlgHom p q A) : lensAlg p A :=
{| view := runNatTrans φ get
;  update a := runNatTrans φ (put a)
|}.

Proposition lensAlgHom_induces_lensAlg :
  forall {p q A} `{Monad p} `{MonadStateLaws A q} (φ : lensAlgHom p q A),
    monad_morphism φ -> lensAlgLaws (lensAlgHom_2_lensAlg φ).
Proof.
  unfold monad_morphism.
  unfold lensAlgHom_2_lensAlg.
  intros.
  destruct H4 as [GG GP PG PP].
  destruct H5 as [QP1 QP2].
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

Definition view {p q A} `{Monad p} `{MonadState A q}
                (φ : lensAlgHom p q A) : p A :=
  view (lensAlgHom_2_lensAlg φ).

Definition update {p q A} `{Monad p} `{MonadState A q}
                  (φ : lensAlgHom p q A)
                  (a : A) : p unit :=
  update (lensAlgHom_2_lensAlg φ) a.

Definition modify {p q A} `{Monad p} `{MonadState A q}
                  (φ : lensAlgHom p q A)
                  (f : A -> A) : p unit :=
  modify (lensAlgHom_2_lensAlg φ) f.
Notation "φ %~ f" := (modify φ f) (at level 40, no associativity).


(* Lens algebra homomorphisms conform a category. *)

Definition composeLnAlgHom {p q r A B}
   `{MonadState B r} `{MonadState A q} `{Monad p}
    (φ : lensAlgHom p q A) (ψ : lensAlgHom q r B) : lensAlgHom p r B :=
  φ • ψ.
Notation "f ▷ g" := (composeLnAlgHom f g) (at level 40, left associativity).

Definition identityLensAlgHom p A `{MonadState A p} : lensAlgHom p p A :=
  mkNatTrans (fun _ => id).

Lemma closed_under_composeLnAlgHom :
  forall  {p q r A B}
         `{MonadState B r} `{MonadState A q} `{Monad p}
          (φ : lensAlgHom p q A)
          (ψ : lensAlgHom q r B),
    monad_morphism φ -> monad_morphism ψ -> monad_morphism (φ • ψ).
Proof.
  unfold monad_morphism.
  intros.
  destruct H7 as [QP1 QP2].
  destruct H8 as [RQ1 RQ2].
  split; intros; simpl; [rewrite RQ1 | rewrite RQ2]; auto.
Qed.

Lemma left_id_law_composeLnAlgHom :
  forall  {p q A B}
         `{MonadState A q} (* weird => *) `{MonadState B p}
          (φ : lensAlgHom p q A),
    identityLensAlgHom p B • φ = φ.
Proof.
  intros.
  unfold composeNT.
  destruct φ.
  apply f_equal.
  extensionality X.
  now extensionality fx.
Qed.

Lemma right_id_law_composeLnAlgHom :
  forall  {p q A} `{MonadState A q} `{Monad p} (φ : lensAlgHom p q A),
    φ • identityLensAlgHom q A = φ.
Proof.
  intros.
  unfold composeNT.
  destruct φ.
  apply f_equal.
  extensionality X.
  now extensionality fx.
Qed.

Lemma assoc_composeLnAlgHom :
  forall  {p q r s A B C}
         `{MonadState C s} `{MonadState B r} `{MonadState A q} `{Monad p}
          (φ : lensAlgHom p q A)
          (ψ : lensAlgHom q r B)
          (χ : lensAlgHom r s C),
    (φ • ψ) • χ = φ • (ψ • χ).
Proof.
  intros.
  unfold composeNT.
  apply f_equal.
  extensionality X.
  now extensionality fx.
Qed.


(*************************)
(* University Data Layer *)
(*************************)

Record DepartmentAlg p Dep `{id : MonadState Dep p} :=
{ budgetLn : lensAlg'' p nat }.
Arguments budgetLn [p Dep _ _ id].

Record UniversityAlg p Univ `{id : MonadState Univ p} :=
{ nameLn : lensAlg p string
; q : Type -> Type
; Dep : Type
; fq : Functor q
; mq : Monad q
; msq : MonadState Dep q
; ev : DepartmentAlg q Dep
; mathDepLn : lensAlgHom p q Dep
}.
Arguments mq [p Univ _ _ id].
Arguments ev [p Univ _ _ id].
Arguments mathDepLn [p Univ _ _ id].

Definition duplicateDepBudget p Dep
   `{MonadState Dep p}
    (data : DepartmentAlg p Dep) : p unit :=
  budgetLn data %~ (fun b => b * 2).

Definition duplicateMathBudget p Univ
   `{MonadState Univ p}
    (data : UniversityAlg p Univ) : p unit :=
  (mathDepLn data ▷ budgetLn (ev data)) %~ (fun b => b * 2).

Definition duplicateMathBudgetR p Univ 
   `{MonadState Univ p}
    (data : UniversityAlg p Univ) : p nat :=
  let ln := mathDepLn data ▷ budgetLn (ev data)
  in ln %~ (fun b => b * 2) >> view ln.

(* Coq doesn't infer that [q] is a monad and therefore the ugly syntax. *)
Definition duplicateMathBudgetR' p Univ
   `{MonadState Univ p}
    (data : UniversityAlg p Univ) : p nat :=
  let bLn := budgetLn (ev data)
  in runNatTrans (mathDepLn data) (@bind _ _ (mq data) _ _
    (@modify _ _ _ _ (mq data) _ _ _ bLn (fun b => b * 2))
    (fun _ => @view _ _ _ _ (mq data) _ _ _ bLn)).
