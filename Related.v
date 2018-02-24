Require Import Background.

(* Monadic lenses *)

Record mLens (S A : Type) (m : Type -> Type) `{Monad m} := mkMLens
{ mview : S -> A
; mupdate : S -> A -> m S
}.
Arguments mview [S A m _].
Arguments mupdate [S A m _].
Arguments mkMLens [S A m _].

Record mLensLaws {S A m} `{Monad m} (mln : mLens S A m) := mkMLensLaws
{ mview_mupdate : forall s, mupdate mln s (mview mln s) = ret s
; mupdate_mview : forall B (k : S -> A -> m B) s a, 
                    mupdate mln s a >>= (fun s' => k s' (mview mln s')) =
                    mupdate mln s a >>= (fun s' => k s' a)
}.