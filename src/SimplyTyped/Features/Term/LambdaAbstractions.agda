module SimplyTyped.Features.Term.LambdaAbstractions (ty : Set) (arrow : ty → ty → ty) where

open import Data.List using (List; _∷_)
open import SimplyTyped.Core.Term
open import SimplyTyped.Judgments using (TyJdg; _⊢_)

open TmFeat
open MapTmForm

private
  variable
    τ τ'  : ty
    Γ     : List ty
    ne nf : TmSet (TyJdg ty)

----------------------------------------------------------------------------------------------------
-- Construct the feature
----------------------------------------------------------------------------------------------------

-- The neutral forms for the lambda feature are applications of neutrals to normal terms.
data NeForm : TmForm (TyJdg ty) where
  app-form : ne (Γ ⊢ arrow τ τ') → nf (Γ ⊢ τ) → NeForm ne nf (Γ ⊢ τ')

-- The normal forms for the lambda feature are abstractions with normal term bodies.
data NfForm : TmForm (TyJdg ty) where
  lam-form : nf (τ ∷ Γ ⊢ τ') → NfForm ne nf (Γ ⊢ arrow τ τ')

-- An instance for the lambda feature.
lambda-feat : TmFeat (TyJdg ty)
lambda-feat .ne-form = NeForm
lambda-feat .nf-form = NfForm

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-ne-form : MapTmForm NeForm
  inst-map-ne-form .map-form map-ne map-nf (app-form t t') = app-form (map-ne t) (map-nf t')

  inst-map-nf-form : MapTmForm NfForm
  inst-map-nf-form .map-form map-ne map-nf (lam-form t') = lam-form (map-nf t')

  inst-map-lambda-feat : MapTmFeat lambda-feat
  inst-map-lambda-feat = infer-map-tm-feat
