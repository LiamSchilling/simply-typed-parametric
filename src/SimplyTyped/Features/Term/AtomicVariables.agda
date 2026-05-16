module SimplyTyped.Features.Term.AtomicVariables (ty : Set) where

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

-- The neutral forms for the variable feature are variable atoms and weakening of neutrals.
data NeForm : TmForm (TyJdg ty) where
  var-form : NeForm ne nf (τ ∷ Γ ⊢ τ)
  wkn-form : ne (Γ ⊢ τ) → NeForm ne nf (τ' ∷ Γ ⊢ τ)

-- There are no properly normal (but not neutral) forms for the variable feature.
data NfForm : TmForm (TyJdg ty) where

-- An instance for the variable feature.
atomic-var-feat : TmFeat (TyJdg ty)
atomic-var-feat .ne-form = NeForm
atomic-var-feat .nf-form = NfForm

----------------------------------------------------------------------------------------------------
-- Algebra instances
----------------------------------------------------------------------------------------------------

instance
  inst-map-ne-form : MapTmForm NeForm
  inst-map-ne-form .map-form map-ne map-nf var-form     = var-form
  inst-map-ne-form .map-form map-ne map-nf (wkn-form t) = wkn-form (map-ne t)

  inst-map-nf-form : MapTmForm NfForm
  inst-map-nf-form .map-form _ _ ()

  inst-map-atomic-var-feat : MapTmFeat atomic-var-feat
  inst-map-atomic-var-feat = infer-map-tm-feat
