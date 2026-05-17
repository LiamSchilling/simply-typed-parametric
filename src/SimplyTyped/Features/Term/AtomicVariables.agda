module SimplyTyped.Features.Term.AtomicVariables (ty : Set) where

open import Data.All using (_∷_)
open import Data.List using (List; _∷_)
open import SimplyTyped.Core.Term
open import SimplyTyped.Judgments using (TyJdg; _⊢_; denote-ty-jdg)

open TmFeat
open MapTmForm
open MapTmFeat
open DenoteTmForm
open DenoteTmFeat

private
  variable
    τ τ'      : ty
    Γ         : List ty
    ne nf     : TmSet (TyJdg ty)
    denote-ty : ty → Set

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
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-ne-form : MapTmForm NeForm
  inst-map-ne-form .map-form map-ne map-nf var-form     = var-form
  inst-map-ne-form .map-form map-ne map-nf (wkn-form t) = wkn-form (map-ne t)

  inst-map-nf-form : MapTmForm NfForm
  inst-map-nf-form .map-form _ _ ()

  inst-map-atomic-var-feat : MapTmFeat atomic-var-feat
  inst-map-atomic-var-feat .map-ne-form = inst-map-ne-form
  inst-map-atomic-var-feat .map-nf-form = inst-map-nf-form

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

instance
  inst-denote-ne-form : DenoteTmForm (denote-ty-jdg denote-ty) NeForm
  inst-denote-ne-form .denote-form denote-ne denote-nf var-form     (σ ∷ _) = σ
  inst-denote-ne-form .denote-form denote-ne denote-nf (wkn-form t) (_ ∷ Σ) = denote-ne t Σ

  inst-denote-nf-form : DenoteTmForm (denote-ty-jdg denote-ty) NfForm
  inst-denote-nf-form .denote-form _ _ ()

  inst-denote-atomic-var-feat : DenoteTmFeat (denote-ty-jdg denote-ty) atomic-var-feat
  inst-denote-atomic-var-feat .denote-ne-form = inst-denote-ne-form
  inst-denote-atomic-var-feat .denote-nf-form = inst-denote-nf-form
