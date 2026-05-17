module SimplyTyped.Features.Term.DeBruijnVariables (ty : Set) where

open import Data.All using (project)
open import Data.List using (List; lookup)
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

-- The neutral forms for the De Bruijn variable feature are indexed variables.
data NeForm : TmForm (TyJdg ty) where
  var-form : ∀ i → NeForm ne nf (Γ ⊢ lookup Γ i)

-- There are no properly normal (but not neutral) forms for the De Bruijn variable feature.
data NfForm : TmForm (TyJdg ty) where

-- An instance for the De Bruijn variable feature.
debruijn-var-feat : TmFeat (TyJdg ty)
debruijn-var-feat .ne-form = NeForm
debruijn-var-feat .nf-form = NfForm

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-ne-form : MapTmForm NeForm
  inst-map-ne-form .map-form map-ne map-nf (var-form i) = var-form i

  inst-map-nf-form : MapTmForm NfForm
  inst-map-nf-form .map-form _ _ ()

  inst-map-debruijn-var-feat : MapTmFeat debruijn-var-feat
  inst-map-debruijn-var-feat .map-ne-form = inst-map-ne-form
  inst-map-debruijn-var-feat .map-nf-form = inst-map-nf-form

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

instance
  inst-denote-ne-form : DenoteTmForm (denote-ty-jdg denote-ty) NeForm
  inst-denote-ne-form .denote-form denote-ne denote-nf (var-form i) Σ = project Σ i

  inst-denote-nf-form : DenoteTmForm (denote-ty-jdg denote-ty) NfForm
  inst-denote-nf-form .denote-form _ _ ()

  inst-denote-debruijn-var-feat : DenoteTmFeat (denote-ty-jdg denote-ty) debruijn-var-feat
  inst-denote-debruijn-var-feat .denote-ne-form = inst-denote-ne-form
  inst-denote-debruijn-var-feat .denote-nf-form = inst-denote-nf-form
