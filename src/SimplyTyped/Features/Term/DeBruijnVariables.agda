module SimplyTyped.Features.Term.DeBruijnVariables (ty : Set) where

open import Data.List using (List; lookup)
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
-- Algebra instances
----------------------------------------------------------------------------------------------------

instance
  inst-map-ne-form : MapTmForm NeForm
  inst-map-ne-form .map-form map-ne map-nf (var-form i) = var-form i

  inst-map-nf-form : MapTmForm NfForm
  inst-map-nf-form .map-form _ _ ()

  inst-map-debruijn-var-feat : MapTmFeat debruijn-var-feat
  inst-map-debruijn-var-feat = infer-map-tm-feat
