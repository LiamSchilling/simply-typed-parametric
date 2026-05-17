module SimplyTyped.Langs.Term.DeBruijnVarSTLC (α : Set) where

open import Data.List using (List; _∷_; lookup)
open import SimplyTyped.Langs.Type.STLC α public
open import SimplyTyped.Core.Term
open import SimplyTyped.Core.Term using (ne-to-tm; nf-to-tm) public
open import SimplyTyped.Features.Term.DeBruijnVariables Ty
open import SimplyTyped.Features.Term.LambdaAbstractions Ty arrow

open MapTmLang

private
  variable
    τ τ' : Ty
    Γ    : List Ty

----------------------------------------------------------------------------------------------------
-- Assemble the term language
----------------------------------------------------------------------------------------------------

data TmFeatIdx : Set where
  var-idx : TmFeatIdx
  lam-idx : TmFeatIdx

tm-lang : TmLang TmFeatIdx Jdg
tm-lang var-idx = debruijn-var-feat
tm-lang lam-idx = lambda-feat

----------------------------------------------------------------------------------------------------
-- Derive the term forms
----------------------------------------------------------------------------------------------------

Tm = TmOf tm-lang
Ne = NeOf tm-lang
Nf = NfOf tm-lang

var : ∀ i → Tm (Γ ⊢ lookup Γ i)
app : Tm (Γ ⊢ arrow τ τ') → Tm (Γ ⊢ τ) → Tm (Γ ⊢ τ')
lam : Tm (τ ∷ Γ ⊢ τ') → Tm (Γ ⊢ arrow τ τ')
var i    = tm-of-ne-form var-idx (var-form i)
app t t' = tm-of-ne-form lam-idx (app-form t t')
lam t'   = tm-of-nf-form lam-idx (lam-form t')

ne-var : ∀ i → Ne (Γ ⊢ lookup Γ i)
ne-app : Ne (Γ ⊢ arrow τ τ') → Nf (Γ ⊢ τ) → Ne (Γ ⊢ τ')
nf-lam : Nf (τ ∷ Γ ⊢ τ') → Nf (Γ ⊢ arrow τ τ')
ne-var i    = of-ne-form var-idx (var-form i)
ne-app t t' = of-ne-form lam-idx (app-form t t')
nf-lam t'   = of-nf-form lam-idx (lam-form t')

nf-of-ne : Ne (Γ ⊢ τ) → Nf (Γ ⊢ τ)
nf-of-ne = of-ne

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-tm-lang : MapTmLang tm-lang
  inst-map-tm-lang .map-feat var-idx = inst-map-debruijn-var-feat
  inst-map-tm-lang .map-feat lam-idx = inst-map-lambda-feat
