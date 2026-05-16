module SimplyTyped.Langs.AtomicVarSTLC (α : Set) where

open import Data.List using (List; _∷_)

----------------------------------------------------------------------------------------------------
-- Assemble the type language
----------------------------------------------------------------------------------------------------

data TyFeatIdx : Set where
  atom-idx  : TyFeatIdx
  arrow-idx : TyFeatIdx

open import SimplyTyped.Core.Type
open import SimplyTyped.Features.Type.Atoms α
open import SimplyTyped.Features.Type.Arrow

ty-lang : TyLang TyFeatIdx
ty-lang atom-idx  = AtomFeat
ty-lang arrow-idx = ArrowFeat

----------------------------------------------------------------------------------------------------
-- Derive the type forms
----------------------------------------------------------------------------------------------------

Ty = TyOf ty-lang

atom  : α → Ty
arrow : Ty → Ty → Ty
atom a     = of-feat atom-idx  (atom-form a)
arrow τ τ' = of-feat arrow-idx (arrow-form τ τ')

----------------------------------------------------------------------------------------------------
-- Derive the set of typing judgments
----------------------------------------------------------------------------------------------------

open import SimplyTyped.Judgments using (TyJdg; _⊢_)

Jdg = TyJdg Ty

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

open import SimplyTyped.Core.Term
open import SimplyTyped.Features.Term.AtomicVariables    Ty
open import SimplyTyped.Features.Term.LambdaAbstractions Ty arrow

tm-lang : TmLang TmFeatIdx Jdg
tm-lang var-idx = atomic-var-feat
tm-lang lam-idx = lambda-feat

----------------------------------------------------------------------------------------------------
-- Derive the term forms
----------------------------------------------------------------------------------------------------

Tm = TmOf tm-lang
Ne = NeOf tm-lang
Nf = NfOf tm-lang

var : Tm (τ ∷ Γ ⊢ τ)
wkn : Tm (Γ ⊢ τ) → Tm (τ' ∷ Γ ⊢ τ)
app : Tm (Γ ⊢ arrow τ τ') → Tm (Γ ⊢ τ) → Tm (Γ ⊢ τ')
lam : Tm (τ ∷ Γ ⊢ τ') → Tm (Γ ⊢ arrow τ τ')
var      = tm-of-ne-form var-idx var-form
wkn t    = tm-of-ne-form var-idx (wkn-form t)
app t t' = tm-of-ne-form lam-idx (app-form t t')
lam t'   = tm-of-nf-form lam-idx (lam-form t')

ne-var : Ne (τ ∷ Γ ⊢ τ)
ne-wkn : Ne (Γ ⊢ τ) → Ne (τ' ∷ Γ ⊢ τ)
ne-app : Ne (Γ ⊢ arrow τ τ') → Nf (Γ ⊢ τ) → Ne (Γ ⊢ τ')
nf-lam : Nf (τ ∷ Γ ⊢ τ') → Nf (Γ ⊢ arrow τ τ')
ne-var      = of-ne-form var-idx var-form
ne-wkn t    = of-ne-form var-idx (wkn-form t)
ne-app t t' = of-ne-form lam-idx (app-form t t')
nf-lam t'   = of-nf-form lam-idx (lam-form t')

nf-of-ne : Ne (Γ ⊢ τ) → Nf (Γ ⊢ τ)
nf-of-ne = of-ne

----------------------------------------------------------------------------------------------------
-- Algebra instances
----------------------------------------------------------------------------------------------------

open MapTmLang

instance
  inst-map-lang : MapTmLang tm-lang
  inst-map-lang .map-feat var-idx = inst-map-atomic-var-feat
  inst-map-lang .map-feat lam-idx = inst-map-lambda-feat

----------------------------------------------------------------------------------------------------
-- Retrieve term operations
----------------------------------------------------------------------------------------------------

ne-to-tm : Ne (Γ ⊢ τ) → Tm (Γ ⊢ τ)
nf-to-tm : Nf (Γ ⊢ τ) → Tm (Γ ⊢ τ)
ne-to-tm = ne-to-tm-of-map
nf-to-tm = nf-to-tm-of-map
