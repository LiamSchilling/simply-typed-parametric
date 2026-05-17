module SimplyTyped.Langs.Type.STLC (α : Set) where

open import SimplyTyped.Judgments using (TyJdg)
open import SimplyTyped.Judgments using (_⊢_) public
open import SimplyTyped.Core.Type hiding (denote-ty)
open import SimplyTyped.Core.Type using (denote-ty) public
open import SimplyTyped.Features.Type.Atoms α hiding (DenoteAtom)
open import SimplyTyped.Features.Type.Atoms α using (DenoteAtom) public
open import SimplyTyped.Features.Type.Arrow

open MapTyLang
open DenoteTyLang

----------------------------------------------------------------------------------------------------
-- Assemble the type language
----------------------------------------------------------------------------------------------------

data TyFeatIdx : Set where
  atom-idx  : TyFeatIdx
  arrow-idx : TyFeatIdx

ty-lang : TyLang TyFeatIdx
ty-lang atom-idx  = AtomFeat
ty-lang arrow-idx = ArrowFeat

----------------------------------------------------------------------------------------------------
-- Derive the type forms
----------------------------------------------------------------------------------------------------

Ty  = TyOf ty-lang
Jdg = TyJdg Ty

atom  : α → Ty
arrow : Ty → Ty → Ty
atom a     = of-feat atom-idx  (atom-form a)
arrow τ τ' = of-feat arrow-idx (arrow-form τ τ')

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-ty-lang : MapTyLang ty-lang
  inst-map-ty-lang .map-feat atom-idx  = inst-map-atom-feat
  inst-map-ty-lang .map-feat arrow-idx = inst-map-arrow-feat

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

instance
  inst-denote-ty-lang : {{DenoteAtom}} → DenoteTyLang ty-lang
  inst-denote-ty-lang .denote-feat atom-idx  = inst-denote-atom-feat
  inst-denote-ty-lang .denote-feat arrow-idx = inst-denote-arrow-feat
