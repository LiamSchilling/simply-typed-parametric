module SimplyTyped.Langs.Type.STLC (α : Set) where

open import SimplyTyped.Judgments using (TyJdg)
open import SimplyTyped.Judgments using (_⊢_) public
open import SimplyTyped.Core.Type
open import SimplyTyped.Features.Type.Atoms α
open import SimplyTyped.Features.Type.Arrow

open MapTyLang

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
