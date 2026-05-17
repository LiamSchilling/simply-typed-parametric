module SimplyTyped.Features.Type.Atoms (α : Set) where

open import SimplyTyped.Core.Type

open MapTyFeat
open DenoteTyFeat

private
  variable
    ty : Set

----------------------------------------------------------------------------------------------------
-- Construct the feature
----------------------------------------------------------------------------------------------------

-- The type atom feature includes the atom form.
data AtomFeat : TyFeat where
  atom-form : α → AtomFeat ty

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-atom-feat : MapTyFeat AtomFeat
  inst-map-atom-feat .map-form map-ty (atom-form a) = atom-form a

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

record DenoteAtom : Set₁ where
  field
    denote-atom : α → Set

open DenoteAtom

instance
  inst-denote-atom-feat : {{DenoteAtom}} → DenoteTyFeat AtomFeat
  inst-denote-atom-feat {{D}} .denote-form denote-ty (atom-form a) = D .denote-atom a
