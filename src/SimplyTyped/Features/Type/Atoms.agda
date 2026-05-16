module SimplyTyped.Features.Type.Atoms (α : Set) where

open import SimplyTyped.Core.Type

private
  variable
    ty : Set

----------------------------------------------------------------------------------------------------
-- Construct the feature
----------------------------------------------------------------------------------------------------

-- The type atom feature includes the atom form.
data AtomFeat : TyFeat where
  atom-form : α → AtomFeat ty
