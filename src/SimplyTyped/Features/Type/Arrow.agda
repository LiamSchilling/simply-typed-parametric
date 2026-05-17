module SimplyTyped.Features.Type.Arrow where

open import SimplyTyped.Core.Type

open MapTyFeat
open DenoteTyFeat

private
  variable
    ty : Set

----------------------------------------------------------------------------------------------------
-- Construct the feature
----------------------------------------------------------------------------------------------------

-- The arrow feature includes the binary `arrow` form.
data ArrowFeat : TyFeat where
  arrow-form : ty → ty → ArrowFeat ty

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

instance
  inst-map-arrow-feat : MapTyFeat ArrowFeat
  inst-map-arrow-feat .map-form map-ty (arrow-form τ τ') = arrow-form (map-ty τ) (map-ty τ')

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

instance
  inst-denote-arrow-feat : DenoteTyFeat ArrowFeat
  inst-denote-arrow-feat .denote-form denote-ty (arrow-form τ τ') = denote-ty τ → denote-ty τ'
