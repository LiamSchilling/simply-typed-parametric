module SimplyTyped.Features.Type.Arrow where

open import SimplyTyped.Core.Type

private
  variable
    ty : Set

----------------------------------------------------------------------------------------------------
-- Construct the feature
----------------------------------------------------------------------------------------------------

-- The arrow feature includes the binary `arrow` form.
data ArrowFeat : TyFeat where
  arrow-form : ty → ty → ArrowFeat ty
