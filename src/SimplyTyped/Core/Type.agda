module SimplyTyped.Core.Type where

private
  variable
    ty ty' : Set

----------------------------------------------------------------------------------------------------
-- Type languages
----------------------------------------------------------------------------------------------------

-- `feat : TyFeat` or a type feature is a family of sets
-- indexed by a target set of types `ty : Set`.
-- Informally, we enforce the invariant that `ty` appear positively in `feat ty`.
TyFeat : Set₁
TyFeat = Set → Set

-- `lang : TyLang` or a type language is a collection of type features `lang i : TyFeat`
-- indexed by elements `i : ι`.
TyLang : Set → Set₁
TyLang ι = ι → TyFeat

private
  variable
    ι : Set

----------------------------------------------------------------------------------------------------
-- Sets of types
----------------------------------------------------------------------------------------------------

-- From a type language `lang : TyLang`, we can construct the set of types `TyOf lang : Set`
-- as the disjunction of every type feature in the language `lang`.
-- It is a valid inductive definition given the positivity invariant of `TyForm`.
{-# NO_POSITIVITY_CHECK #-}
data TyOf (lang : TyLang ι) : Set where
  of-feat : ∀ i → lang i (TyOf lang) → TyOf lang

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

record MapTyFeat (feat : TyFeat) : Set₁ where
  field
    map-form : (ty → ty') → feat ty → feat ty'

record MapTyLang (lang : TyLang ι) : Set₁ where
  field
    map-feat : ∀ i → MapTyFeat (lang i)
