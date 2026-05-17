module SimplyTyped.Core.Term where

private
  variable
    jdg : Set
    J   : jdg

----------------------------------------------------------------------------------------------------
-- Term languages
----------------------------------------------------------------------------------------------------

-- `tm : TmSet jdg` or a term set is a family of sets
-- indexed by the judgments `j : jdg` they certify.
-- The set of judgments `jdg` may be specialized to, for example, types in a typing context.
TmSet : Set → Set₁
TmSet jdg = jdg → Set

-- `form : TmForm jdg` or a term form is a family of term sets
-- indexed by term sets of neutral terms `ne : TmSet jdg`
-- and term sets of normal terms `nf : TmSet jdg`.
-- Informally, we enforce the invariant that `ne` and `nf` appear positively in `form ne nf J`.
TmForm : Set → Set₁
TmForm jdg = TmSet jdg → TmSet jdg → TmSet jdg

-- `feat : TmFeat jdg` or a term feature is the conjunction of
-- a term form for neutral terms `feat .ne-form : TmForm jdg`
-- and a term form for normal terms `feat .nf-form : TmForm jdg`.
-- Generally, these will be respectively the elim and intro forms of the feature.
record TmFeat (jdg : Set) : Set₁ where
  field
    ne-form : TmForm jdg
    nf-form : TmForm jdg

open TmFeat

-- `lang : TmLang jdg` or a term language is a collection of term features `lang i : TmFeat jdg`
-- indexed by elements `i : ι`.
TmLang : Set → Set → Set₁
TmLang ι jdg = ι → TmFeat jdg

private
  variable
    ι                 : Set
    ne nf ne' nf'     : TmSet jdg
    ne-form' nf-form' : TmForm jdg
    lang              : TmLang ι jdg

----------------------------------------------------------------------------------------------------
-- Sets of terms
----------------------------------------------------------------------------------------------------

-- From a term language `lang : TmLang ty`, we can construct the term set `TmOf lang : TmSet ty`
-- as the disjunction of every neutral or normal term form in the language `lang`.
-- It is a valid inductive definition given the positivity invariant of `TmForm`.
{-# NO_POSITIVITY_CHECK #-}
data TmOf (lang : TmLang ι jdg) : TmSet jdg where
  tm-of-ne-form : ∀ i → lang i .ne-form (TmOf lang) (TmOf lang) J → TmOf lang J
  tm-of-nf-form : ∀ i → lang i .nf-form (TmOf lang) (TmOf lang) J → TmOf lang J

-- From a term language `lang : TmLang ty`,
-- we can construct the term set of neutral terms `NeOf lang : TmSet ty`
-- mutually with the term set of normal terms `NfOf lang : TmSet ty`,
-- each as the disjunction of neutral or normal term forms in the language `lang`.
-- Additionally, the the `of-ne` rule allows casting neutral terms directly to normal terms.
-- It is a valid inductive definition given the positivity invariant of `TmForm`.
{-# NO_POSITIVITY_CHECK #-}
data NeOf (lang : TmLang ι jdg) : TmSet jdg
data NfOf (lang : TmLang ι jdg) : TmSet jdg

data NeOf lang where
  of-ne-form : ∀ i → lang i .ne-form (NeOf lang) (NfOf lang) J → NeOf lang J

data NfOf lang where
  of-nf-form : ∀ i → lang i .nf-form (NeOf lang) (NfOf lang) J → NfOf lang J
  of-ne      : NeOf lang J → NfOf lang J

----------------------------------------------------------------------------------------------------
-- Mapping
----------------------------------------------------------------------------------------------------

record MapTmForm (form : TmForm jdg) : Set₁ where
  field
    map-form : (∀ {J'} → ne J' → ne' J') → (∀ {J'} → nf J' → nf' J') → form ne nf J → form ne' nf' J

record MapTmFeat (feat : TmFeat jdg) : Set₁ where
  field
    map-ne-form : MapTmForm (feat .ne-form)
    map-nf-form : MapTmForm (feat .nf-form)

record MapTmLang (lang : TmLang ι jdg) : Set₁ where
  field
    map-feat : ∀ i → MapTmFeat (lang i)

open MapTmForm
open MapTmFeat
open MapTmLang

instance
  infer-map-tm-feat : {{MapTmForm ne-form'}} → {{MapTmForm nf-form'}} →
                      MapTmFeat record { ne-form = ne-form'; nf-form = nf-form' }
  infer-map-tm-feat {{F-ne}} {{F-nf}} .map-ne-form = F-ne
  infer-map-tm-feat {{F-ne}} {{F-nf}} .map-nf-form = F-nf

-- Cast a neutral or normal term into the general set of terms.
-- It terminates as long as the `MapTmLang` argument is a proper homomorphic map.
{-# TERMINATING #-}
ne-to-tm : {{MapTmLang lang}} → NeOf lang J → TmOf lang J
nf-to-tm : {{MapTmLang lang}} → NfOf lang J → TmOf lang J
ne-to-tm {{F}} (of-ne-form i t) = tm-of-ne-form i
                                  (F .map-feat i .map-ne-form .map-form ne-to-tm nf-to-tm t)
nf-to-tm {{F}} (of-nf-form i t) = tm-of-nf-form i
                                  (F .map-feat i .map-nf-form .map-form ne-to-tm nf-to-tm t)
nf-to-tm {{F}} (of-ne t)        = ne-to-tm t
