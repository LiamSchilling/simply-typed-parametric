{-# OPTIONS --guardedness #-}

module Main where

-- Our set of type variable atoms.
data Atom : Set where
  A : Atom
  B : Atom

open import Data.Fin using (#_)
open import Data.Integer using (ℤ; _+_)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import IO
open import SimplyTyped.Judgments using (_⊢_)
import SimplyTyped.Langs.Type.STLC Atom as TY
import SimplyTyped.Langs.Term.AtomicVarSTLC Atom as AV
import SimplyTyped.Langs.Term.DeBruijnVarSTLC Atom as DB

open TY.DenoteAtom

-- Interpret atoms as sets of semantic objects.
instance
  inst-denote-atom : TY.DenoteAtom
  inst-denote-atom .denote-atom A = ℤ
  inst-denote-atom .denote-atom B = ℕ

----------------------------------------------------------------------------------------------------
-- Variants of STLC with both atomic (start/weakening) variables and De-Bruijn-indexed variables
----------------------------------------------------------------------------------------------------

-- The simple type `A → B → A`.

ty : TY.Ty
ty = TY.arrow (TY.atom A) (TY.arrow (TY.atom B) (TY.atom A))

-- Denote types into sets of semantic objects.

add-int-nat : TY.denote-ty ty
add-int-nat z n = z + ℤ.pos n

-- The inhabitant `λ a. λ b. a` in the atomic variant,
-- in the style of both a term and a normal form.

av-tm : AV.Tm ([] ⊢ ty)
av-tm = AV.lam (AV.lam (AV.wkn AV.var))

av-nf : AV.Nf ([] ⊢ ty)
av-nf = AV.nf-lam (AV.nf-lam (AV.nf-of-ne (AV.ne-wkn AV.ne-var)))

-- The inhabitant `λ a. λ b. a` in the De Bruijn variant,
-- in the style of both a term and a normal form.

db-tm : DB.Tm ([] ⊢ ty)
db-tm = DB.lam (DB.lam (DB.var (# 1)))

db-nf : DB.Nf ([] ⊢ ty)
db-nf = DB.nf-lam (DB.nf-lam (DB.nf-of-ne (DB.ne-var (# 1))))

-- Cast normal and neutral terms into the set of general terms.

db-tm-of-nf : DB.Tm ([] ⊢ ty)
db-tm-of-nf = DB.nf-to-tm db-nf

av-tm-of-nf : AV.Tm ([] ⊢ ty)
av-tm-of-nf = AV.nf-to-tm av-nf

----------------------------------------------------------------------------------------------------

main : Main
main = run (putStrLn "Hello, World!")
