{-# OPTIONS --guardedness #-}

module Main where

open import IO

open import Data.Fin using (#_)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import SimplyTyped.Judgments using (_⊢_)

import SimplyTyped.Langs.AtomicVarSTLC   ℕ as AV
import SimplyTyped.Langs.DeBruijnVarSTLC ℕ as DB

----------------------------------------------------------------------------------------------------
-- Variants of STLC with both atomic (start/weakening) variables and De-Bruijn-indexed variables
----------------------------------------------------------------------------------------------------

-- The same simple type `A → B → A` in both languages.

av-ty : AV.Ty
av-ty = AV.arrow (AV.atom 0) (AV.arrow (AV.atom 1) (AV.atom 0))

db-ty : DB.Ty
db-ty = DB.arrow (DB.atom 0) (DB.arrow (DB.atom 1) (DB.atom 0))

-- The inhabitant `λ a. λ b. a` in the atomic variant,
-- in the style of both a term and a normal form.

av-tm : AV.Tm ([] ⊢ av-ty)
av-tm = AV.lam (AV.lam (AV.wkn AV.var))

av-nf : AV.Nf ([] ⊢ av-ty)
av-nf = AV.nf-lam (AV.nf-lam (AV.nf-of-ne (AV.ne-wkn AV.ne-var)))

-- The inhabitant `λ a. λ b. a` in the De Bruijn variant,
-- in the style of both a term and a normal form.

db-tm : DB.Tm ([] ⊢ db-ty)
db-tm = DB.lam (DB.lam (DB.var (# 1)))

db-nf : DB.Nf ([] ⊢ db-ty)
db-nf = DB.nf-lam (DB.nf-lam (DB.nf-of-ne (DB.ne-var (# 1))))

----------------------------------------------------------------------------------------------------

main : Main
main = run (putStrLn "Hello, World!")
