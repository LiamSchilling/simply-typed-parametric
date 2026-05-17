{-# OPTIONS --guardedness #-}

module Main where

open import Data.Fin using (#_)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import IO
open import SimplyTyped.Langs.Type.STLC ℕ
import SimplyTyped.Langs.Term.AtomicVarSTLC ℕ as AV
import SimplyTyped.Langs.Term.DeBruijnVarSTLC ℕ as DB

----------------------------------------------------------------------------------------------------
-- Variants of STLC with both atomic (start/weakening) variables and De-Bruijn-indexed variables
----------------------------------------------------------------------------------------------------

-- The simple type `A → B → A`.

ty : Ty
ty = arrow (atom 0) (arrow (atom 1) (atom 0))

-- The inhabitant `λ a. λ b. a` in the atomic variant,
-- in the style of both a term and a normal form.

av-tm : AV.Tm ([] ⊢ ty)
av-tm = AV.lam (AV.lam (AV.wkn AV.var))

av-nf : AV.Nf ([] ⊢ ty)
av-nf = AV.nf-lam (AV.nf-lam (AV.nf-of-ne (AV.ne-wkn AV.ne-var)))

av-tm-of-nf : AV.Tm ([] ⊢ ty)
av-tm-of-nf = AV.nf-to-tm av-nf

-- The inhabitant `λ a. λ b. a` in the De Bruijn variant,
-- in the style of both a term and a normal form.

db-tm : DB.Tm ([] ⊢ ty)
db-tm = DB.lam (DB.lam (DB.var (# 1)))

db-nf : DB.Nf ([] ⊢ ty)
db-nf = DB.nf-lam (DB.nf-lam (DB.nf-of-ne (DB.ne-var (# 1))))

db-tm-of-nf : DB.Tm ([] ⊢ ty)
db-tm-of-nf = DB.nf-to-tm db-nf

----------------------------------------------------------------------------------------------------

main : Main
main = run (putStrLn "Hello, World!")
