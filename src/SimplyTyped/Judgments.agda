module SimplyTyped.Judgments where
    
open import Data.All using (All)
open import Data.List using (List)

private
  variable
    ty : Set

----------------------------------------------------------------------------------------------------
-- Typing judgments
----------------------------------------------------------------------------------------------------

infix 3 _⊢_

-- `J : TyJdg ty` or a typing judgment is the conjunction of
-- a target type `J .τ : ty` and a typing context `J .Γ : List ty`.
record TyJdg (ty : Set) : Set where
  constructor _⊢_
  field
    Γ : List ty
    τ : ty

----------------------------------------------------------------------------------------------------
-- Semantics
----------------------------------------------------------------------------------------------------

denote-ty-jdg : (ty → Set) → (TyJdg ty → Set)
denote-ty-jdg denote-ty (Γ ⊢ τ) = All denote-ty Γ → denote-ty τ
