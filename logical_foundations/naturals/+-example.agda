open import Data.Nat

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
{-# BUILTIN NATURAL ℕ #-}

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4))
  ≡⟨⟩
    suc (suc (suc 4)
  ≡⟨⟩
    7
  ∎

