--open import Data.Nat

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
suc (suc (suc (suc (suc (suc (suc (zero)))))))
