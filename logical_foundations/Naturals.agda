module logical_foundations.Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ  #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)
{-# BUILTIN NATPLUS _+_  #-}
-- zero + n = n             -- 0 + n = n
-- suc m + n = suc (m + n)  -- (1 + m) + n = 1 + (m + n)

infixl 6 _+_

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero            -- 0 * n = 0
suc m * n = n + (m * n)    -- (1 + m) * n = n + (m * n)
{-# BUILTIN NATTIMES _*_  #-}

infixl 7 _*_

_ : 2 * 3 ≡ 6
_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ suc n = m * (m ^ n)

infixl 8 _^_

_ : 2 ^ 3 ≡ 8
_ =
  begin
    2 ^ 3
  ≡⟨⟩
    2 * (2 ^ 2)
  ≡⟨⟩
    2 * (2 * (2 ^ 1))
  ≡⟨⟩
    2 * (2 * (2 * (2 ^ 0)))
  ≡⟨⟩
    2 * (2 * (2 * 1))
  ≡⟨⟩
    8
  ∎

_ : 3 ^ 4 ≡ 81
_ = refl

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n
{-# BUILTIN NATMINUS _∸_  #-}

infixl 6 _∸_

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 b) = x1 b
inc (x1 b) = x0 (inc b)

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

_ : inc (x1 x1 x1 x1 nil) ≡ x0 x0 x0 x0 x1 nil
_ = refl

to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

_ : to 0 ≡ x0 nil
_ = refl

_ : to 1 ≡ x1 nil
_ = refl

_ : to 2 ≡ x0 x1 nil
_ = refl

_ : to 3 ≡ x1 x1 nil
_ = refl

_ : to 14 ≡ x0 x1 x1 x1 nil
_ = refl

two = suc (suc zero)

from : Bin → ℕ
from nil = zero
from (x0 n) = two * (from n)
from (x1 n) = suc (two * (from n))

_ : from nil ≡ zero
_ = refl

_ : from (x0 nil) ≡ zero
_ = refl

_ : from (x1 nil) ≡ suc zero
_ = refl

_ : from (x0 x1 nil) ≡ two
_ = refl

_ : from (x0 x1 nil) ≡ two * suc zero
_ = refl

_ : from (x1 x1 nil) ≡ suc (suc (suc zero))
_ = refl

_ : from (x1 x1 nil) ≡ suc (two * suc zero)
_ = refl

_ : from (x0 x0 x1 nil) ≡ suc (suc (suc (suc zero)))
_ = refl

_ : from (x0 x0 x1 nil) ≡ two * (two * suc zero)
_ = refl

_ : from (x1 x0 x1 nil) ≡ suc (suc (suc (suc (suc zero))))
_ = refl

_ : from (x1 x0 x1 nil) ≡ suc (two * (two * suc zero))
_ = refl
