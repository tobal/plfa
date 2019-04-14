module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- associativity of addition: (m + n) + p ≡ m + (n + p)
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p ≡⟨⟩
    suc (m + n) + p ≡⟨⟩
    suc ((m + n) + p) ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p)) ≡⟨⟩
    suc m + (n + p)
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

{-
  identity: m + 0 ≡ m, analogous to 0 + m ≡ m,
  which is the base case of addition
-}
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero ≡⟨⟩
    suc (m + zero) ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-identity′ : ∀ (m : ℕ) → m + zero ≡ m
+-identity′ zero = refl
+-identity′ (suc m) rewrite +-identity′ m = refl

{- 
  m + suc n ≡ suc (m + n), analogous to suc m + n ≡ suc (m + n), 
  which is the inductive case of addition for ∀ (m n :ℕ) 
-}
+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n ≡⟨⟩
    suc (m + suc n) ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n)) ≡⟨⟩
    suc (suc m + n)
  ∎

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

-- commutativity: m + n ≡ n + m
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero ≡⟨ +-identityʳ m ⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n ≡⟨ +-suc m n ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨⟩
    suc n + m
  ∎

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- rearrange: (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q) ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q)) ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q) ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
  ∎

-- swap: m + (n + p) ≡ n + (m + p)
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p) ≡⟨ +-comm m (n + p) ⟩
    (n + p) + m ≡⟨ +-assoc n p m ⟩
    n + (p + m) ≡⟨ cong (n +_) (+-comm p m) ⟩
    n + (m + p)
  ∎

+-swap′ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap′ m n p rewrite +-comm′ m (n + p) | +-assoc′ n p m | +-comm′ p m  = refl

-- distributivity of multiplication over addition: (m + n) * p ≡ m * p + n * p
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    (suc m + n) * p ≡⟨⟩
    suc (m + n) * p ≡⟨⟩
    p + (m + n) * p ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p) ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    p + m * p + n * p ≡⟨⟩
    suc m * p + n * p
  ∎

*-distrib-+′ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+′ zero n p = refl
*-distrib-+′ (suc m) n p rewrite *-distrib-+′ m n p | sym (+-assoc′ p (m * p) (n * p)) = refl

-- associativity of multiplication: (m * n) * p ≡ m * (n * p)
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p ≡⟨⟩
    (n + m * n) * p ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + (m * n) * p ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
    n * p + m * (n * p) ≡⟨⟩
    suc m * (n * p)
  ∎

*-assoc′ : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc′ zero n p = refl
*-assoc′ (suc m) n p rewrite *-distrib-+′ n (m * n) p | *-assoc′ m n p = refl

-- multiplication by zero, analogous to the base case of multiplication.
n*0≡0 : ∀ (n : ℕ) → n * zero ≡ zero
n*0≡0 zero =
  begin
    zero * zero ≡⟨⟩
    zero
  ∎
n*0≡0 (suc n) =
  begin
    suc n * zero ≡⟨ n*0≡0 n ⟩
    zero
  ∎

n*0≡0′ : ∀ (n : ℕ) → n * zero ≡ zero
n*0≡0′ zero = refl
n*0≡0′ (suc n) rewrite n*0≡0′ n = refl

-- multiplication, analogous to the inductive case of multiplication.
*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n =
  begin
    zero * suc n ≡⟨⟩
    zero + zero * n
  ∎
*-suc (suc m) n =
  begin
    suc m * suc n ≡⟨⟩
    suc n + m * suc n ≡⟨ cong (suc n +_) (*-suc m n) ⟩
    suc (n + (m + m * n)) ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
    suc (n + m + m * n) ≡⟨ cong suc (cong (_+ (m * n)) (+-comm n m)) ⟩
    suc (m + n + m * n) ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
    suc m + (n + m * n) ≡⟨⟩
    suc m + suc m * n
  ∎

*-suc′ : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc′ zero n = refl
*-suc′ (suc m) n rewrite *-suc′ m n | sym (+-assoc′ n m (m * n)) | +-comm n m | +-assoc m n (m * n)= refl

-- commutitavity of multiplication: m * n ≡ n * m
*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero =
  begin
    m * zero ≡⟨ n*0≡0 m ⟩
    zero * m
  ∎
*-comm m (suc n) =
  begin
    m * suc n ≡⟨ *-suc m n ⟩
    m + m * n ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m ≡⟨⟩
    suc n * m
  ∎

*-comm′ : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm′ m zero rewrite n*0≡0′ m = refl
*-comm′ m (suc n) rewrite *-suc′ m n | *-comm′ m n = refl

-- zero monus (n : ℕ)
0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero =
  begin
    zero ∸ zero ≡⟨⟩
    zero
  ∎
0∸n≡0 (suc n) =
  begin
    zero ∸ suc n ≡⟨⟩
    zero
  ∎

0∸n≡0′ : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0′ zero = refl
0∸n≡0′ (suc n) = refl

-- associativity of monus: m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p =
  begin
    zero ∸ n ∸ p ≡⟨ cong (_∸ p) (0∸n≡0 n) ⟩
    zero ∸ p ≡⟨ 0∸n≡0 p ⟩
    zero ≡⟨ sym (0∸n≡0 (n + p)) ⟩
    zero ∸ (n + p)
  ∎
∸-+-assoc (suc m) zero p =
  begin
    suc m ∸ zero ∸ p ≡⟨⟩
    suc m ∸ p ≡⟨⟩
    suc m ∸ (zero + p)
  ∎
∸-+-assoc (suc m) (suc n) p =
  begin
    suc m ∸ suc n ∸ p ≡⟨⟩
    m ∸ n ∸ p ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p) ≡⟨⟩
    suc m ∸ suc (n + p) ≡⟨⟩
    suc m ∸ (suc n + p)
  ∎

∸-+-assoc′ : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc′ zero zero p = refl
∸-+-assoc′ zero (suc n) p rewrite 0∸n≡0 p = refl
∸-+-assoc′ (suc m) zero p = refl
∸-+-assoc′ (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl
