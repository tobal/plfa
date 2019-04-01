
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p
  ≡⟨⟩
    zero
  ≡⟨⟩
   zero * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
  ≡⟨⟩
    suc (m * n) * p
  ≡⟨⟩
    suc ((m * n) * p)
  ≡⟨ cong suc (*-assoc m n p) ⟩
    suc (m * (n * p))
  ≡⟨⟩
    suc m * (n * p)
  ∎

