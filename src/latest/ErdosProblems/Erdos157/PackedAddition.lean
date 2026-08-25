import ErdosProblems.Erdos157.TaggedBlocks

/-! Carry-free pair addition and decoding of packed digit strings. -/

namespace Erdos157.Elementary.PackedDigits

def pairSum (xs ys : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.zipWith (fun x y => (x.1, x.2 + y.2)) xs ys

theorem pairSum_radices {xs ys : List (ℕ × ℕ)}
    (hbase : xs.map Prod.fst = ys.map Prod.fst) :
    (pairSum xs ys).map Prod.fst = xs.map Prod.fst := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [pairSum]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hbase
    | cons y ys =>
      have htail := (List.cons.inj hbase).2
      simpa only [pairSum, List.zipWith_cons_cons, List.map_cons] using
        congrArg (List.cons x.1) (ih htail)

theorem encode_pairSum {xs ys : List (ℕ × ℕ)}
    (hbase : xs.map Prod.fst = ys.map Prod.fst) :
    MixedRadix.encode (pairSum xs ys) = MixedRadix.encode xs + MixedRadix.encode ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [pairSum]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hbase
    | cons y ys =>
      rcases x with ⟨b, d⟩
      rcases y with ⟨c, e⟩
      have hhead := (List.cons.inj hbase).1
      have htail := (List.cons.inj hbase).2
      change b = c at hhead
      subst c
      change MixedRadix.encode ((b, d + e) :: pairSum xs ys) = _
      rw [MixedRadix.encode_cons, MixedRadix.encode_cons, MixedRadix.encode_cons, ih htail]
      ring

theorem pairSum_valid {xs ys : List (ℕ × ℕ)} (hx : HalfValid xs) (hy : HalfValid ys)
    (hbase : xs.map Prod.fst = ys.map Prod.fst) : MixedRadix.Valid (pairSum xs ys) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [pairSum, MixedRadix.Valid]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hbase
    | cons y ys =>
      rcases x with ⟨b, d⟩
      rcases y with ⟨c, e⟩
      have hhead := (List.cons.inj hbase).1
      have htail := (List.cons.inj hbase).2
      change b = c at hhead
      subst c
      change 2 ≤ b ∧ d + e < b ∧ MixedRadix.Valid (pairSum xs ys)
      exact ⟨hx.1, by have := hx.2.1; have := hy.2.1; omega, ih hx.2.2 hy.2.2 htail⟩

theorem pairSum_eq_of_encode_add_eq {x₁ x₂ x₃ x₄ : List (ℕ × ℕ)}
    (h₁ : HalfValid x₁) (h₂ : HalfValid x₂) (h₃ : HalfValid x₃) (h₄ : HalfValid x₄)
    (h₁₂ : x₁.map Prod.fst = x₂.map Prod.fst) (h₁₃ : x₁.map Prod.fst = x₃.map Prod.fst)
    (h₃₄ : x₃.map Prod.fst = x₄.map Prod.fst)
    (heq : MixedRadix.encode x₁ + MixedRadix.encode x₂ =
      MixedRadix.encode x₃ + MixedRadix.encode x₄) : pairSum x₁ x₂ = pairSum x₃ x₄ := by
  apply MixedRadix.encode_injective_of_valid (pairSum_valid h₁ h₂ h₁₂) (pairSum_valid h₃ h₄ h₃₄)
  · rw [pairSum_radices h₁₂, pairSum_radices h₃₄]
    exact h₁₃
  · rw [encode_pairSum h₁₂, encode_pairSum h₃₄]
    exact heq

/-- Higher blocks cannot affect a common lower packed prefix of a pair sum. -/
theorem prefix_pair_encode_eq {x₁ x₂ x₃ x₄ : List (ℕ × ℕ)}
    (h₁ : HalfValid x₁) (h₂ : HalfValid x₂) (h₃ : HalfValid x₃) (h₄ : HalfValid x₄)
    (B : ℕ) (hB₁ : MixedRadix.place x₁ = B) (hB₂ : MixedRadix.place x₂ = B)
    (hB₃ : MixedRadix.place x₃ = B) (hB₄ : MixedRadix.place x₄ = B)
    (t₁ t₂ t₃ t₄ : ℕ)
    (heq : (MixedRadix.encode x₁ + B * t₁) + (MixedRadix.encode x₂ + B * t₂) =
      (MixedRadix.encode x₃ + B * t₃) + (MixedRadix.encode x₄ + B * t₄)) :
    MixedRadix.encode x₁ + MixedRadix.encode x₂ = MixedRadix.encode x₃ + MixedRadix.encode x₄ := by
  have hl : MixedRadix.encode x₁ + MixedRadix.encode x₂ < B := by
    rw [← hB₁]
    exact pair_encode_lt_place h₁ h₂ (hB₁.trans hB₂.symm)
  have hr : MixedRadix.encode x₃ + MixedRadix.encode x₄ < B := by
    rw [← hB₃]
    exact pair_encode_lt_place h₃ h₄ (hB₃.trans hB₄.symm)
  have heq' : (MixedRadix.encode x₁ + MixedRadix.encode x₂) + B * (t₁ + t₂) =
      (MixedRadix.encode x₃ + MixedRadix.encode x₄) + B * (t₃ + t₄) := by nlinarith
  have hm := congrArg (fun n => n % B) heq'
  simpa only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using hm

theorem pair_digit_eq_of_pairSum_eq {x₁ x₂ x₃ x₄ : List (ℕ × ℕ)} (j b d₁ d₂ d₃ d₄ : ℕ)
    (h₁ : x₁[j]? = some (b, d₁)) (h₂ : x₂[j]? = some (b, d₂))
    (h₃ : x₃[j]? = some (b, d₃)) (h₄ : x₄[j]? = some (b, d₄))
    (heq : pairSum x₁ x₂ = pairSum x₃ x₄) : d₁ + d₂ = d₃ + d₄ := by
  have h := congrArg (fun xs : List (ℕ × ℕ) => xs[j]?) heq
  simpa only [pairSum, List.getElem?_zipWith, h₁, h₂, h₃, h₄, Option.some.injEq,
    Prod.mk.injEq, true_and] using h

end Erdos157.Elementary.PackedDigits
