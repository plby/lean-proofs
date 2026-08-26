import ErdosProblems.Erdos796.Core

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Multiplicative Sidon consequences of compatibility

The ordered convolution bound `≤ 2` implies uniqueness of unordered
factorizations, including the interaction between a diagonal factorization
and an off-diagonal one.  This is the local contradiction used whenever a
four-cycle is converted into an equal-product relation.
-/

namespace Erdos796

/-- A set has unique unordered product factorizations. -/
def UnorderedProductUnique (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c d : ℕ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a * b = c * d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Three distinct ordered solutions force convolution at least three. -/
theorem three_solutions_le_productRepCount {A : Finset ℕ} {m : ℕ}
    {x₁ x₂ x₃ : ℕ × ℕ}
    (h₁ : x₁.1 ∈ A ∧ x₁.2 ∈ A ∧ x₁.1 * x₁.2 = m)
    (h₂ : x₂.1 ∈ A ∧ x₂.2 ∈ A ∧ x₂.1 * x₂.2 = m)
    (h₃ : x₃.1 ∈ A ∧ x₃.2 ∈ A ∧ x₃.1 * x₃.2 = m)
    (h₁₂ : x₁ ≠ x₂) (h₁₃ : x₁ ≠ x₃) (h₂₃ : x₂ ≠ x₃) :
    3 ≤ productRepCount A A m := by
  let S : Finset (ℕ × ℕ) := {x₁, x₂, x₃}
  have hcard : S.card = 3 := by
    simp [S, h₁₂, h₁₃, h₂₃]
  have hsub : S ⊆ (A ×ˢ A).filter (fun uv => uv.1 * uv.2 = m) := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₁.1, h₁.2.1⟩, h₁.2.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₂.1, h₂.2.1⟩, h₂.2.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h₃.1, h₃.2.1⟩, h₃.2.2⟩
  rw [productRepCount]
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- An ordered convolution bound of two gives uniqueness up to swapping. -/
theorem unorderedProductUnique_of_conv_le_two {A : Finset ℕ}
    (hconv : ∀ m : ℕ, productRepCount A A m ≤ 2) :
    UnorderedProductUnique A := by
  intro a b c d ha hb hc hd hprod
  by_cases hab : a = b
  · subst b
    by_cases hcd : c = d
    · subst d
      have hac : a = c := by
        apply (mul_self_inj (Nat.zero_le a) (Nat.zero_le c)).mp
        exact hprod
      exact Or.inl ⟨hac, hac⟩
    · have h₁₂ : (a, a) ≠ (c, d) := by
        intro h
        have hac : a = c := congrArg Prod.fst h
        have had : a = d := congrArg Prod.snd h
        exact hcd (hac.symm.trans had)
      have h₁₃ : (a, a) ≠ (d, c) := by
        intro h
        have had : a = d := congrArg Prod.fst h
        have hac : a = c := congrArg Prod.snd h
        exact hcd (hac.symm.trans had)
      have h₂₃ : (c, d) ≠ (d, c) := by
        intro h
        exact hcd (congrArg Prod.fst h)
      have hthree : 3 ≤ productRepCount A A (a * a) :=
        three_solutions_le_productRepCount
          ⟨ha, ha, rfl⟩
          ⟨hc, hd, hprod.symm⟩
          ⟨hd, hc, by simpa [Nat.mul_comm] using! hprod.symm⟩
          h₁₂ h₁₃ h₂₃
      have hupper := hconv (a * a)
      omega
  · by_cases hacbd : a = c ∧ b = d
    · exact Or.inl hacbd
    · by_cases hadbc : a = d ∧ b = c
      · exact Or.inr hadbc
      · have h₁₂ : (a, b) ≠ (b, a) := by
          intro h
          exact hab (congrArg Prod.fst h)
        have h₁₃ : (a, b) ≠ (c, d) := by
          intro h
          apply hacbd
          exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
        have h₂₃ : (b, a) ≠ (c, d) := by
          intro h
          apply hadbc
          exact ⟨congrArg Prod.snd h, congrArg Prod.fst h⟩
        have hthree : 3 ≤ productRepCount A A (a * b) :=
          three_solutions_le_productRepCount
            ⟨ha, hb, rfl⟩
            ⟨hb, ha, Nat.mul_comm b a⟩
            ⟨hc, hd, hprod.symm⟩
            h₁₂ h₁₃ h₂₃
        have hupper := hconv (a * b)
        omega

/-- Every fibre of a compatible family is multiplicatively Sidon, with
diagonal factorizations included. -/
theorem compatible_fiber_unorderedProductUnique {U : ℕ → Finset ℕ}
    (hU : Compatible U) (j : ℕ) : UnorderedProductUnique (U j) := by
  exact unorderedProductUnique_of_conv_le_two (hU.2 j j)

end Erdos796
