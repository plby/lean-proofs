/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverBPZConditional
import ErdosProblems.Erdos387.UniformAnalyticInputs

/-!
# Unconditional BNPZ wide cover

The Bombieri--Vinogradov adapter proves the only analytic hypothesis of the
ported public cover, so its Section 6 interface is now available without a
project-local assumption.
-/

namespace Erdos387.CoverBPZ

/-- Unconditional Section 6 cover data, with arbitrarily large `k`. -/
theorem unconditional_fixed_B_cover_section6_input
    (B K : ℕ) (hB : 3 ≤ B) :
    ∃ S : BPZSection6Input B K, True :=
  fixed_B_cover_section6_input Erdos387.shiftedSiegelWalfiszLower B K hB

/-- Unconditional public fixed-`B` covering theorem. -/
theorem unconditional_fixed_B_cover
    (B K : ℕ) (hB : 3 ≤ B) :
    ∃ k : ℕ, K ≤ k ∧ 3 ≤ k ∧
      ∃ α_k : ℤ,
        ∀ n : ℤ, (k : ℤ) < n → (Nk_formula k : ℤ) ∣ n - α_k →
          (∀ p : ℕ, p.Prime → p ≤ k →
            ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ)) ∧
          (∀ i : ℕ, i < k → ∃ p : ℕ,
            p.Prime ∧ B ≤ p ∧ (p : ℤ) ∣ n - (i : ℤ)) :=
  fixed_B_cover Erdos387.shiftedSiegelWalfiszLower B K hB

end Erdos387.CoverBPZ
