/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTQuadraticScaleDecay
import ErdosProblems.Erdos4b.FGKMTPinnedQuadraticMean

/-! # Quantitative total and pinned quadratic means at growing dimension -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_commonSieveQuadratic_relative_decay {a H b : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hb : 0 < b) :
    ∀ᶠ x : ℕ in atTop, ∀ k B W R : ℕ,
      2 ≤ k → 10000 ≤ Real.log (k : ℝ) → 0 < B → 0 < W → 1 < R → R ≤ x →
      (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
      (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2) →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      b * Real.log (x : ℝ) ≤ Real.log (R : ℝ) →
      (∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ B * W) →
      |commonSieveQuadratic k (B * W) R - commonSieveMainTerm k (B * W) R| /
        commonSieveMainTerm k (B * W) R ≤ Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
  obtain ⟨C, hC, hquad⟩ := exists_commonSieveQuadratic_relative_error
  filter_upwards [eventually_uniform_sieveQuadraticError_small ha hH hb hC] with x hx
  intro k B W R hk hlog hB hW hR hRx hBsize hWsize hdim hRlower hsmall
  have he := hx k B W R hB hW (by omega) hRx hBsize hWsize hdim hRlower
  exact (hquad hk hlog (Nat.mul_pos hB hW) hR hsmall he.2).trans he.1

theorem eventually_commonPinnedQuadratic_relative_decay {a H b : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hb : 0 < b) :
    ∀ᶠ x : ℕ in atTop, ∀ m B W R : ℕ,
      1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) → 0 < B → 0 < W → 1 < R → R ≤ x →
      (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))) →
      (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2) →
      (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      b * Real.log (x : ℝ) ≤ Real.log (R : ℝ) →
      (∀ p : ℕ, p.Prime → p ≤ 2 * (m + 1) ^ 2 → p ∣ B * W) →
      ∀ j : Fin (m + 1),
        |commonPinnedQuadratic m (B * W) R j - commonPinnedMainTerm m (B * W) R| /
          commonPinnedMainTerm m (B * W) R ≤ Real.log (x : ℝ) ^ (-1 / 4 : ℝ) := by
  obtain ⟨C, hC, hquad⟩ := exists_commonPinnedQuadratic_relative_error
  filter_upwards [eventually_uniform_sieveQuadraticError_small ha hH hb hC] with x hx
  intro m B W R hm hlog hB hW hR hRx hBsize hWsize hdim hRlower hsmall j
  have he := hx (m + 1) B W R hB hW (by omega) hRx hBsize hWsize hdim hRlower
  exact (hquad hm hlog (Nat.mul_pos hB hW) hR hsmall he.2 j).trans he.1

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_commonSieveQuadratic_relative_decay
#print axioms Erdos4b.FGKMT.eventually_commonPinnedQuadratic_relative_decay
