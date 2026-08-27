/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteKernel
import ErdosProblems.Erdos4b.FGKMTTensorDenominators

/-!
# Uniform shifted hypotheses for both absolute-kernel denominators

The real parameter `a` covers both `p - 1` and `p - 2` in the numerator
of the local absolute weight. The allowed coordinate count retains the
one-coordinate loss in the pinned case.
-/

namespace Erdos4b.FGKMT

noncomputable section

theorem absoluteDenominator_real_bounds {k p a s : ℝ} (hk : 2 ≤ k)
    (hp : 2 * k ^ 2 < p) (ha : 1 ≤ a) (ha2 : a ≤ 2)
    (hs : 0 ≤ s) (hsa : s + a ≤ k) :
    p / 2 ≤ (p - k) ^ 2 / (p - a) + s ∧
      |(p - k) ^ 2 / (p - a) + s - p| ≤ 2 * k ∧
      (p - k) ^ 2 / (p - a) + s ≤ p - 1 := by
  have hk0 : 0 ≤ k := by linarith
  have hp0 : 0 < p := by nlinarith [sq_nonneg k]
  have h4k : 4 * k < p := by nlinarith
  have hpa : 0 < p - a := by linarith
  have hak : a ≤ k := by linarith
  have hid : (p - k) ^ 2 / (p - a) = p - 2 * k + a + (k - a) ^ 2 / (p - a) := by
    field_simp [hpa.ne']
    ring
  have hrem0 : 0 ≤ (k - a) ^ 2 / (p - a) := div_nonneg (sq_nonneg _) hpa.le
  have hsq : (k - a) ^ 2 ≤ (k - 1) ^ 2 := by
    apply pow_le_pow_left₀ (by linarith : 0 ≤ k - a)
    linarith
  have hrem : (k - a) ^ 2 / (p - a) ≤ 1 / 2 := by
    apply (div_le_iff₀ hpa).mpr
    nlinarith
  have hlower : p / 2 ≤ (p - k) ^ 2 / (p - a) := by
    apply (le_div_iff₀ hpa).mpr
    nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr h4k.le)]
  have hupper : (p - k) ^ 2 / (p - a) + s ≤ p - 1 := by
    rw [hid]
    linarith
  refine ⟨by linarith, ?_, hupper⟩
  rw [abs_le, hid]
  constructor <;> linarith

theorem absoluteSieveDenominator_chain {k M j a : ℕ} (hk : 2 ≤ k)
    (ha : 1 ≤ a) (ha2 : a ≤ 2) (hj : j + a ≤ k + 1)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ M) :
    ∀ s : ℕ, s < j → ∀ p : ℕ, p.Prime → ¬p ∣ M →
      (p : ℝ) / 2 ≤ absoluteSieveDenominator a k p + s ∧
        |absoluteSieveDenominator a k p + s - p| ≤ 2 * (k : ℝ) ∧
        absoluteSieveDenominator a k p + s ≤ p - 1 := by
  intro s hs p hp hpM
  have hrough : 2 * k ^ 2 < p := by
    by_contra hnot
    exact hpM (hsmall p hp (by omega))
  exact absoluteDenominator_real_bounds (by exact_mod_cast hk) (by exact_mod_cast hrough)
    (by exact_mod_cast ha) (by exact_mod_cast ha2) (Nat.cast_nonneg s)
    (by exact_mod_cast (show s + a ≤ k by omega))

theorem absoluteDenominator_local_ratio {k p a j : ℝ} (hk : 2 ≤ k)
    (hp : 2 * k ^ 2 < p) (_ha : 1 ≤ a) (ha2 : a ≤ 2) (hj : 0 ≤ j) :
    (1 + j / ((p - k) ^ 2 / (p - a))) / (1 + j / (p - k)) =
      1 + j * (k - a) / ((p - k) * (p - k + j)) := by
  have hpk : 0 < p - k := by nlinarith
  have hpa : 0 < p - a := by nlinarith
  have hpj : 0 < p - k + j := by linarith
  field_simp [hpk.ne', hpa.ne', hpj.ne']
  ring

theorem absoluteDenominator_local_ratio_le {k p a j : ℝ} (hk : 2 ≤ k)
    (hp : 2 * k ^ 2 < p) (ha : 1 ≤ a) (ha2 : a ≤ 2)
    (hj : 0 ≤ j) (hjk : j ≤ k) :
    (1 + j / ((p - k) ^ 2 / (p - a))) / (1 + j / (p - k)) ≤ 1 + 4 * k ^ 2 / p ^ 2 := by
  have hp0 : 0 < p := by nlinarith [sq_nonneg k]
  have hhalf : p / 2 ≤ p - k := by nlinarith
  have hnum : j * (k - a) ≤ k ^ 2 := by
    have hprod := mul_le_mul hjk (show k - a ≤ k by linarith)
      (show 0 ≤ k - a by linarith) (show 0 ≤ k by linarith)
    simpa only [pow_two] using hprod
  have hden : p ^ 2 / 4 ≤ (p - k) * (p - k + j) := by
    have hprod := mul_le_mul hhalf (show p / 2 ≤ p - k + j by linarith)
      (show 0 ≤ p / 2 by positivity) (show 0 ≤ p - k by linarith)
    nlinarith
  rw [absoluteDenominator_local_ratio hk hp ha ha2 hj]
  apply add_le_add le_rfl
  calc
    _ ≤ k ^ 2 / (p ^ 2 / 4) := div_le_div₀ (sq_nonneg k) hnum (by positivity) hden
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.absoluteSieveDenominator_chain
#print axioms Erdos4b.FGKMT.absoluteDenominator_local_ratio_le
