/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTTotalMainLower
import ErdosProblems.Erdos4b.FGKMTPreSieveRange

/-! # A uniform subpower lower bound for the chosen total-weight scale -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem chosenPreSieveWeightMassScale_ge_exp_cube {k B R : ℕ}
    (hk : 2 ≤ k) (hlog : 10000 ≤ Real.log k) (hB : B = 1 ∨ B.Prime)
    (hR : 1 ≤ Real.log (R : ℝ)) (h : Fin k → ℕ)
    (hadm : BoundedGaps.IsAdmissible (Finset.univ.image h)) :
    Real.exp (-22 * (k : ℝ) ^ 3) ≤
      commonWeightMassScale k (dimensionPreSieveModulus k B)
        (B * dimensionPreSieveModulus k B) R h := by
  obtain ⟨n, hn⟩ := exists_dimensionPreSieveCondition k B h hadm
  have hm := commonWeightMassScale_ge_exp_cube (by norm_num : (0 : ℝ) ≤ 8) hk hlog hB
    (dimensionPreSieveModulus_pos k B) (dimensionPreSieveModulus_coprime hB) hR
    (fun _p hp hpk => small_prime_dvd_dimensionPreSieve hp hpk)
    (dimensionPreSieveModulus_le_exp k B) h hn
  norm_num at hm ⊢
  exact hm

theorem eventually_commonWeightMassScale_ge_inv_rpow {e : ℝ} (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, ∀ k B : ℕ,
      2 ≤ k → 10000 ≤ Real.log k →
      (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) → (B = 1 ∨ B.Prime) →
      ∀ h : Fin k → ℕ, BoundedGaps.IsAdmissible (Finset.univ.image h) →
      (x : ℝ) ^ (-e) ≤
        commonWeightMassScale k (dimensionPreSieveModulus k B)
          (B * dimensionPreSieveModulus k B) (dimensionSieveRadius x) h := by
  filter_upwards [eventually_dimensionSieveRadius_window,
    eventually_uniform_cubeDimension_loss (by norm_num : (0 : ℝ) < 22)
      (by norm_num : (0 : ℝ) < 1), eventually_exp_mul_sqrtLog_le_rpow 1 he] with x hR hcost heX
  intro k B hk hlog hdim hB h hadm
  have hcost' : 22 * (k : ℝ) ^ 3 ≤ Real.sqrt (Real.log (x : ℝ)) := by
    have hS := mul_le_mul_of_nonneg_left (one_le_dimensionLogLossScale x)
      (by positivity : 0 ≤ 22 * (k : ℝ) ^ 3)
    have hC := hcost k hdim
    simp only [mul_one, one_mul] at hS hC
    exact hS.trans hC
  have hexp : Real.exp (Real.sqrt (Real.log (x : ℝ))) ≤ (x : ℝ) ^ e := by
    simpa only [one_mul] using heX
  have hinv : (x : ℝ) ^ (-e) ≤ Real.exp (-Real.sqrt (Real.log (x : ℝ))) := by
    rw [Real.rpow_neg (Nat.cast_nonneg x), Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hexp
  calc
    _ ≤ Real.exp (-Real.sqrt (Real.log (x : ℝ))) := hinv
    _ ≤ Real.exp (-22 * (k : ℝ) ^ 3) := Real.exp_monotone (by linarith)
    _ ≤ _ := chosenPreSieveWeightMassScale_ge_exp_cube hk hlog hB hR.2.2.1 h hadm

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.chosenPreSieveWeightMassScale_ge_exp_cube
#print axioms Erdos4b.FGKMT.eventually_commonWeightMassScale_ge_inv_rpow
