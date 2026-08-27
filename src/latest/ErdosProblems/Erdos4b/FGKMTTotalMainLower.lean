/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProfileExponentialLower
import ErdosProblems.Erdos4b.FGKMTCommonWeightNormalization

/-! # Explicit lower bounds for the genuine total-weight main scale -/

namespace Erdos4b.FGKMT

noncomputable section

theorem dimensionProfileEnergy_ge_exp_square {k j : ℕ} (hk : 0 < k)
    (hlog : 10000 ≤ Real.log k) (hj : j ≤ k) :
    Real.exp (-5 * (k : ℝ) ^ 2) ≤ dimensionProfileEnergy k j := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hT : 0 < sieveProfileScale k := zero_lt_one.trans_le (profile_scales_bounds hk hlog).1
  have hjR : (j : ℝ) ≤ k := by exact_mod_cast hj
  have hmass := pow_le_pow_left₀ (Real.exp_pos _).le
    (exp_neg_two_mul_le_inv_profileScale hk hlog) j
  have hthird : Real.exp (-3) ≤ (1 / 3 : ℝ) :=
    exp_neg_le_inv_of_le_exp (by norm_num) (by linarith [Real.add_one_le_exp 3])
  calc
    _ ≤ Real.exp (-2 * (k : ℝ)) ^ j * Real.exp (-3) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_monotone
      nlinarith [mul_le_mul_of_nonneg_left hjR (by positivity : (0 : ℝ) ≤ k)]
    _ ≤ (1 / (2 * sieveProfileScale k)) ^ j / 3 := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using
        mul_le_mul hmass hthird (Real.exp_pos _).le
          (pow_nonneg (by positivity : 0 ≤ 1 / (2 * sieveProfileScale k)) j)
    _ ≤ _ := dimensionProfileEnergy_explicit_lower hk hlog hj

theorem commonSieveMainTerm_ge_exp_cube {k B W R : ℕ} {H : ℝ}
    (_hH : 0 ≤ H) (hk : 2 ≤ k) (hlog : 10000 ≤ Real.log k)
    (hB : B = 1 ∨ B.Prime) (hW : 0 < W) (hBW : B.Coprime W)
    (hR : 1 ≤ Real.log (R : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ B * W)
    (hsize : (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2)) :
    Real.exp (-(H + 6) * (k : ℝ) ^ 3) ≤ commonSieveMainTerm k (B * W) R := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk23 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1 (by omega)
  have hBpos : 0 < B := hB.elim (by rintro rfl; omega) Nat.Prime.pos
  have hM : 0 < B * W := Nat.mul_pos hBpos hW
  have hb := totientDensity_ge_exp_dimension hB hW hBW (by omega : 1 ≤ k) hsize
  have hP : Real.exp (-(H + 1) * (k : ℝ) ^ 3) ≤
      multivariateSieveConstant (B * W) (actualSieveDenominator false k) k := by
    calc
      _ = Real.exp (-(H + 1) * (k : ℝ) ^ 2) ^ k := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ (((B * W).totient : ℝ) / (B * W)) ^ k :=
        pow_le_pow_left₀ (Real.exp_pos _).le hb k
      _ ≤ _ := by
        simpa only [Nat.cast_mul] using
          totientDensity_pow_le_actual_multivariate hk hM le_rfl hsmall
  have hP0 := (Real.exp_pos _).le.trans hP
  have hPL : Real.exp (-(H + 1) * (k : ℝ) ^ 3) ≤
      multivariateSieveConstant (B * W) (actualSieveDenominator false k) k * Real.log R ^ k :=
    hP.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ hR) hP0)
  have hI := dimensionProfileEnergy_ge_exp_square (by omega : 0 < k) hlog (le_refl k)
  calc
    _ ≤ Real.exp (-(H + 1) * (k : ℝ) ^ 3) * Real.exp (-5 * (k : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_monotone
      nlinarith
    _ ≤ _ := mul_le_mul hPL hI (Real.exp_pos _).le
      (mul_nonneg hP0 (pow_nonneg (by linarith) k))

theorem commonWeightMassScale_ge_exp_cube {k B W R : ℕ} {H : ℝ}
    (hH : 0 ≤ H) (hk : 2 ≤ k) (hlog : 10000 ≤ Real.log k)
    (hB : B = 1 ∨ B.Prime) (hW : 0 < W) (hBW : B.Coprime W)
    (hR : 1 ≤ Real.log (R : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ 2 * k ^ 2 → p ∣ B * W)
    (hsize : (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2))
    (h : Fin k → ℕ) {n : ℤ} (hn : preSieveCondition W (fun i => (h i : ℤ)) n) :
    Real.exp (-(2 * H + 6) * (k : ℝ) ^ 3) ≤ commonWeightMassScale k W (B * W) R h := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hk23 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := pow_le_pow_right₀ hk1 (by omega)
  have hdensity : Real.exp (-H * (k : ℝ) ^ 2) ≤ preSieveDensity W (fun i => (h i : ℤ)) := by
    have h := exp_neg_le_inv_of_le_exp (by exact_mod_cast hW) hsize
    have he : Real.exp (-H * (k : ℝ) ^ 2) ≤ 1 / (W : ℝ) := by
      simpa only [neg_mul] using h
    exact he.trans (preSieveDensity_ge_inv_of_witness hW _ hn)
  have hmain := commonSieveMainTerm_ge_exp_cube hH hk hlog hB hW hBW hR hsmall hsize
  calc
    _ ≤ Real.exp (-H * (k : ℝ) ^ 2) * Real.exp (-(H + 6) * (k : ℝ) ^ 3) := by
      rw [← Real.exp_add]
      apply Real.exp_monotone
      nlinarith [mul_le_mul_of_nonneg_left hk23 hH]
    _ ≤ _ := mul_le_mul hdensity hmain (Real.exp_pos _).le (preSieveDensity_nonneg W _)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.dimensionProfileEnergy_ge_exp_square
#print axioms Erdos4b.FGKMT.commonSieveMainTerm_ge_exp_cube
#print axioms Erdos4b.FGKMT.commonWeightMassScale_ge_exp_cube
