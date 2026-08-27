/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionLossAbsorption

/-!
# Absorbing the exact coefficient and Cauchy factors

The modulus-size hypothesis is explicit and will be supplied by the
presieve construction. Dimensions and radii vary below the displayed bounds.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem pinnedErrorLoss_le_exp {K C H : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C) (hH : 0 ≤ H)
    {m W R x : ℕ} (hR : 2 ≤ R) (hRx : R ≤ x)
    (hW : (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2)) :
    K * W * Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
        (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) ≤
      Real.exp ((K + H + 2 * C + 18) * (m + 1 : ℕ) ^ 2 * dimensionLogLossScale x) := by
  let k : ℝ := (m + 1 : ℕ)
  let S := dimensionLogLossScale x
  have hk1 : 1 ≤ k := by
    dsimp [k]
    exact_mod_cast (by omega : 1 ≤ m + 1)
  have hk0 : 0 ≤ k := zero_le_one.trans hk1
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hkk : k ≤ k ^ 2 := by nlinarith
  have hS1 : 1 ≤ S := one_le_dimensionLogLossScale x
  have hS0 : 0 ≤ S := zero_le_one.trans hS1
  have hprod : 1 ≤ k ^ 2 * S := by
    simpa only [one_mul] using mul_le_mul hk2 hS1 (by norm_num : (0 : ℝ) ≤ 1) (sq_nonneg k)
  have hKbound : K ≤ Real.exp (K * k ^ 2 * S) := by
    calc
      _ ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
      _ ≤ _ := Real.exp_monotone (by
        simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hprod hK)
  have hWbound : (W : ℝ) ≤ Real.exp (H * k ^ 2 * S) := by
    apply hW.trans
    apply Real.exp_monotone
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hS1 (mul_nonneg hH (sq_nonneg k))
  have hcoeff : Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) ≤
      Real.exp ((2 * C) * k ^ 2 * S) := by
    apply Real.exp_monotone
    have hck : C * ((m : ℝ) + 1) = C * k := by simp [k]
    rw [hck]
    calc
      _ ≤ (C * k) * (2 * S) :=
        mul_le_mul_of_nonneg_left (one_add_log_natLog_le_dimensionScale hR hRx)
          (mul_nonneg hC hk0)
      _ ≤ (C * k ^ 2) * (2 * S) := by gcongr
      _ = _ := by ring
  have hF : (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) ≤ Real.exp (18 * k ^ 2 * S) :=
    cauchyRadius_pow_le_exp (by omega) hRx
  calc
    _ ≤ Real.exp (K * k ^ 2 * S) * Real.exp (H * k ^ 2 * S) *
        Real.exp ((2 * C) * k ^ 2 * S) * Real.exp (18 * k ^ 2 * S) := by
      exact mul_le_mul
        (mul_le_mul (mul_le_mul hKbound hWbound (Nat.cast_nonneg W) (Real.exp_pos _).le)
          hcoeff (Real.exp_pos _).le (by positivity)) hF (by positivity) (by positivity)
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      dsimp [k, S]
      push_cast
      ring

theorem eventually_pinnedError_scale_absorbed {K C H d : ℝ}
    (hK : 0 < K) (hC : 0 < C) (hH : 0 < H) (hd : 0 < d) :
    ∀ᶠ x : ℕ in atTop, ∀ m W R : ℕ, 2 ≤ R → R ≤ x →
      (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
      (W : ℝ) ≤ Real.exp (H * (m + 1 : ℕ) ^ 2) →
      K * W * x * Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
          (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2) *
            Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) ≤
        (x : ℝ) * Real.exp (-(d / 2) * Real.sqrt (Real.log (x : ℝ))) := by
  have hsum : 0 < K + H + 2 * C + 18 := by positivity
  filter_upwards [eventually_uniform_squareDimension_loss hsum
    (by positivity : 0 < d / 2)] with x hx
  intro m W R hR hRx hdim hW
  have hbound := pinnedErrorLoss_le_exp hK.le hC.le hH.le hR hRx hW
  have habsorb := hx (m + 1) (by omega) hdim
  have hexp := Real.exp_monotone habsorb
  calc
    _ = (x : ℝ) * (K * W *
        Real.exp (C * (m + 1) * (1 + Real.log (Nat.log 2 R : ℕ))) *
          (1 + Real.log (R ^ 2 : ℕ)) ^ ((3 * m) ^ 2)) *
            Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) := by ring
    _ ≤ (x : ℝ) * Real.exp ((d / 2) * Real.sqrt (Real.log (x : ℝ))) *
        Real.exp (-d * Real.sqrt (Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound.trans hexp)
        (Nat.cast_nonneg x)) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedErrorLoss_le_exp
#print axioms Erdos4b.FGKMT.eventually_pinnedError_scale_absorbed
