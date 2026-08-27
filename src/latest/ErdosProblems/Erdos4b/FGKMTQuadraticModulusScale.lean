/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTDimensionLogLoss
import ErdosProblems.Erdos4b.FGKMTCommonQuadraticMean

/-! # A common logarithmic modulus bound at growing dimension -/

namespace Erdos4b.FGKMT

noncomputable section

theorem modulusLogScale_le_dimensionScale {N x : ℕ} {A : ℝ}
    (hA : 0 ≤ A) (hL : 1 ≤ Real.log (x : ℝ))
    (hN : Real.log (N : ℝ) ≤ A * Real.log (x : ℝ) ^ 2) :
    modulusLogScale N ≤ (A + 7) * dimensionLogLossScale x := by
  let L := Real.log (x : ℝ)
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hA4 : 0 < A + 4 := by linarith
  have harg : 4 + Real.log (N : ℝ) ≤ (A + 4) * (1 + L) ^ 2 := by
    change Real.log (N : ℝ) ≤ A * L ^ 2 at hN
    nlinarith [mul_nonneg hA hL0, sq_nonneg L]
  have hlog := Real.log_le_log
    (by positivity : 0 < 4 + Real.log (N : ℝ)) harg
  rw [Real.log_mul (ne_of_gt hA4) (by positivity), Real.log_pow] at hlog
  have hself := Real.log_le_self hA4.le
  have hlog0 : 0 ≤ Real.log (1 + L) := Real.log_nonneg (by linarith)
  change 1 + Real.log (4 + Real.log (N : ℝ)) ≤ (A + 7) * (1 + Real.log (1 + L))
  norm_num at hlog
  nlinarith [mul_nonneg hA hlog0]

theorem log_quadraticModulus_le_square {x k B W R : ℕ} {a H : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hL : 1 ≤ Real.log (x : ℝ))
    (hB : 0 < B) (hW : 0 < W) (hR : 0 < R) (hRx : R ≤ x)
    (hBsize : (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))))
    (hWsize : (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2))
    (hk : (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ)) :
    Real.log (B * W * R ^ (2 * k) : ℕ) ≤
      (a + H + 2) * Real.log (x : ℝ) ^ 2 := by
  let L := Real.log (x : ℝ)
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 ≤ L := by linarith
  have hkL : (k : ℝ) ≤ L :=
    hk.trans (Real.rpow_le_self_of_one_le hL1 (by norm_num))
  have hsqrt : Real.sqrt L ≤ L := Real.sqrt_le_self_iff.mpr (Or.inr hL1)
  have hLs : L ≤ L ^ 2 := by nlinarith
  have hk2 : (k : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg k) hkL 2
  have hlogB : Real.log (B : ℝ) ≤ a * Real.sqrt L := by
    have hb := Real.log_le_log (by exact_mod_cast hB) hBsize
    simpa only [Real.log_exp] using hb
  have hlogW : Real.log (W : ℝ) ≤ H * (k : ℝ) ^ 2 := by
    have hw := Real.log_le_log (by exact_mod_cast hW) hWsize
    simpa only [Real.log_exp] using hw
  have hlogR : Real.log (R : ℝ) ≤ L :=
    Real.log_le_log (by exact_mod_cast hR) (by exact_mod_cast hRx)
  have hB0 : (B : ℝ) ≠ 0 := by positivity
  have hW0 : (W : ℝ) ≠ 0 := by positivity
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hlogeq : Real.log (B * W * R ^ (2 * k) : ℕ) =
      Real.log (B : ℝ) + Real.log (W : ℝ) + 2 * (k : ℝ) * Real.log (R : ℝ) := by
    push_cast
    rw [Real.log_mul (mul_ne_zero hB0 hW0) (pow_ne_zero _ hR0),
      Real.log_mul hB0 hW0, Real.log_pow]
    push_cast
    ring
  rw [hlogeq]
  have htermB := hlogB.trans (mul_le_mul_of_nonneg_left (hsqrt.trans hLs) ha)
  have htermW := hlogW.trans (mul_le_mul_of_nonneg_left hk2 hH)
  have htermR : 2 * (k : ℝ) * Real.log (R : ℝ) ≤ 2 * L ^ 2 := by
    calc
      _ ≤ 2 * (k : ℝ) * L := mul_le_mul_of_nonneg_left hlogR (by positivity)
      _ ≤ 2 * L * L := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkL (by norm_num)) hL0
      _ = _ := by ring
  change _ ≤ (a + H + 2) * L ^ 2
  nlinarith

theorem quadraticModulusLogScale_le {x k B W R : ℕ} {a H : ℝ}
    (ha : 0 ≤ a) (hH : 0 ≤ H) (hL : 1 ≤ Real.log (x : ℝ))
    (hB : 0 < B) (hW : 0 < W) (hR : 0 < R) (hRx : R ≤ x)
    (hBsize : (B : ℝ) ≤ Real.exp (a * Real.sqrt (Real.log (x : ℝ))))
    (hWsize : (W : ℝ) ≤ Real.exp (H * (k : ℝ) ^ 2))
    (hk : (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ)) :
    modulusLogScale (B * W * R ^ (2 * k)) ≤ (a + H + 9) * dimensionLogLossScale x := by
  have h := modulusLogScale_le_dimensionScale (by positivity : 0 ≤ a + H + 2) hL
    (log_quadraticModulus_le_square ha hH hL hB hW hR hRx hBsize hWsize hk)
  convert h using 1
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.quadraticModulusLogScale_le
