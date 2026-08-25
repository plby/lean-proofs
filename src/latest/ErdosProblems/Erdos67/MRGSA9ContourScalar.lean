import ErdosProblems.Erdos67.MRGSA9RpowIntegral

/-!
# Scalar absorption after the GS A.9 contour estimate

The analytic part of the A.9 argument leaves a factor
`X / L * (sqrt L * exp (-M / 2) + 1)` multiplying an integral of size at
most `2 * sqrt L`, together with an `X / sqrt L` error.  This file records
the elementary normalized consequence separately from the contour proof.
-/

namespace Erdos67

noncomputable section

/-- A coarse but convenient comparison for the two logarithmic square-root
scales that occur in the explicit zeta and contour bounds. -/
theorem sqrt_one_add_div_sqrt_le_two {L : ℝ} (hL : 1 ≤ L) :
    Real.sqrt (1 + L) / Real.sqrt L ≤ 2 := by
  have hL0 : 0 ≤ L := le_trans (by norm_num) hL
  have hOneL0 : 0 ≤ 1 + L := by positivity
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL0
  have hsOneL : Real.sqrt (1 + L) ^ 2 = 1 + L :=
    Real.sq_sqrt hOneL0
  have hroot : Real.sqrt (1 + L) ≤ 2 * Real.sqrt L := by
    have hsqrtL0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hsqrtOneL0 : 0 ≤ Real.sqrt (1 + L) := Real.sqrt_nonneg _
    nlinarith
  exact (div_le_iff₀ (Real.sqrt_pos.2 (zero_lt_one.trans_le hL))).2
    (by simpa [mul_comm] using hroot)

/-- General normalized form of the last contour calculation, before the
maximum-modulus envelope `B` is specialized. -/
theorem normalized_gsA9_contour_bound_general
    {X L U I B : ℝ} (hX : 0 < X) (hL : 1 ≤ L)
    (hB : 0 ≤ B) (hI : I ≤ 2 * Real.sqrt L)
    (hU : U ≤ X / L * B * I + X / Real.sqrt L) :
    U / X ≤ 2 * B / Real.sqrt L + 1 / Real.sqrt L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsqrtSq : Real.sqrt L * Real.sqrt L = L :=
    Real.mul_self_sqrt hLpos.le
  have hcoef : 0 ≤ X / L * B := by positivity
  have hmain := add_le_add_right (mul_le_mul_of_nonneg_left hI hcoef)
    (X / Real.sqrt L)
  have hU' : U ≤
      X / L * B * (2 * Real.sqrt L) + X / Real.sqrt L :=
    hU.trans (by
      simpa only [add_comm, add_left_comm, add_assoc] using hmain)
  have hid :
      X / L * B * (2 * Real.sqrt L) + X / Real.sqrt L =
        X * (2 * B / Real.sqrt L + 1 / Real.sqrt L) := by
    field_simp [hLpos.ne', hsqrtPos.ne']
    rw [show Real.sqrt L ^ 2 = L by
      simpa only [pow_two] using hsqrtSq]
    ring
  rw [hid] at hU'
  exact (div_le_iff₀ hX).2 (by simpa [mul_comm] using hU')

/-- The final scalar calculation in the A.9 argument.  Here `L` is the
quantity `log X` and `I` is the remaining `sigma ^ (-3/2)` integral. -/
theorem normalized_gsA9_contour_bound
    {X L M U I : ℝ} (hX : 0 < X) (hL : 1 ≤ L)
    (hI : I ≤ 2 * Real.sqrt L)
    (hU : U ≤
      X / L * (Real.sqrt L * Real.exp (-M / 2) + 1) * I +
        X / Real.sqrt L) :
    U / X ≤ 2 * Real.exp (-M / 2) + 3 / Real.sqrt L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hsqrtPos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hsqrtSq : Real.sqrt L * Real.sqrt L = L :=
    Real.mul_self_sqrt hLpos.le
  have hcoef :
      0 ≤ X / L * (Real.sqrt L * Real.exp (-M / 2) + 1) := by
    positivity
  have hmain := add_le_add_right (mul_le_mul_of_nonneg_left hI hcoef)
    (X / Real.sqrt L)
  have hU' : U ≤
      X / L * (Real.sqrt L * Real.exp (-M / 2) + 1) *
          (2 * Real.sqrt L) + X / Real.sqrt L :=
    hU.trans (by
      simpa only [add_comm, add_left_comm, add_assoc] using hmain)
  have hid :
      X / L * (Real.sqrt L * Real.exp (-M / 2) + 1) *
            (2 * Real.sqrt L) + X / Real.sqrt L =
        X * (2 * Real.exp (-M / 2) + 3 / Real.sqrt L) := by
    field_simp [hLpos.ne', hsqrtPos.ne']
    rw [show Real.sqrt L ^ 2 = L by
      simpa only [pow_two] using hsqrtSq]
    ring
  rw [hid] at hU'
  exact (div_le_iff₀ hX).2 (by simpa [mul_comm] using hU')

/-- Version with the actual interval integral left by A.10.  This directly
uses the lower endpoint `1 / L` occurring when `L = log X`. -/
theorem normalized_gsA9_contour_integral_bound
    {X L M U b : ℝ} (hX : 0 < X) (hL : 1 ≤ L)
    (hb : L⁻¹ ≤ b)
    (hU : U ≤
      X / L * (Real.sqrt L * Real.exp (-M / 2) + 1) *
          (∫ σ in L⁻¹..b, σ ^ (-3 / 2 : ℝ)) +
        X / Real.sqrt L) :
    U / X ≤ 2 * Real.exp (-M / 2) + 3 / Real.sqrt L := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hInv : 0 < L⁻¹ := inv_pos.mpr hLpos
  have hpow : L⁻¹ ^ (-1 / 2 : ℝ) = Real.sqrt L := by
    rw [Real.inv_rpow hLpos.le, Real.sqrt_eq_rpow]
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring]
    rw [Real.rpow_neg hLpos.le]
    simp
  have hI := integral_inv_rpow_three_halves_le hInv hb
  rw [hpow] at hI
  exact normalized_gsA9_contour_bound hX hL hI hU

end

end Erdos67
