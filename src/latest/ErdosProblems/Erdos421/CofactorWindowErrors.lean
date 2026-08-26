import ErdosProblems.Erdos421.AdditivePrimeCofactors

/-! # Mean-square control of the actual cofactor window by its two sieve errors -/

namespace Erdos421

open MeasureTheory

theorem additivePrimeCofactorWindow_mean_square_errors (P : Finset ℕ) {Q D z : ℕ}
    (hP : ∀ p ∈ P, 0 < p ∧ p ≤ Q) (hD : 0 < D) (hz : 2 ≤ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z)
    {Y u v : ℝ} (hY : 0 < Y) (hu : 0 ≤ u) (huv : u ≤ v) {B : ℕ} (hB : v + Y ≤ B) :
    (∫ x in u..v, |additivePrimeCofactorWindow P B z Y x -
      (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z| ^ 2) ≤
        3 * (v - u) * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z) ^ 2 +
        3 * (∫ x in u..v, ‖sieveWindowError (Q * D ^ 2)
          (primeDivisorConvolution P (canonicalUpperSieve D z)) Y x‖ ^ 2) +
        3 * (∫ x in u..v, ‖sieveWindowError (Q * (z * D ^ 2))
          (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y x‖ ^ 2) := by
  let U := sieveWindowError (Q * D ^ 2) (primeDivisorConvolution P (canonicalUpperSieve D z)) Y
  let L := sieveWindowError (Q * (z * D ^ 2))
    (primeDivisorConvolution P (lowerSieveCoefficient D z)) Y
  let c := ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z
  have hU : Continuous U := sieveWindowError_continuous _ _ hY
  have hL : Continuous L := sieveWindowError_continuous _ _ hY
  have hR : Continuous (fun x ↦ |additivePrimeCofactorWindow P B z Y x -
      (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z| ^ 2) :=
    ((additivePrimeCofactorWindow_continuous P B z Y).sub continuous_const).abs.pow 2
  have hUI : IntervalIntegrable (fun x ↦ 3 * ‖U x‖ ^ 2) volume u v :=
    (continuous_const.mul (hU.norm.pow 2)).intervalIntegrable u v
  have hLI : IntervalIntegrable (fun x ↦ 3 * ‖L x‖ ^ 2) volume u v :=
    (continuous_const.mul (hL.norm.pow 2)).intervalIntegrable u v
  have hCI : IntervalIntegrable (fun _ : ℝ ↦ 3 * c ^ 2) volume u v := intervalIntegrable_const
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc u v) :
      |additivePrimeCofactorWindow P B z Y x -
        (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z| ^ 2 ≤
          3 * c ^ 2 + 3 * ‖U x‖ ^ 2 + 3 * ‖L x‖ ^ 2 := by
    have hb := additivePrimeCofactorWindow_relative_control P hP hD hz hε hε1 hlevel hY
      (hu.trans hx.1) (le_trans (add_le_add_left hx.2 Y) hB)
    change |additivePrimeCofactorWindow P B z Y x -
      (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct z| ≤ c + ‖U x‖ + ‖L x‖ at hb
    have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
    nlinarith [sq_nonneg (c - ‖U x‖), sq_nonneg (c - ‖L x‖), sq_nonneg (‖U x‖ - ‖L x‖)]
  have hi := intervalIntegral.integral_mono_on huv (hR.intervalIntegrable u v)
    ((hCI.add hUI).add hLI) hpoint
  rw [intervalIntegral.integral_add (hCI.add hUI) hLI,
    intervalIntegral.integral_add hCI hUI,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul] at hi
  dsimp only [U, L, c] at hi
  nlinarith

end Erdos421
