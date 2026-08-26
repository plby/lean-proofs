import ErdosProblems.Erdos421.RoughWindowControl

/-! # An unconditional mean-square estimate for smooth rough-number counts -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem additiveRoughWindow_mean_square_errors {D z : ℕ} (hD : 0 < D) (hz : 2 ≤ z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hlevel : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z)
    {Y u v : ℝ} (hY : 0 < Y) (hu : 0 ≤ u) (huv : u ≤ v) {B : ℕ} (hB : v + Y ≤ B) :
    (∫ x in u..v, |additiveRoughWindow B z Y x - roughEulerProduct z| ^ 2) ≤
      3 * (v - u) * (ε * roughEulerProduct z) ^ 2 +
      3 * (∫ x in u..v, ‖sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x‖ ^ 2) +
      3 * (∫ x in u..v, ‖sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x‖ ^ 2) := by
  let U := sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y
  let L := sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y
  let c := ε * roughEulerProduct z
  have hU : Continuous U := sieveWindowError_continuous _ _ hY
  have hL : Continuous L := sieveWindowError_continuous _ _ hY
  have hR : Continuous (fun x ↦ |additiveRoughWindow B z Y x - roughEulerProduct z| ^ 2) :=
    ((additiveRoughWindow_continuous B z Y).sub continuous_const).abs.pow 2
  have hUI : IntervalIntegrable (fun x ↦ 3 * ‖U x‖ ^ 2) volume u v :=
    (continuous_const.mul (hU.norm.pow 2)).intervalIntegrable u v
  have hLI : IntervalIntegrable (fun x ↦ 3 * ‖L x‖ ^ 2) volume u v :=
    (continuous_const.mul (hL.norm.pow 2)).intervalIntegrable u v
  have hCI : IntervalIntegrable (fun _ : ℝ ↦ 3 * c ^ 2) volume u v := intervalIntegrable_const
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc u v) :
      |additiveRoughWindow B z Y x - roughEulerProduct z| ^ 2 ≤
        3 * c ^ 2 + 3 * ‖U x‖ ^ 2 + 3 * ‖L x‖ ^ 2 := by
    have hb := additiveRoughWindow_relative_control hD hz hε hε1 hlevel hY
      (hu.trans hx.1) (le_trans (add_le_add_left hx.2 Y) hB)
    change |additiveRoughWindow B z Y x - roughEulerProduct z| ≤ c + ‖U x‖ + ‖L x‖ at hb
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

theorem additiveRoughWindow_mean_square (A : ℝ) {ε τ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∀ᶠ X : ℕ in atTop, ∀ D z : ℕ, 0 < D → 2 ≤ z →
      ((z * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log z →
      ∀ (Y u v : ℝ) (B : ℕ), (X : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
      0 ≤ u → u ≤ v → v - u ≤ X → v + Y ≤ B →
      (∫ x in u..v, |additiveRoughWindow B z Y x - roughEulerProduct z| ^ 2) ≤
        3 * X * (ε * roughEulerProduct z) ^ 2 + τ * X / (Real.log X) ^ A := by
  have hτ6 : 0 < τ / 6 := by positivity
  filter_upwards [eventually_ge_atTop 1, canonicalUpper_window_mean A hτ6,
    canonicalLower_window_mean A hτ6] with X hX hU hL
  intro D z hD hz hMX hlevel Y u v B hY hu huv hlen hB
  have hYpos : 0 < Y := (Real.rpow_pos_of_pos (by exact_mod_cast hX) _).trans_le hY
  have hDX : ((D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) := by
    apply le_trans _ hMX
    exact_mod_cast Nat.le_mul_of_pos_left (D ^ 2) (by omega : 0 < z)
  have hbU := hU D z hD hDX Y u v hY huv hlen
  have hbL := hL D z hD (by omega) hMX Y u v hY huv hlen
  have hb := additiveRoughWindow_mean_square_errors hD hz hε hε1 hlevel hYpos hu huv hB
  change (∫ x in u..v, ‖sieveWindowError (D ^ 2) (canonicalUpperSieve D z) Y x‖ ^ 2) ≤ _ at hbU
  change (∫ x in u..v,
    ‖sieveWindowError (z * D ^ 2) (lowerSieveCoefficient D z) Y x‖ ^ 2) ≤ _ at hbL
  have hlen' := mul_le_mul_of_nonneg_right hlen (sq_nonneg (ε * roughEulerProduct z))
  apply hb.trans
  calc
    _ ≤ 3 * X * (ε * roughEulerProduct z) ^ 2 +
        3 * (τ / 6 * X / (Real.log X) ^ A) + 3 * (τ / 6 * X / (Real.log X) ^ A) := by
      exact add_le_add (add_le_add (by nlinarith [hlen'])
        (mul_le_mul_of_nonneg_left hbU (by norm_num)))
        (mul_le_mul_of_nonneg_left hbL (by norm_num))
    _ = _ := by ring

end Erdos421
