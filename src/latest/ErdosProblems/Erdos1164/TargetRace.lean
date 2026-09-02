import ErdosProblems.Erdos1164.GreenHitBounds
import ErdosProblems.Erdos1164.SeparatedTargets
import ErdosProblems.Erdos1165.PointBeforeReturn

/-! # A uniform chance of reaching zero before a different selected target -/

open MeasureTheory

namespace Erdos1164

open Erdos1165 Erdos1165.Annulus Erdos1165.AnnulusHarnack
open Erdos1165.PotentialConvergence Erdos1165.PotentialEuclideanGeometry
open Erdos1165.GreenProbability Erdos1165.RadialHarnackSpecialization

noncomputable def spatialLogScale (m : ℕ) : ℝ := potentialSlope * Real.log (m : ℝ)

/-- An explicit large-scale condition, eventually true as `m` tends to infinity. -/
def LargeTargetScale (m : ℕ) : Prop :=
  4 ≤ m ∧ 1000 * potentialError ≤ spatialLogScale m

private theorem outer_log_scale (m : ℕ) :
    potentialSlope * Real.log ((m ^ 8 : ℕ) : ℝ) = 8 * spatialLogScale m := by
  rw [Nat.cast_pow, Real.log_pow]
  unfold spatialLogScale
  norm_num only [Nat.cast_ofNat]
  ring

private theorem outer_radius_large {m : ℕ} (hm : 4 ≤ m) : 8 ≤ m ^ 8 :=
  (by norm_num : 8 ≤ 4 ^ 8).trans (Nat.pow_le_pow_left hm 8)

private theorem origin_mem_outer_disc (m : ℕ) : (0 : Point) ∈ closedDisc (m ^ 8) := by
  simp [radiusSqInt]

private theorem origin_inner_quarter (m : ℕ) :
    euclideanRadius (0 : Point) ≤ ((m ^ 8 : ℕ) : ℝ) / 4 := by
  simp only [euclideanRadius, euclideanRadiusSq, Prod.fst_zero, Prod.snd_zero,
    Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
    Real.sqrt_zero]
  positivity

private theorem target_mem_outer_disc {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    separatedTarget m i ∈ closedDisc (m ^ 8) := by
  apply mem_closedDisc_of_euclideanRadius_le
  have h := separatedTarget_inner_quarter hm i
  have hp : (0 : ℝ) ≤ ((m ^ 8 : ℕ) : ℝ) := by positivity
  linarith

private theorem scale_denominator_pos {m : ℕ} (hm : LargeTargetScale m) :
    0 < 8 * spatialLogScale m - potentialError := by
  have h := hm.2
  have hp := potentialError_pos
  linarith

theorem target_hit_origin_lower {m : ℕ} (hm : LargeTargetScale m) (i : Fin m) :
    (23 / 32 : ℝ) ≤
      fairSteps.real (hitBeforeExitEvent (closedDisc (m ^ 8)) (separatedTarget m i) 0) := by
  have hpot := separatedTarget_potential hm.1 i
  change 2 * spatialLogScale m - potentialError ≤ _ ∧
    _ ≤ 2 * spatialLogScale m + potentialError at hpot
  have he := potentialError_pos
  have hscale := hm.2
  have hnum : 0 ≤ potentialSlope * Real.log ((m ^ 8 : ℕ) : ℝ) - potentialError -
      planarPotentialKernel (separatedTarget m i - 0) := by
    rw [outer_log_scale, sub_zero]
    linarith
  have h := killedHit_lower (outer_radius_large hm.1) (target_mem_outer_disc hm.1 i)
    (origin_mem_outer_disc m) (origin_inner_quarter m) hnum
  rw [outer_log_scale, sub_zero] at h
  apply le_trans _ h
  apply (le_div_iff₀ (by linarith : 0 < 8 * spatialLogScale m + potentialError)).mpr
  linarith

theorem target_hit_origin_upper {m : ℕ} (hm : LargeTargetScale m) (i : Fin m) :
    fairSteps.real (hitBeforeExitEvent (closedDisc (m ^ 8)) (separatedTarget m i) 0) ≤
      (25 / 32 : ℝ) := by
  have hpot := separatedTarget_potential hm.1 i
  change 2 * spatialLogScale m - potentialError ≤ _ ∧
    _ ≤ 2 * spatialLogScale m + potentialError at hpot
  have he := potentialError_pos
  have hscale := hm.2
  have hden : 0 < potentialSlope * Real.log ((m ^ 8 : ℕ) : ℝ) - potentialError := by
    rw [outer_log_scale]
    exact scale_denominator_pos hm
  have h := killedHit_upper (outer_radius_large hm.1) (target_mem_outer_disc hm.1 i)
    (origin_mem_outer_disc m) (origin_inner_quarter m) hden
  rw [outer_log_scale, sub_zero] at h
  apply h.trans
  apply (div_le_iff₀ (scale_denominator_pos hm)).mpr
  linarith

theorem target_hit_target_upper {m : ℕ} (hm : LargeTargetScale m)
    {i j : Fin m} (hij : i ≠ j) :
    fairSteps.real (hitBeforeExitEvent (closedDisc (m ^ 8))
      (separatedTarget m i) (separatedTarget m j)) ≤ (29 / 32 : ℝ) := by
  have hpot := separatedTarget_difference_potential hm.1 hij
  change spatialLogScale m - potentialError ≤ _ at hpot
  have he := potentialError_pos
  have hscale := hm.2
  have hden : 0 < potentialSlope * Real.log ((m ^ 8 : ℕ) : ℝ) - potentialError := by
    rw [outer_log_scale]
    exact scale_denominator_pos hm
  have h := killedHit_upper (outer_radius_large hm.1) (target_mem_outer_disc hm.1 i)
    (target_mem_outer_disc hm.1 j) (separatedTarget_inner_quarter hm.1 j) hden
  rw [outer_log_scale] at h
  apply h.trans
  apply (div_le_iff₀ (scale_denominator_pos hm)).mpr
  linarith

/-- The spatial race probability is bounded below uniformly over distinct
selected targets. No two-point hitting formula is assumed. -/
theorem target_race_origin_lower {m : ℕ} (hm : LargeTargetScale m)
    {i j : Fin m} (hij : i ≠ j) :
    (1 / 128 : ℝ) ≤ fairSteps.real
      (hitBeforePoint (separatedTarget m i) 0 (separatedTarget m j)) := by
  have h := raceProbability_lower (closedDisc (m ^ 8)) (separatedTarget m i) 0
    (separatedTarget m j)
  have hlow := target_hit_origin_lower hm i
  have hprod := mul_le_mul (target_hit_target_upper hm hij) (target_hit_origin_upper hm j)
    (measureReal_nonneg : 0 ≤ fairSteps.real
      (hitBeforeExitEvent (closedDisc (m ^ 8)) (separatedTarget m j) 0))
    (by norm_num : (0 : ℝ) ≤ 29 / 32)
  linarith

/-- The large-scale condition holds eventually, with no additional hypothesis
on the walk or on a subsequence. -/
theorem eventually_largeTargetScale : ∀ᶠ m : ℕ in Filter.atTop, LargeTargetScale m := by
  have ht : Filter.Tendsto spatialLogScale Filter.atTop Filter.atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop potentialSlope_pos
  filter_upwards [Filter.eventually_ge_atTop 4,
    ht.eventually (Filter.eventually_ge_atTop (1000 * potentialError))] with m hm hs
  exact ⟨hm, hs⟩

/-- Hitting a selected target within one origin excursion has probability of
order at most the reciprocal logarithmic scale. -/
theorem target_excursion_probability_upper {m : ℕ} (hm : LargeTargetScale m) (i : Fin m) :
    PointBeforeReturn.pointBeforeReturnProbability (separatedTarget m i) ≤
      1 / (2 * spatialLogScale m) := by
  rw [PointBeforeReturn.pointBeforeReturnProbability_eq
    (separatedTarget_ne_zero (by have := hm.1; omega) i)]
  have hpot := (separatedTarget_potential hm.1 i).1
  change 2 * spatialLogScale m - potentialError ≤ _ at hpot
  have hs := hm.2
  have he := potentialError_pos
  have htpos : 0 < spatialLogScale m := by linarith
  have hdom : spatialLogScale m ≤ planarPotentialKernel (separatedTarget m i) := by linarith
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hdom (by norm_num))

end Erdos1164
