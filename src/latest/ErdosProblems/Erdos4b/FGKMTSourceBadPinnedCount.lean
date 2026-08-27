/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSurvivorConcentration

/-! # An absolute exceptional-vertex count for the actual source sieve -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem eventually_actualSource_badPinnedVertexCount_tail_le {a c e : ℝ}
    (ha : 0 < a) (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      (∑ b : ResidueAssignment (sourceSmallPrimes a x),
        if (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2) ≤
            ((D.badPinnedVertices (sourceSmallPrimes a x) b).card : ℝ)
          then residueAssignmentMass (sourceSmallPrimes a x) b else 0) ≤
        1 / Real.log (Real.log (x : ℝ)) := by
  obtain ⟨_A, B, _hA, hB, hmean⟩ := exists_sourceSurvivorMean_bounds
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ)
    (by norm_num : (0 : ℝ) < 6)).comp_tendsto hlog).def
      (by positivity : (0 : ℝ) < 1 / (2 * B * a * c))
  filter_upwards [hmean a c ha hc, eventually_source_badPinnedVertexCount_tail_le hc he,
    eventually_sourceSmallPrimes_le ha, hsmall,
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hmean htail hupper hs hL hl hx
  change 0 < Real.log (Real.log (x : ℝ)) at hl
  intro D
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let v := (x : ℝ) / (L * l ^ 2)
  change 0 < L at hL
  change 0 < l at hl
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hv : 0 < v := by dsimp only [v, L, l]; positivity
  change ‖l ^ (4 : ℝ)‖ ≤ (1 / (2 * B * a * c)) * ‖L ^ (6 : ℝ)‖ at hs
  have hs' : l ^ 4 ≤ L ^ 6 / (2 * B * a * c) := by
    simpa only [Real.rpow_ofNat, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hl.le 4),
      abs_of_nonneg (pow_nonneg hL.le 6), one_div, div_eq_mul_inv, mul_comm, one_mul] using hs
  have hbudget : 2 * B * a * c * l ^ 4 ≤ L ^ 6 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * B * a * c)).mp hs'
    nlinarith
  have ht := htail D (sourceSmallPrimes a x) (sourceSmallPrimes_prime a x)
    (sourceSmallPrimes_rough a x) hupper v hv
  have hM : sourceSurvivorMean a c x ≤ B * a * c * x * l / L := hmean.2
  calc
    _ ≤ 2 * residueSieveDensity (sourceSmallPrimes a x) * (sourceSievingPrimes c x).card /
        (L ^ 6 * v) := ht
    _ = (2 * sourceSurvivorMean a c x) / (L ^ 6 * v) := by
      unfold sourceSurvivorMean
      ring
    _ ≤ (2 * (B * a * c * x * l / L)) / (L ^ 6 * v) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by norm_num)) (by positivity)
    _ = (2 * B * a * c * l ^ 4 / L ^ 6) / l := by
      dsimp only [v]
      field_simp [hL.ne', hl.ne', hxR.ne']
    _ ≤ 1 / l := div_le_div_of_nonneg_right
      ((div_le_one (pow_pos hL 6)).mpr hbudget) hl.le

end

end Erdos4b.FGKMT
