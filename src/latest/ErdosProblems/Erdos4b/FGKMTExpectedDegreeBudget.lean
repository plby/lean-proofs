/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTExpectedDegreeScale

/-! # The required absolute degree tolerance from an explicit bound on the scale -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem degree_relative_error_budget {r v : ℝ} (hr : 0 ≤ r) (hv : 0 ≤ v)
    (hrv : r ≤ v) (hv1 : v ≤ 1) :
    (r * (1 + 4 * v) + 4 * v) + 2 * r * (1 + (r * (1 + 4 * v) + 4 * v)) ≤ 29 * v := by
  let δ := r * (1 + 4 * v) + 4 * v
  have hδ0 : 0 ≤ δ := by dsimp only [δ]; positivity
  have hv2 : v ^ 2 ≤ v := by nlinarith [mul_nonneg hv (sub_nonneg.mpr hv1)]
  have hδ : δ ≤ 9 * v := by
    have h := mul_le_mul_of_nonneg_right hrv (by positivity : 0 ≤ 1 + 4 * v)
    dsimp only [δ]
    nlinarith
  have hprod : 2 * r * (1 + δ) ≤ 2 * v * (1 + 9 * v) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hrv (by norm_num))
      (add_le_add le_rfl hδ) (by positivity) (by positivity)
  change δ + 2 * r * (1 + δ) ≤ 29 * v
  nlinarith

theorem eventually_sourceDegreeRelativeError_le :
    ∀ᶠ x : ℕ in atTop,
      sourceDegreeRelativeError x ≤ 29 / Real.log (Real.log (x : ℝ)) ^ 10 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((10 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 3)).comp_tendsto hlog).eventuallyLE
  filter_upwards [hsmall, hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ))] with x hsmall hL hl
  change 1 ≤ Real.log (Real.log (x : ℝ)) at hl
  have hlpos : 0 < Real.log (Real.log (x : ℝ)) := by linarith
  have hsmall' : Real.log (Real.log (x : ℝ)) ^ 10 ≤ Real.log (x : ℝ) ^ 3 := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.rpow_ofNat, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlpos.le 10), abs_of_nonneg (pow_nonneg hL.le 3)] using hsmall
  have hrv : 1 / Real.log (x : ℝ) ^ 3 ≤ 1 / Real.log (Real.log (x : ℝ)) ^ 10 :=
    one_div_le_one_div_of_le (pow_pos hlpos 10) hsmall'
  have hv1 : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 : ℝ) :=
    (div_le_one (pow_pos hlpos 10)).mpr (one_le_pow₀ hl)
  have h := degree_relative_error_budget (by positivity) (by positivity) hrv hv1
  simpa only [sourceDegreeRelativeError, sourcePinnedRelativeError, mul_one_div] using h

theorem absolute_degree_loglog_budget {l K : ℝ} (hl : 2 ≤ l) (hK : 58 * K ≤ l ^ 8) :
    1 / l ^ 3 + (29 / l ^ 10) * K ≤ 1 / l ^ 2 := by
  have hlpos : 0 < l := by linarith
  have hfirst : 1 / l ^ 3 ≤ 1 / (2 * l ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    have h := mul_le_mul_of_nonneg_right hl (sq_nonneg l)
    nlinarith
  have hsecond : (29 / l ^ 10) * K ≤ 1 / (2 * l ^ 2) := by
    have heq : (29 / l ^ 10) * K = (58 * K / l ^ 8) * (1 / (2 * l ^ 2)) := by
      field_simp [hlpos.ne']
      ring
    rw [heq]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one (pow_pos hlpos 8)).mpr hK)
  calc
    _ ≤ 1 / (2 * l ^ 2) + 1 / (2 * l ^ 2) := add_le_add hfirst hsecond
    _ = _ := by ring

theorem eventually_source_expectedDegree_good_vertices {c e K : ℝ} (hc : 0 < c) (hK : 0 < K) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → D.expectedDegreeScale S ≤ K →
      ∀ a : ResidueAssignment S, ∀ q ∈ sourceSievingPrimes c x,
      residueAssignmentAvoids S {(q : ℤ)} a → q ∉ D.badPinnedVertices S a →
      q ∉ D.lostDegreeVertices S (1 / Real.log (Real.log (x : ℝ)) ^ 3) a →
      |D.primeTupleExpectedDegree S (sourceSievingPrimes c x) a q - D.expectedDegreeScale S| ≤
        1 / Real.log (Real.log (x : ℝ)) ^ 2 := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_source_expectedDegree_error_scale hc,
    eventually_sourceDegreeRelativeError_le, eventually_sourceIntervalLength_bounds hc,
    hloglog.eventually (eventually_ge_atTop (max 2 (58 * K + 1))),
    eventually_ge_atTop (1 : ℕ)] with x hdegree herror hy hl hx
  change max 2 (58 * K + 1) ≤ Real.log (Real.log (x : ℝ)) at hl
  intro D S hS hcap a q hq hsurv hpin hlost
  have hl2 : 2 ≤ Real.log (Real.log (x : ℝ)) := (le_max_left _ _).trans hl
  have hlK : 58 * K + 1 ≤ Real.log (Real.log (x : ℝ)) := (le_max_right _ _).trans hl
  have hlpos : 0 < Real.log (Real.log (x : ℝ)) := by linarith
  have hxpos : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hCpos := D.expectedDegreeScale_pos hS hxpos (hxR.trans_le hy.1)
  have hbad : D.pinnedBadMass S q a ≤ 1 / Real.log (Real.log (x : ℝ)) ^ 3 := by
    apply le_of_not_gt
    intro h
    exact hlost (Finset.mem_filter.mpr ⟨hq, h⟩)
  have hKpow : 58 * K ≤ Real.log (Real.log (x : ℝ)) ^ 8 := by
    have h7 : (1 : ℝ) ≤ Real.log (Real.log (x : ℝ)) ^ 7 := one_le_pow₀ (by linarith)
    have hmul := mul_le_mul_of_nonneg_left h7 hlpos.le
    nlinarith
  calc
    _ ≤ D.pinnedBadMass S q a + sourceDegreeRelativeError x * D.expectedDegreeScale S :=
      hdegree D S hS a q hq hsurv hpin
    _ ≤ 1 / Real.log (Real.log (x : ℝ)) ^ 3 +
        (29 / Real.log (Real.log (x : ℝ)) ^ 10) * K :=
      add_le_add hbad (mul_le_mul herror hcap hCpos.le (by positivity))
    _ ≤ _ := absolute_degree_loglog_budget hl2 hKpow

end

end Erdos4b.FGKMT
