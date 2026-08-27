/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSurvivorMean

/-! # Concentration of the actual surviving natural source primes -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

open scoped Classical in
def sourceSurvivorVertices (a c : ℝ) (x : ℕ) (b : ResidueAssignment (sourceSmallPrimes a x)) :
    Finset ℕ :=
  (sourceSievingPrimes c x).filter fun q =>
    residueAssignmentAvoids (sourceSmallPrimes a x) {(q : ℤ)} b

theorem sourceSurvivorVertices_image_eq (a c : ℝ) (x : ℕ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) :
    residueSurvivorSet (sourceSmallPrimes a x)
        ((sourceSievingPrimes c x).image fun q : ℕ => (q : ℤ)) b =
      (sourceSurvivorVertices a c x b).image (fun q : ℕ => (q : ℤ)) := by
  classical
  simp only [residueSurvivorSet, sourceSurvivorVertices, Finset.filter_image]

theorem sourceSurvivorVertices_integer_card (a c : ℝ) (x : ℕ)
    (b : ResidueAssignment (sourceSmallPrimes a x)) :
    (residueSurvivorSet (sourceSmallPrimes a x)
      ((sourceSievingPrimes c x).image fun q : ℕ => (q : ℤ)) b).card =
        (sourceSurvivorVertices a c x b).card := by
  rw [sourceSurvivorVertices_image_eq, Finset.card_image_of_injective _ Nat.cast_injective]

theorem sourceSurvivorVertices_expectation (a c : ℝ) (x : ℕ) :
    residueExpectation (sourceSmallPrimes a x)
      (fun b => ((sourceSurvivorVertices a c x b).card : ℝ)) = sourceSurvivorMean a c x := by
  have h := residueExpectation_survivor_count
    (fun p hp => (sourceSmallPrimes_prime a x p hp).pos)
    ((sourceSievingPrimes c x).image fun q : ℕ => (q : ℤ))
  simp_rw [sourceSurvivorVertices_integer_card] at h
  rw [Finset.card_image_of_injective _ Nat.cast_injective] at h
  exact h.trans (by unfold sourceSurvivorMean; ring)

theorem survivor_relative_tail_budget {L l M : ℝ} (hL : 145 ≤ L) (hl : 0 < l)
    (hl3 : l ^ 3 ≤ L) (hM : L ^ 8 ≤ M) :
    (144 / L ^ 16 + 1 / M) / (1 / l) ^ 2 ≤ 1 / l := by
  have hLpos : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hMpos : 0 < M := (pow_pos hLpos 8).trans_le hM
  have hpow16 : L ^ 2 ≤ L ^ 16 := pow_le_pow_right₀ hL1 (by norm_num)
  have hpow8 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
  have hcoeff : 144 / L ^ 16 + 1 / M ≤ 145 / L ^ 2 := by
    have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 144)
      (sq_pos_of_pos hLpos) hpow16
    have h2 := one_div_le_one_div_of_le (sq_pos_of_pos hLpos) (hpow8.trans hM)
    exact (add_le_add h1 h2).trans_eq (by ring)
  have hbudget : (144 / L ^ 16 + 1 / M) * l ^ 3 ≤ 1 := by
    calc
      _ ≤ (145 / L ^ 2) * L := mul_le_mul hcoeff hl3 (by positivity) (by positivity)
      _ = 145 / L := by field_simp [hLpos.ne']
      _ ≤ 1 := (div_le_one hLpos).mpr hL
  calc
    _ = ((144 / L ^ 16 + 1 / M) * l ^ 3) / l := by field_simp [hl.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hbudget hl.le

theorem eventually_sourceSurvivorVertices_tail_le {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      (∑ b : ResidueAssignment (sourceSmallPrimes a x),
        if sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ)) ≤
            |((sourceSurvivorVertices a c x b).card : ℝ) - sourceSurvivorMean a c x|
          then residueAssignmentMass (sourceSmallPrimes a x) b else 0) ≤
        1 / Real.log (Real.log (x : ℝ)) := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (3 : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto hlog).eventuallyLE
  filter_upwards [eventually_uniform_survivor_concentration (by norm_num : (0 : ℝ) ≤ 2),
    eventually_sourceSurvivorMean_ge_log_pow ha hc 8,
    eventually_sourceTuple_ranges hc, eventually_sourceIntervalLength_bounds hc,
    hlog.eventually (eventually_ge_atTop (145 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)), hsmall] with
      x hcon hM hy2 hy hL hl hsmall
  change 0 < Real.log (Real.log (x : ℝ)) at hl
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hMpos : 0 < sourceSurvivorMean a c x := (pow_pos hLpos 8).trans_le hM
  have hσpos := residueSieveDensity_pos
    (fun p hp => (sourceSmallPrimes_prime a x p hp).one_lt)
  have hQcard : 0 < ((sourceSievingPrimes c x).card : ℝ) := by
    unfold sourceSurvivorMean at hMpos
    exact (mul_pos_iff_of_pos_left hσpos).mp hMpos
  have hQne : (sourceSievingPrimes c x).Nonempty := Finset.card_pos.mp (by exact_mod_cast hQcard)
  have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
  have hheight : ∀ n ∈ (sourceSievingPrimes c x).image (fun q : ℕ => (q : ℤ)),
      |(n : ℝ)| ≤ (x : ℝ) ^ (2 : ℝ) := by
    intro n hn
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hn
    have hqle := (mem_sourceSievingPrimes hy0).mp hq |>.2.2
    simp only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q),
      Real.rpow_two]
    linarith [hy2.2]
  have htail := hcon (sourceSmallPrimes a x) (sourceSmallPrimes_prime a x)
    (sourceSmallPrimes_rough a x) ((sourceSievingPrimes c x).image fun q : ℕ => (q : ℤ))
    (hQne.image _) hheight (1 / Real.log (Real.log (x : ℝ))) (by positivity)
  simp_rw [sourceSurvivorVertices_integer_card] at htail
  rw [Finset.card_image_of_injective _ Nat.cast_injective] at htail
  have hcenter : ((sourceSievingPrimes c x).card : ℝ) *
      residueSieveDensity (sourceSmallPrimes a x) = sourceSurvivorMean a c x := by
    unfold sourceSurvivorMean
    ring
  rw [hcenter] at htail
  have hsmall' : Real.log (Real.log (x : ℝ)) ^ 3 ≤ Real.log (x : ℝ) := by
    simpa only [Function.comp_apply, Real.rpow_ofNat, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hl.le 3), abs_of_nonneg hLpos.le] using hsmall
  have hbudget := survivor_relative_tail_budget hL hl hsmall' hM
  have htail' :
      (∑ b : ResidueAssignment (sourceSmallPrimes a x),
        if sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ)) ≤
            |((sourceSurvivorVertices a c x b).card : ℝ) - sourceSurvivorMean a c x|
          then residueAssignmentMass (sourceSmallPrimes a x) b else 0) ≤
        (144 / Real.log (x : ℝ) ^ 16 + 1 / sourceSurvivorMean a c x) /
          (1 / Real.log (Real.log (x : ℝ))) ^ 2 := by
    convert htail using 1 <;> norm_num [one_div, div_eq_mul_inv, mul_comm]
  exact htail'.trans hbudget

end

end Erdos4b.FGKMT
