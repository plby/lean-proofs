/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTRegularVertexSet

/-! # Quantitative size of the retained set and its deleted cleanup cost -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem eventually_sourceSurvivorMean_ge_mul_div_log {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (K : ℝ) : ∀ᶠ x : ℕ in atTop,
      K * (x : ℝ) / Real.log (x : ℝ) ≤ sourceSurvivorMean a c x := by
  obtain ⟨A, _B, hA, _hB, hbound⟩ := exists_sourceSurvivorMean_bounds
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hbound a c ha hc, hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (K / (A * a * c)))] with x hM hL hl
  have hfactor : K ≤ A * a * c * Real.log (Real.log (x : ℝ)) := by
    have h := (div_le_iff₀ (mul_pos (mul_pos hA ha) hc)).mp hl
    simpa only [Function.comp_apply, mul_comm] using h
  calc
    _ ≤ (A * a * c * Real.log (Real.log (x : ℝ))) * x / Real.log (x : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg x)) hL.le
    _ = A * a * c * x * Real.log (Real.log (x : ℝ)) / Real.log (x : ℝ) := by ring
    _ ≤ _ := hM.1

theorem eventually_source_cleanup_budget {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      8 * ((x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2)) ≤
        sourceSurvivorMean a c x := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_sourceSurvivorMean_ge_mul_div_log ha hc 8,
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (1 : ℝ))] with x hM hL hl
  have hden : Real.log (x : ℝ) ≤
      Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2 :=
    le_mul_of_one_le_right hL.le (one_le_pow₀ hl)
  calc
    _ ≤ 8 * ((x : ℝ) / Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Nat.cast_nonneg x) hL hden) (by norm_num)
    _ = 8 * (x : ℝ) / Real.log (x : ℝ) := by ring
    _ ≤ _ := hM

theorem SourceProbabilityData.sourceRegularVertices_card_bounds {a c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (b : ResidueAssignment (sourceSmallPrimes a x))
    (hl : 4 ≤ Real.log (Real.log (x : ℝ))) (hM : 0 ≤ sourceSurvivorMean a c x)
    (hcleanup : 8 * ((x : ℝ) /
      (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2)) ≤ sourceSurvivorMean a c x)
    (hsize : |((sourceSurvivorVertices a c x b).card : ℝ) - sourceSurvivorMean a c x| <
      sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ)))
    (hpin : ((D.badPinnedVertices (sourceSmallPrimes a x) b).card : ℝ) <
      (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2))
    (hlost : ((D.lostDegreeVertices (sourceSmallPrimes a x)
      (1 / Real.log (Real.log (x : ℝ)) ^ 3) b).card : ℝ) <
        (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2)) :
    sourceSurvivorMean a c x / 2 ≤ (D.sourceRegularVertices a b).card ∧
    ((D.sourceRegularVertices a b).card : ℝ) ≤ 2 * sourceSurvivorMean a c x ∧
    ((sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card : ℝ) <
      2 * ((x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2)) := by
  have hremoved : ((sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card : ℝ) ≤
      (D.badPinnedVertices (sourceSmallPrimes a x) b).card +
        (D.lostDegreeVertices (sourceSmallPrimes a x)
          (1 / Real.log (Real.log (x : ℝ)) ^ 3) b).card := by
    exact_mod_cast D.sourceRegularVertices_removed_card_le a b
  have hpartition : ((D.sourceRegularVertices a b).card : ℝ) +
      (sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card =
        (sourceSurvivorVertices a c x b).card := by
    exact_mod_cast D.sourceRegularVertices_card_partition a b
  have hquarter : sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ)) ≤
      sourceSurvivorMean a c x / 4 := div_le_div_of_nonneg_left hM (by norm_num) hl
  have hsize' := abs_lt.mp hsize
  have hremoved0 : (0 : ℝ) ≤
      (sourceSurvivorVertices a c x b \ D.sourceRegularVertices a b).card := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩ <;> linarith

theorem sourceSievingPrimes_card_le_interval {c : ℝ} {x : ℕ}
    (hy : 0 ≤ sourceIntervalLength c x) :
    ((sourceSievingPrimes c x).card : ℝ) ≤ sourceIntervalLength c x := by
  have hsub : sourceSievingPrimes c x ⊆ Finset.Icc 1 ⌊sourceIntervalLength c x⌋₊ := by
    intro q hq
    have h := mem_commonPinnedPrimeSet.mp hq
    exact Finset.mem_Icc.mpr ⟨h.2.2.one_le, h.2.1⟩
  have hcard : (sourceSievingPrimes c x).card ≤ ⌊sourceIntervalLength c x⌋₊ := by
    simpa using Finset.card_le_card hsub
  exact (by exact_mod_cast hcard : ((sourceSievingPrimes c x).card : ℝ) ≤
    (⌊sourceIntervalLength c x⌋₊ : ℕ)).trans (Nat.floor_le hy)

theorem eventually_sourceRegularVertices_card_le_sq {a c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ b : ResidueAssignment (sourceSmallPrimes a x),
        ((D.sourceRegularVertices a b).card : ℝ) ≤ (x : ℝ) ^ 2 := by
  filter_upwards [eventually_sourceTuple_ranges hc, eventually_sourceIntervalLength_bounds hc]
    with x hy2 hy
  intro D b
  have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
  have hcard : ((D.sourceRegularVertices a b).card : ℝ) ≤ (sourceSievingPrimes c x).card := by
    exact_mod_cast Finset.card_le_card (D.sourceRegularVertices_subset_source a b)
  exact (hcard.trans (sourceSievingPrimes_card_le_interval hy0)).trans (by linarith [hy2.2])

end

end Erdos4b.FGKMT
