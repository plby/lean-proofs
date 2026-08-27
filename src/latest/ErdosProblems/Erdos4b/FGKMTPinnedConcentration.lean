/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedTupleOverlap

/-! # Conditional concentration for the genuine pinned source weights -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

def SourceProbabilityData.pinnedSurvivalMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ)
    (a : ResidueAssignment S) : ℝ :=
  ∑ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
    D.pinnedTupleWeight q j * residueAvoidanceIndicator S (D.pinnedResidueTuple q j) a

def SourceProbabilityData.pinnedNormalizedSurvival {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ)
    (a : ResidueAssignment S) : ℝ :=
  ∑ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
    D.pinnedNormalizedWeight q j * residueAvoidanceIndicator S (D.pinnedResidueTuple q j) a

theorem SourceProbabilityData.pinnedNormalizedSurvival_eq {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (q : ℕ) (a : ResidueAssignment S) :
    D.pinnedNormalizedSurvival S q a = D.pinnedSurvivalMass S q a / D.pinnedTotalMass q := by
  simp only [pinnedNormalizedSurvival, pinnedSurvivalMass, pinnedNormalizedWeight,
    div_mul_eq_mul_div, Finset.sum_div]

theorem eventually_source_pinned_concentration {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ q ∈ sourceSievingPrimes c x, ∀ r : ℝ, 0 < r →
      (∑ a : ResidueAssignment S,
        if r * residueSieveDensity S ^ (D.dimension - 1) ≤
            |D.pinnedNormalizedSurvival S q a - residueSieveDensity S ^ (D.dimension - 1)|
          then conditionalResidueMass S q a else 0) ≤
        (3 * (144 / Real.log (x : ℝ) ^ 16) *
            (residueSieveDensity S ^ (D.dimension - 1)) ^ 2 +
          4 * (D.dimension : ℝ) * Real.log (x : ℝ) ^ 2 * (x : ℝ) ^ (-2 / 3 + e : ℝ)) /
          (r * residueSieveDensity S ^ (D.dimension - 1)) ^ 2 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_uniform_conditional_residue_concentration
      (by norm_num : (0 : ℝ) ≤ 2), eventually_pinnedResidueTuple_ranges hc,
    eventually_pinnedTuple_overlap_mass_le hc, eventually_pinnedTotalMass_lower hc,
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with x hcor hranges hoverlap hB hL
  intro D S hS hrough q hq r hr
  have hBpos : 0 < D.pinnedTotalMass q :=
    (by positivity : (0 : ℝ) < 1 / (4 * Real.log (x : ℝ) ^ 2)).trans_le (hB D q hq)
  have hpin := fun j (_hj : j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x) =>
    D.pin_mem_pinnedResidueTuple q j
  have hcard : ∀ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
      (D.pinnedResidueTuple q j).card = D.dimension := by
    intro j hj
    exact D.pinnedResidueTuple_card q
      (mem_commonPinnedPrimeSet.mp (Finset.mem_product.mp hj).2).2.2.pos
  have hheight : ∀ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x,
      ∀ n ∈ D.pinnedResidueTuple q j, |(n : ℝ)| ≤ (x : ℝ) ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using (hranges D).2.1 q hq
  have h := hcor (Fin D.dimension × ℕ) S hS hrough q
    (Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x) (D.pinnedNormalizedWeight q)
    (D.pinnedResidueTuple q) D.dimension
    (fun j hj => D.pinnedNormalizedWeight_nonneg q hBpos hj)
    (D.pinnedNormalizedWeight_sum_one q hBpos) hpin hcard (hranges D).1 hheight r hr
  norm_num only [show (48 : ℝ) * (2 + 1) = 144 from by norm_num] at h
  exact h.trans (div_le_div_of_nonneg_right
    (add_le_add le_rfl (hoverlap D q hq)) (sq_nonneg _))

end

end Erdos4b.FGKMT
