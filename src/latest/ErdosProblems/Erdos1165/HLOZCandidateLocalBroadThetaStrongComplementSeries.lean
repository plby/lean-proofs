/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongComplementRoute

/-!
# Summable concrete candidate-local product complement
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongComplementSeries

open HLOZCandidateLocalBroadThetaRoute
open HLOZCandidateLocalBroadThetaStrongComplementRoute
open HLOZCandidateLocalBroadThetaStrongTransportPayment
open HLOZNoLazyFullBetaProductBranch HLOZUpperEstimates

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def candidateLocalComplementSmallLevelEvent (m : ℕ) : Set WalkPath :=
  if 2 ≤ m then ∅ else Set.univ

private theorem simpleRandomWalk_candidateLocalComplementSmallLevelEvent_series_ne_top :
    ∑' m, simpleRandomWalk (candidateLocalComplementSmallLevelEvent m) ≠ ∞ := by
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  simp [candidateLocalComplementSmallLevelEvent, hm]

private theorem measure_union_series_ne_top
    {first second : ℕ → Set WalkPath}
    (hfirst : ∑' m, simpleRandomWalk (first m) ≠ ∞)
    (hsecond : ∑' m, simpleRandomWalk (second m) ≠ ∞) :
    ∑' m, simpleRandomWalk (first m ∪ second m) ≠ ∞ := by
  have hmajor : ∑' m,
      (simpleRandomWalk (first m) + simpleRandomWalk (second m)) ≠ ∞ := by
    rw [ENNReal.tsum_add]
    exact ENNReal.add_ne_top.mpr ⟨hfirst, hsecond⟩
  exact ne_top_of_le_ne_top hmajor
    (ENNReal.tsum_le_tsum fun m ↦ measure_union_le _ _)

def candidateLocalComplementConcreteMajorant
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  candidateLocalComplementSmallLevelEvent m ∪
    (candidateLocalBroadStrongSourceOnTimePayment t m ∪
      candidateLocalBroadCheckerOriginPayment t m)

theorem onTimeProductBetaCandidateLocalComplementEvent_subset_concreteMajorant
    (t : DominoTiling) (m : ℕ) :
    onTimeProductBetaCandidateLocalComplementEvent t m (m / 2) ⊆
      candidateLocalComplementConcreteMajorant t m := by
  intro s hs
  by_cases hm : 2 ≤ m
  · exact Or.inr
      (onTimeProductBetaCandidateLocalComplementEvent_subset_strongOnTime_union_origin
        t hm hs)
  · apply Or.inl
    simp [candidateLocalComplementSmallLevelEvent, hm]

theorem simpleRandomWalk_candidateLocalComplementConcreteMajorant_series_ne_top
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk (candidateLocalComplementConcreteMajorant t m) ≠ ∞ :=
  measure_union_series_ne_top
    simpleRandomWalk_candidateLocalComplementSmallLevelEvent_series_ne_top
    (measure_union_series_ne_top
      (simpleRandomWalk_candidateLocalBroadStrongSourceOnTimePayment_series_ne_top
        t)
      (simpleRandomWalk_candidateLocalBroadCheckerOriginPayment_series_ne_top t))

/-- The exact product-complement series required by the concrete no-lazy
FullBeta assembly. -/
theorem simpleRandomWalk_onTimeProductBetaCandidateLocalComplementEvent_half_series_ne_top
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (onTimeProductBetaCandidateLocalComplementEvent t m (m / 2)) ≠ ∞ := by
  apply ne_top_of_le_ne_top
    (simpleRandomWalk_candidateLocalComplementConcreteMajorant_series_ne_top t)
  exact ENNReal.tsum_le_tsum fun m ↦ measure_mono
    (onTimeProductBetaCandidateLocalComplementEvent_subset_concreteMajorant t m)

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongComplementSeries
