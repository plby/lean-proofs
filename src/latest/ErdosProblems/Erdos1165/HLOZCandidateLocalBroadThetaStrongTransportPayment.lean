/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongSourcePaymentSeries
import ErdosProblems.Erdos1165.HLOZSourceEndpointTransportTable

/-!
# Transported broad strong source payments

Each endpoint-normalization row is the literal preimage of the measurable
on-time target event.  The four rows and the three possible old ranks form a
fixed finite union, so their measure series is summable.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongTransportPayment

open HLOZCandidateLocalBroadThetaStrongSourcePaymentSeries
open HLOZSourceEndpointTransportTable LazyDecomposition

noncomputable section

abbrev DominoTiling := Tilings.Tiling

def transportedBroadStrongSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) : Set WalkPath :=
  sourceTransportPath t cls ⁻¹'
    broadStrongSourceOnTimeEvent
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls) m k

theorem measurableSet_transportedBroadStrongSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) :
    MeasurableSet (transportedBroadStrongSourceOnTimeEvent t o cls m k) :=
  (measurableSet_broadStrongSourceOnTimeEvent
    (sourceTransportTargetTiling t cls)
    (sourceTransportTargetOrientation t o cls) m k).preimage
      (measurable_sourceTransportPath t cls)

theorem simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (m k : ℕ) :
    simpleRandomWalk (transportedBroadStrongSourceOnTimeEvent t o cls m k) =
      simpleRandomWalk
        (broadStrongSourceOnTimeEvent
          (sourceTransportTargetTiling t cls)
          (sourceTransportTargetOrientation t o cls) m k) := by
  exact simpleRandomWalk_preimage_sourceTransportPath t cls
    (measurableSet_broadStrongSourceOnTimeEvent
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls) m k)

theorem simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (cls : DominantEndpointClass)
    (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk
      (transportedBroadStrongSourceOnTimeEvent t o cls m k) ≠ ∞ := by
  simpa only [simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent]
    using simpleRandomWalk_broadStrongSourceOnTimeEvent_series_ne_top
      (sourceTransportTargetTiling t cls)
      (sourceTransportTargetOrientation t o cls) k hk

def allTilingBroadStrongSourceOnTimePaymentAtRank
    (t : DominoTiling) (rank m : ℕ) : Set WalkPath :=
  (transportedBroadStrongSourceOnTimeEvent t .even .canonical m rank ∪
      transportedBroadStrongSourceOnTimeEvent t .shifted .canonical m rank) ∪
    (transportedBroadStrongSourceOnTimeEvent t .even .opposite m rank ∪
      transportedBroadStrongSourceOnTimeEvent t .shifted .opposite m rank)

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

theorem simpleRandomWalk_allTilingBroadStrongSourceOnTimePaymentAtRank_series_ne_top
    (t : DominoTiling) (rank : ℕ) (hrank : 0 < rank) :
    ∑' m, simpleRandomWalk
      (allTilingBroadStrongSourceOnTimePaymentAtRank t rank m) ≠ ∞ := by
  apply measure_union_series_ne_top
  · exact measure_union_series_ne_top
      (simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent_series_ne_top
        t .even .canonical rank hrank)
      (simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent_series_ne_top
        t .shifted .canonical rank hrank)
  · exact measure_union_series_ne_top
      (simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent_series_ne_top
        t .even .opposite rank hrank)
      (simpleRandomWalk_transportedBroadStrongSourceOnTimeEvent_series_ne_top
        t .shifted .opposite rank hrank)

def candidateLocalBroadStrongSourceOnTimePayment
    (t : DominoTiling) (m : ℕ) : Set WalkPath :=
  allTilingBroadStrongSourceOnTimePaymentAtRank t 1 m ∪
    (allTilingBroadStrongSourceOnTimePaymentAtRank t 2 m ∪
      allTilingBroadStrongSourceOnTimePaymentAtRank t 3 m)

theorem simpleRandomWalk_candidateLocalBroadStrongSourceOnTimePayment_series_ne_top
    (t : DominoTiling) :
    ∑' m, simpleRandomWalk
      (candidateLocalBroadStrongSourceOnTimePayment t m) ≠ ∞ := by
  apply measure_union_series_ne_top
  · exact simpleRandomWalk_allTilingBroadStrongSourceOnTimePaymentAtRank_series_ne_top
      t 1 (by omega)
  · exact measure_union_series_ne_top
      (simpleRandomWalk_allTilingBroadStrongSourceOnTimePaymentAtRank_series_ne_top
        t 2 (by omega))
      (simpleRandomWalk_allTilingBroadStrongSourceOnTimePaymentAtRank_series_ne_top
        t 3 (by omega))

theorem transportedBroadStrongSourceOnTimeEvent_mem_rankPayment
    {t : DominoTiling} {o : Orientation} {cls : DominantEndpointClass}
    {rank m : ℕ} {s : WalkPath}
    (hs : s ∈ transportedBroadStrongSourceOnTimeEvent t o cls m rank) :
    s ∈ allTilingBroadStrongSourceOnTimePaymentAtRank t rank m := by
  cases o <;> cases cls <;>
    simp only [allTilingBroadStrongSourceOnTimePaymentAtRank] <;> aesop

theorem rankPayment_mem_candidateLocal
    {t : DominoTiling} {rank m : ℕ} {s : WalkPath}
    (hrank : 0 < rank) (hrankThree : rank ≤ 3)
    (hs : s ∈ allTilingBroadStrongSourceOnTimePaymentAtRank t rank m) :
    s ∈ candidateLocalBroadStrongSourceOnTimePayment t m := by
  interval_cases rank <;>
    simp only [candidateLocalBroadStrongSourceOnTimePayment] at hs ⊢ <;> aesop

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongTransportPayment
