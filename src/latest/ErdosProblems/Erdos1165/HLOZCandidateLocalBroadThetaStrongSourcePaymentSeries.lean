/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZCandidateLocalBroadThetaStrongZeroPrefixOrigin

/-!
# Complete on-time broad strong source payment

The positive-prefix stopped products and the zero-prefix fixed-origin tail
pay every on-time strong source base.  This file also records ordinary
measurability of the physical event, which is needed for the genuine path-law
transports.
-/

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCandidateLocalBroadThetaStrongSourcePaymentSeries

open HLOZCandidateLocalBroadSourceLowThetaGeometry
open HLOZCandidateLocalBroadSourceStrongRoute
open HLOZCandidateLocalBroadThetaProduct
open HLOZCandidateLocalBroadThetaStrongCreationCover
open HLOZCandidateLocalBroadThetaStrongPositivePayment
open HLOZCandidateLocalBroadThetaStrongZeroPrefixOrigin
open HLOZPathEvents HLOZSourceOrientedExternalLocalTime
open HLOZTypedStoppedCandidateObservability
open LazyDecomposition TilingOrientedAllCreationConcreteFamily
open TilingShellZeroSourcePartition VariableStoppedTracePartition
open ExternalProposition44 HLOZUpperEstimates

noncomputable section

abbrev DominoTiling := Tilings.Tiling

theorem orientedBroadSourceLowThetaStrongBases_eq_of_pathPrefix_eq
    (t : DominoTiling) (o : Orientation)
    (m width externalThreshold : ℕ) {s s' : WalkPath} {n : ℕ}
    (hp : pathPrefix s n = pathPrefix s' n) :
    orientedBroadSourceLowThetaStrongBases t o m width externalThreshold s n =
      orientedBroadSourceLowThetaStrongBases t o m width externalThreshold s' n := by
  classical
  unfold orientedBroadSourceLowThetaStrongBases
    orientedBroadSourceLowThetaBases visitedTilingBases visitedSites
    tilingSourceExternalBaseLocalTime localTime
  rw [hp]

theorem measurable_fixedOrientedBroadSourceLowThetaStrongBases
    (t : DominoTiling) (o : Orientation)
    (m width externalThreshold n : ℕ) :
    Measurable fun s : WalkPath ↦
      orientedBroadSourceLowThetaStrongBases t o m width externalThreshold s n := by
  apply measurable_of_pathPrefix_invariant n
  exact orientedBroadSourceLowThetaStrongBases_eq_of_pathPrefix_eq
    t o m width externalThreshold

theorem measurable_orientedBroadSourceLowThetaStrongBasesAtCreation
    (t : DominoTiling) (o : Orientation)
    (m k width externalThreshold : ℕ) :
    Measurable fun s : WalkPath ↦
      orientedBroadSourceLowThetaStrongBases t o m width externalThreshold s
        (creationTimeNat m k s) := by
  exact measurable_natIndexed (creationTimeNat m k)
    (measurable_creationTimeNat m k)
    (fun n s ↦ orientedBroadSourceLowThetaStrongBases
      t o m width externalThreshold s n)
    (measurable_fixedOrientedBroadSourceLowThetaStrongBases
      t o m width externalThreshold)

/-- Physical strong source event at an on-time rank creation. -/
def broadStrongSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ) : Set WalkPath :=
  {s | ReachesThreshold s m k ∧
    creationTimeNat m k s ≤ hlozCutoff44 m ∧
    (orientedBroadSourceLowThetaStrongBases t o m
      (candidateLocalBroadWidth48 m) (m / 2) s
        (creationTimeNat m k s)).Nonempty}

theorem measurableSet_broadStrongSourceOnTimeEvent
    (t : DominoTiling) (o : Orientation) (m k : ℕ) :
    MeasurableSet (broadStrongSourceOnTimeEvent t o m k) := by
  have hnonempty : MeasurableSet {s : WalkPath |
      (orientedBroadSourceLowThetaStrongBases t o m
        (candidateLocalBroadWidth48 m) (m / 2) s
          (creationTimeNat m k s)).Nonempty} := by
    have heq : MeasurableSet {s : WalkPath |
        orientedBroadSourceLowThetaStrongBases t o m
          (candidateLocalBroadWidth48 m) (m / 2) s
            (creationTimeNat m k s) = ∅} :=
      measurableSet_eq_fun
        (measurable_orientedBroadSourceLowThetaStrongBasesAtCreation
          t o m k (candidateLocalBroadWidth48 m) (m / 2))
        measurable_const
    rw [show {s : WalkPath |
        (orientedBroadSourceLowThetaStrongBases t o m
          (candidateLocalBroadWidth48 m) (m / 2) s
            (creationTimeNat m k s)).Nonempty} =
        {s : WalkPath |
          orientedBroadSourceLowThetaStrongBases t o m
            (candidateLocalBroadWidth48 m) (m / 2) s
              (creationTimeNat m k s) = ∅}ᶜ by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff,
        Finset.nonempty_iff_ne_empty]]
    exact heq.compl
  exact (measurableSet_thresholdReachStage m k).inter
    ((measurableSet_le (measurable_creationTimeNat m k) measurable_const).inter
      hnonempty)

theorem broadStrongSourceOnTimeEvent_subset_payment
    (t : DominoTiling) (o : Orientation) (m k : ℕ)
    (hm : 1 < m) (hk : 0 < k) :
    broadStrongSourceOnTimeEvent t o m k ⊆
      positiveBroadStrongSourceProductMajorant t o m k
          (candidateLocalBroadWidth48 m) (m / 2) ∪
        zeroPrefixBroadStrongSourceEvent t o m k
          (candidateLocalBroadWidth48 m) (m / 2) := by
  exact broadStrongSource_onTime_subset_positive_or_zero
    t o m k (candidateLocalBroadWidth48 m) (m / 2) hm hk

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

def broadStrongSmallLevelEvent (m : ℕ) : Set WalkPath :=
  if 1 < m then ∅ else Set.univ

private theorem simpleRandomWalk_broadStrongSmallLevelEvent_series_ne_top :
    ∑' m, simpleRandomWalk (broadStrongSmallLevelEvent m) ≠ ∞ := by
  apply measure_series_ne_top_of_eventually_exp_bound simpleRandomWalk _
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with m hm
  simp [broadStrongSmallLevelEvent, show 1 < m by omega]

theorem simpleRandomWalk_broadStrongSourceOnTimeEvent_series_ne_top
    (t : DominoTiling) (o : Orientation) (k : ℕ) (hk : 0 < k) :
    ∑' m, simpleRandomWalk (broadStrongSourceOnTimeEvent t o m k) ≠ ∞ := by
  have hpaid : ∑' m, simpleRandomWalk
      (positiveBroadStrongSourceProductMajorant t o m k
          (candidateLocalBroadWidth48 m) (m / 2) ∪
        zeroPrefixBroadStrongSourceEvent t o m k
          (candidateLocalBroadWidth48 m) (m / 2)) ≠ ∞ :=
    measure_union_series_ne_top
      (simpleRandomWalk_positiveBroadStrongSourceProductMajorant_series_ne_top
        t o k hk)
      (simpleRandomWalk_zeroPrefixBroadStrongSourceEvent_series_ne_top
        t o k hk)
  have hmajor : ∑' m, simpleRandomWalk
      (broadStrongSmallLevelEvent m ∪
        (positiveBroadStrongSourceProductMajorant t o m k
            (candidateLocalBroadWidth48 m) (m / 2) ∪
          zeroPrefixBroadStrongSourceEvent t o m k
            (candidateLocalBroadWidth48 m) (m / 2))) ≠ ∞ :=
    measure_union_series_ne_top
      simpleRandomWalk_broadStrongSmallLevelEvent_series_ne_top hpaid
  apply ne_top_of_le_ne_top hmajor
  apply ENNReal.tsum_le_tsum
  intro m
  apply measure_mono
  intro s hs
  by_cases hm : 1 < m
  · exact Or.inr
      (broadStrongSourceOnTimeEvent_subset_payment t o m k hm hk hs)
  · apply Or.inl
    simp [broadStrongSmallLevelEvent, hm]

end

end Erdos1165.HLOZCandidateLocalBroadThetaStrongSourcePaymentSeries
