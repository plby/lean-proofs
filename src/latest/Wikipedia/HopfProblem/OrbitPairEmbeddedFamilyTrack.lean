import Wikipedia.HopfProblem.OrbitPairClosedImmersionRetraction
import Wikipedia.HopfProblem.OrbitPairCollisionArcTrackNeighborhoods
import Wikipedia.HopfProblem.OrbitPairTrackDiffeomorphismTransport

/-!
# Proper embedded tracks and native recovery for embedding families

For a compact spatial source, an injective smooth family has a proper
embedded time-retaining track. Spatial immersion makes this full track
immersive. Consequently every point of the track has a smooth ambient
source recovery map valid on the full preimage of its target neighborhood.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

theorem injective_track {M N : Type*} {F : ℝ × M → N}
    (hi : ∀ t, Injective (fun x => F (t, x))) : Injective (track F) := by
  rintro ⟨s, x⟩ ⟨t, y⟩ heq
  have htime : s = t := congrArg (fun q : ℝ × N => q.1) heq
  subst t
  exact Prod.ext rfl (hi s (congrArg (fun q : ℝ × N => q.2) heq))

theorem isClosedEmbedding_track {M N : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace N] [T2Space N]
    {F : ℝ × M → N} (hF : Continuous F) (hi : ∀ t, Injective (fun x => F (t, x))) :
    Topology.IsClosedEmbedding (track F) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_fst.prodMk hF) (injective_track hi) (track_isProperMap hF).isClosedMap

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_embedded_track_recovery {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ t, Injective (fun x => F (t, x)))
    (himm : ∀ t x, Injective (mfderiv I J (fun y => F (t, y)) x))
    (p : ℝ × M) :
    ∃ O : Set (ℝ × N), IsOpen O ∧ track F p ∈ O ∧ ∃ r : ℝ × N → ℝ × M,
      ContMDiffOn (𝓘(ℝ, ℝ).prod J) (𝓘(ℝ, ℝ).prod I) ∞ r O ∧
      ∀ q : ℝ × M, track F q ∈ O → r (track F q) = q :=
  NativeImmersion.exists_recovery_of_closed_immersion
    (contMDiff_fst.prodMk hF) (isClosedEmbedding_track hF.continuous hi) p
    (injective_mfderiv_track p (hF.mdifferentiableAt (by simp)) (himm p.1 p.2))

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
