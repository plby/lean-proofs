import Wikipedia.HopfProblem.OrbitPairClockSliceDiffeomorph
import Wikipedia.HopfProblem.OrbitPairTrackFlowFollowing

/-!
# Constructed ambient endpoint extension of a smooth embedding family

For a compact source and compact target, extend the time velocity of the
proper embedded track, normalize its ambient clock, and impose compact
time support. The resulting complete flow gives a native target
diffeomorphism carrying the initial parametrized embedding to the final
one. A jointly smooth ambient isotopy from the identity is retained.
All extension and flow ingredients are proved, not supplied as assumptions.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {G N : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]

attribute [local instance] cylinderChartedSpace cylinder_isManifold

theorem exists_ambient_diffeomorph_of_embedding_family {F : ℝ × M → N}
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) ∞ F)
    (hi : ∀ t, Injective (fun x => F (t, x)))
    (himm : ∀ t x, Injective (mfderiv I 𝓘(ℝ, G) (fun y => F (t, y)) x)) :
    ∃ d : Diffeomorph 𝓘(ℝ, G) 𝓘(ℝ, G) N N ∞,
      Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph.IsotopicToIdentity d ∧
      ∀ x : M, d (F (0, x)) = F (1, x) := by
  obtain ⟨v, hclock, hmatch⟩ := exists_supported_clock_track_velocity hF hi himm
  refine ⟨clockSliceDiffeomorph v hclock 1 (by norm_num), clockSlice_one_isotopic v hclock, ?_⟩
  intro x
  have htrack := flow_follows_track hF v hmatch (s := 1) (by norm_num) x
  have hspace := congrArg (fun p : ℝ × N => p.2) htrack
  exact hspace

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
