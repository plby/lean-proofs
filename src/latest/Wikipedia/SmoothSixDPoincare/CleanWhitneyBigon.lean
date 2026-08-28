import Wikipedia.SmoothSixDPoincare.WhitneyBigon
import Wikipedia.SmoothSixDPoincare.NormedStarConvexTubularNeighborhood
import Wikipedia.SmoothSixDPoincare.CleanNeighborhoodAvoidance

/-!
# An embedded tubular bigon relative to a supplied clean boundary neighborhood

Starting with a smooth ambient map and an already embedded immersive clean
neighborhood of the cornered boundary, construct the entire embedded bigon,
avoid the obstacle in its interior, and construct genuine tubular coordinates.
The map is unchanged on the whole prescribed neighborhood.

The initial clean neighborhood is still an explicit input. Constructing it
from intersecting handles, and matching the tubular chart to their sheet
directions, are not consequences of this theorem.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel (bigon)

variable {E M F H Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold J ∞ Y]
  [CompactSpace Y] [LindelofSpace ((ℝ × ℝ) × Y)]

/-- The entire bigon and a positive-radius normal chart are constructed relative to the
supplied clean collar; only that collar need initially be embedded and immersive. -/
theorem exists_tubular_bigon_of_clean_neighborhood
    (f : C(ℝ × ℝ, M)) (g : C(Y, M))
    (hf : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff J 𝓘(ℝ, E) ∞ g)
    (hdim : Module.finrank ℝ E = 6) (hobstacle : Module.finrank ℝ F ≤ 3)
    {h : ℝ} (hh : 0 < h) {C : Set (ℝ × ℝ)} (hC : IsClosed C)
    (hboundary : frontier (bigon h) ⊆ interior C)
    (hinj : InjOn f (bigon h ∩ C))
    (hi : ∀ x ∈ bigon h ∩ C, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f x))
    (hclean : ∀ x ∈ bigon h ∩ C, x ∉ frontier (bigon h) → f x ∉ range g) :
    ∃ f' : C(ℝ × ℝ, M), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f' ∧
      f.HomotopicRel f' C ∧ Topology.IsClosedEmbedding (fun x : bigon h => f' x) ∧
      (∀ x ∈ bigon h, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f' x)) ∧
      (∀ x ∈ interior (bigon h), f' x ∉ range g) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin 4)) 𝓘(ℝ, E)
            ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 4)) M ∞,
          bigon h ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
          (∀ x, Φ (x, 0) = f' x) ∧
          (∀ x ∈ bigon h ∩ C, Φ (x, 0) = f x) := by
  have hplane : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp [Module.finrank_prod]
  obtain ⟨f', hf', hrel, hemb, hi', havoid⟩ :=
    ManifoldImmersion.exists_relative_embedded_avoidance_of_clean_neighborhood f g hf hg
      hplane (by omega) (by omega) (WhitneyPairModel.isCompact_bigon hh)
      hC hboundary hinj hi hclean
  have hinj' : InjOn f' (bigon h) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  obtain ⟨ε, hε, Φ, hsource, hzero, -⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf'
      (WhitneyPairModel.isCompact_bigon hh) (WhitneyPairModel.zero_mem_bigon hh.le)
      (WhitneyPairModel.starConvex_bigon hh.le) hinj' hi' 4 (by omega)
      isOpen_univ (mapsTo_univ _ _)
  refine ⟨f', hf', hrel, hemb, hi', ?_, ε, hε, Φ, hsource, hzero, ?_⟩
  · intro x hx
    apply havoid x ⟨interior_subset hx, ?_⟩
    exact fun hfront => hfront.2 hx
  · intro x hx
    exact (hzero x).trans (hrel.fst_eq_snd hx.2).symm

end Wikipedia.SmoothSixDPoincare
