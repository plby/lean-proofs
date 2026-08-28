import Wikipedia.NoExoticSixSphere.WhitneySphereScaledChart

/-!
# A constructed frame-one Whitney reference in any chart about the origin

Openness supplies the positive scale. The reference is an actual smooth
self-transverse sphere immersion in the given chart, with a chart contraction,
one unordered double point, and source-twisted frame obstruction one.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization WhitneySphere SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

include r in
theorem exists_whitneyReference (h0 : (0 : Vector 3 × Vector 3) ∈ Φ.source) :
    ∃ (ε : ℝ) (_ : 0 < ε) (f : C(Sphere 3, M))
      (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
      (hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x)),
      (∀ x, f x = Φ (ε • WhitneySphere.map x)) ∧
      range f ⊆ Φ.target ∧ NativeSphereSelfTransverse f ∧
      f.Homotopic (ContinuousMap.const _ (Φ 0)) ∧
      SphereSelfIntersections.unorderedParity f = 1 ∧
      e.immersedSphereFrameParity a f hf hi = 1 := by
  obtain ⟨ε, hε, hball⟩ := nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0)
  have hp : closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε ⊆ Φ.source := by
    rw [closedBall_prod_same]
    exact hball
  let Ψ := scaledChart Φ ε hε
  have hunit : closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 ⊆ Ψ.source :=
    unitProduct_subset_scaledChart_source Φ hε hp
  let f := chartContinuousMap Ψ hunit
  have hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f := contMDiff_chartMap Ψ hunit
  have hi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x) :=
    injective_mfderiv_chartMap Ψ hunit
  refine ⟨ε, hε, f, hf, hi, fun _ ↦ rfl, ?_, selfTransverse_chartMap Ψ hunit,
    ?_, unorderedParity_chartMap Ψ hunit, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact Φ.map_source ((hunit (map_mem_product x)).2)
  · have hz : Ψ 0 = Φ 0 := by
      change Φ (ε • (0 : Vector 3 × Vector 3)) = Φ 0
      rw [smul_zero]
    have H : f.Homotopic (ContinuousMap.const _ (Ψ 0)) := ⟨contraction Ψ hunit⟩
    rwa [hz] at H
  · exact e.immersedSphereFrameParity_whitney a r Ψ hunit

end NoExoticSixSphere.EuclideanEmbedding
