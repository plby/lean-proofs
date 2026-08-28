import Wikipedia.NoExoticSixSphere.ConvexReferenceProductChart
import Wikipedia.NoExoticSixSphere.LocalInverse

/-!
# A normalized product chart about any point of the original six-manifold

Translate actual native coordinates to the selected point and identify their
model with the three-plus-three product. Restriction and positive dilation
give the radius-three chart needed for the embedded reference pair.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ProductChartCoordinates

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem exists_centered_reference_product_chart (b : M) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
      (Vector 3 × Vector 3) M ∞,
      Φ.source = ball (0 : Vector 3 × Vector 3) 3 ∧
      closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Φ.source ∧ Φ 0 = b := by
  let c := modelChartPartialDiffeomorph (I := 𝓡 6) b
  let L : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6 :=
    (EuclideanSpace.finAddEquivProd (n := 3) (m := 3)).symm
  let a : (Vector 3 × Vector 3) → Vector 6 := fun z ↦ L z + c b
  have ha : ContDiff ℝ ∞ a := L.contDiff.add contDiff_const
  have hD : HasFDerivAt a L.toContinuousLinearMap 0 :=
    L.toContinuousLinearMap.hasFDerivAt.add_const (c b)
  have hDi : (fderiv ℝ a 0).IsInvertible := by
    rw [hD.fderiv]
    exact ⟨L, rfl⟩
  obtain ⟨T, h0T, _, hT⟩ := exists_partialDiffeomorph_of_contDiffOn
    isOpen_univ (mem_univ (0 : Vector 3 × Vector 3)) ha.contDiffOn hDi
  have hT0 : T 0 = c b := by
    rw [hT]
    change L 0 + c b = c b
    rw [map_zero, zero_add]
  have hb : b ∈ c.source := mem_extChartAt_source b
  let Ψ := T.trans c.symm
  have h0Ψ : (0 : Vector 3 × Vector 3) ∈ Ψ.source := by
    refine ⟨h0T, ?_⟩
    change T 0 ∈ c.target
    rw [hT0]
    exact c.map_source hb
  have hΨ0 : Ψ 0 = b := by
    change c.symm (T 0) = b
    rw [hT0]
    exact c.left_inv hb
  obtain ⟨Φ, hsource, _, hball, _, hcenter⟩ := exists_convex_reference_chart Ψ h0Ψ
  exact ⟨Φ, hsource, hball, hcenter.trans hΨ0⟩

end NoExoticSixSphere.ProductChartCoordinates
