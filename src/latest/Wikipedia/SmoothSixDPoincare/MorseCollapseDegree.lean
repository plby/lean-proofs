import Wikipedia.SmoothSixDPoincare.MorseCollapseSignedCount

/-!
# The signed-count formula from native transverse embedded-sphere hypotheses

The original smooth embedded sphere and its transverse belt crossings
construct the finite set and the entire separated local-degree cover inside
the proof. The resulting homology formula has no local cover, source-class
comparison, or degree theorem as an additional hypothesis.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

/-- The actual signed-count formula, with all finite local data constructed. -/
theorem collapse_homology_signed_count (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Hemisphere.Sphere (n + 2), d.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (hinj : Function.Injective g)
      (ht : ∀ x y, NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularHomology (UnitSphere (n + 2)) (k + 2)),
      OnePointCover.sphereConnecting r hr (k + 1)
        (singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g) (k + 2) a) =
          d.beltIntersectionCount (n + 2) j g
            (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht) •
              singularHomologyMap
                (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
                  (k + 1) (SpherePoint.outwardClass n j B k a) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht r hr k a
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) :=
    (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht).fintype
  obtain ⟨D⟩ := d.nonempty_collapseNeighborhoods hf q (n + 2) hdim g hg hinj ht
  exact d.collapseSphereConnecting_signed_count hf q n hdim j B g D hg ht r hr k a

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
