import Wikipedia.SmoothSixDPoincare.MorseCollapseLocalRegularity
import Wikipedia.SmoothSixDPoincare.NativeLocalDegreeBoundary

/-!
# Constructed local boundaries of the original Morse collapse

At an actual transverse belt crossing, center the existing sphere chart and
construct a small boundary inside any prescribed neighborhood and the actual
new surgery interior. Its punctured-target map is the finite part of the
original global collapse, and has the derivative's induced homology map.
-/

noncomputable section

open Set Function Topology Metric Filter
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
theorem exists_collapseLocalBoundary_of_transverse (n m : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = m)
    (g : Hemisphere.Sphere m → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 m) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 m) (𝓡 n) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere m), x ∈ d.beltIntersectionPoints m g →
      ∀ W : Set (Hemisphere.Sphere m), W ∈ 𝓝 x →
      ∃ L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] d.chart.NegativeCoordinates,
        L.toContinuousLinearMap = fderiv ℝ
          ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) 0 ∧
        Nonempty (LocalDegree.BoundaryData
          ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) L
          ((NativeParametrization.centered x).source ∩ NativeParametrization.centered x ⁻¹'
            (W ∩ g ⁻¹' d.surgery.NewInterior))) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht x hx W hW
  have hs := d.contMDiffAt_collapseNormal_comp hf m g hg x hx
  have hA := d.isInvertible_collapseNormal_comp_of_transverse hf n m hdim g hg ht x hx
  obtain ⟨v, hv⟩ := hx
  have hz : (d.collapseNormal ∘ g) x = 0 := by
    change d.collapseNormal (g x) = 0
    rw [← hv, d.collapseNormal_belt]
  have hnew : g ⁻¹' d.surgery.NewInterior ∈ 𝓝 x := by
    apply hg.continuous.continuousAt
    apply d.surgery.isOpen_newInterior.mem_nhds
    rw [← hv]
    exact d.surgery.beltSphere_mem_newInterior v
  exact LocalDegree.exists_native_boundaryData x hs hz hA
    (W ∩ g ⁻¹' d.surgery.NewInterior) (inter_mem hW hnew)

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
open Classical in
/-- Every point of the constructed boundary is evaluated by the same original global collapse. -/
theorem collapseLocalBoundary_coe [T2Space M] (hf : Continuous f) (m : ℕ)
    (g : Hemisphere.Sphere m → d.UpperLevel) (x : Hemisphere.Sphere m)
    (W : Set (Hemisphere.Sphere m))
    (L : EuclideanSpace ℝ (Fin m) ≃L[ℝ] d.chart.NegativeCoordinates)
    (b : LocalDegree.BoundaryData
      ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) L
      ((NativeParametrization.centered x).source ∩ NativeParametrization.centered x ⁻¹'
        (W ∩ g ⁻¹' d.surgery.NewInterior)))
    (u : sphere (0 : EuclideanSpace ℝ (Fin m)) 1) :
    d.levelCollapseMap hf (g (NativeParametrization.centered x
      (b.radius • (u : EuclideanSpace ℝ (Fin m))))) =
      ((b.map u).val : OnePoint d.chart.NegativeCoordinates) := by
  have hu : b.radius • (u : EuclideanSpace ℝ (Fin m)) ∈ closedBall 0 b.radius := by
    rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul b.radius b.radius_pos u]
  have hmem := b.ball_subset hu
  exact d.levelCollapse_eq_coe_collapseNormal hf hmem.2.2

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
