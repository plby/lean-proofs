import Wikipedia.SmoothSixDPoincare.OutwardLocalBoundaryHomology
import Wikipedia.SmoothSixDPoincare.MorseCollapseLocalBoundary
import Wikipedia.SmoothSixDPoincare.MorseCollapseIntersectionSigns

/-!
# Original collapse-boundary homology has the original belt-intersection sign

Specialize the proved outward local-degree formula to the actual finite
collapse representative at a native transverse belt crossing. Its positively
scaled normal derivative has exactly the original belt-intersection sign.
The local boundaries and their exact global-collapse values were constructed
in `MorseCollapseLocalBoundary`; no global sum formula is assumed here.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M} (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- The local homology contribution uses exactly the signed crossing counted by the surgery. -/
theorem collapseLocalBoundary_homology_sign_of_transverse (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : Hemisphere.Sphere (n + 2) → d.UpperLevel) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_ht : ∀ x y, NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, RegularLevel.Model E)
        g d.surgery.beltSphere x y)
      (x : Hemisphere.Sphere (n + 2)), x ∈ d.beltIntersectionPoints (n + 2) g →
      ∀ (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates),
        L.toContinuousLinearMap = fderiv ℝ
          ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) 0 →
      ∀ {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
        (b : LocalDegree.BoundaryData
          ((d.collapseNormal ∘ g) ∘ NativeParametrization.centered x) L s)
        (k : ℕ) (a : SingularHomology (UnitSphere (n + 1)) (k + 1)),
        singularHomologyMap b.normalizedMap (k + 1)
          ((SignType.sign (SphereNormalCoordinates.chartJacobian
            (NativeParametrization.centered x) j B 0) : ℤ) • a) =
          (d.beltIntersectionSign (n + 2) j g x : ℤ) •
            singularHomologyMap
              (LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx L hL s b k a
  have hs := d.contMDiffAt_collapseNormal_comp hf (n + 2) g hg x hx
  have hA := d.isInvertible_collapseNormal_comp_of_transverse hf q (n + 2) hdim g hg ht x hx
  have hc0 := NativeParametrization.centered_zero (D := EuclideanSpace ℝ (Fin (n + 2))) x
  have h := SphereNormalCoordinates.localBoundary_homology_outward n
    (NativeParametrization.centered x) j B (NativeParametrization.zero_mem_centered_source x)
    (d.collapseNormal ∘ g) (hc0.symm ▸ hs.mdifferentiableAt (by simp))
    (hc0.symm ▸ hA) L hL b k a
  rw [hc0, d.collapseNormal_comp_sign_of_transverse hf q (n + 2) hdim j g hg ht x hx] at h
  exact h

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
