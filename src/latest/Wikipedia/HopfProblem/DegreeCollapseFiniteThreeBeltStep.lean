import Wikipedia.HopfProblem.DegreeCollapseThreeBeltSignedStep
import Wikipedia.SmoothSixDPoincare.FiniteSignedCancellation

/-! # The actual finite three-belt step preserves the entire signed sum -/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold BigOperators
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}

open Classical in
theorem exists_finite_three_belt_cancellation_step
    (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4)
    (P : Finset (Hemisphere.Sphere 3)) (g : C(Hemisphere.Sphere 3, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 3)) = D.beltIntersectionPoints 3 g)
    (hgood : IsNativeTransverseBeltSphere D hf 3 3 g)
    (x y : Hemisphere.Sphere 3) (hx : x ∈ P) (hy : y ∈ P)
    (hxy : D.beltIntersectionSign 3 r g x * D.beltIntersectionSign 3 r g y = -1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 3, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ z, g' z = e (g z)) ∧
        IsNativeTransverseBeltSphere D hf 3 3 g' ∧
        ((P \ {x, y} : Finset (Hemisphere.Sphere 3)) : Set (Hemisphere.Sphere 3)) =
          D.beltIntersectionPoints 3 g' ∧
        (∀ z ∈ P \ {x, y}, (g' : Hemisphere.Sphere 3 → D.UpperLevel) =ᶠ[𝓝 z] g) ∧
        (∑ z ∈ P \ {x, y}, (D.beltIntersectionSign 3 r g' z : ℤ)) =
          ∑ z ∈ P, (D.beltIntersectionSign 3 r g z : ℤ) := by
  classical
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  have hxB : x ∈ D.beltIntersectionPoints 3 g := hP ▸ hx
  have hyB : y ∈ D.beltIntersectionPoints 3 g := hP ▸ hy
  obtain ⟨e, g', hiso, heq, hgood', hpoints, hgerm, hsign⟩ :=
    exists_signed_three_belt_cancellation_step D hf hdim hindex hnull r g hgood
      x y hxB hyB hxy
  have hP' : ((P \ {x, y} : Finset (Hemisphere.Sphere 3)) : Set (Hemisphere.Sphere 3)) =
      D.beltIntersectionPoints 3 g' := by
    rw [hpoints, ← hP]
    simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
  have hmem (z : Hemisphere.Sphere 3) (hz : z ∈ P \ {x, y}) :
      z ∈ D.beltIntersectionPoints 3 g' := hP' ▸ hz
  refine ⟨e, g', hiso, heq, hgood', hP', ?_, ?_⟩
  · exact fun z hz => hgerm z (hmem z hz)
  · exact FiniteSignedCancellation.sum_sdiff_pair_of_eq P
      (D.beltIntersectionSign 3 r g) (D.beltIntersectionSign 3 r g')
      (x := x) (y := y) hx hy hxy
      (fun z hz => hsign z (hmem z hz))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
