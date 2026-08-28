import Wikipedia.SmoothSixDPoincare.TransverseBeltSphere
import Wikipedia.SmoothSixDPoincare.FiniteSignedCancellation

/-! # The actual signed cancellation step on a finite crossing set -/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold BigOperators

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- The actual geometric step deletes a finite pair and preserves its signed sum. -/
theorem exists_finite_belt_cancellation_step
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (P : Finset (Hemisphere.Sphere 2)) (g : C(Hemisphere.Sphere 2, D.UpperLevel))
    (hP : (P : Set (Hemisphere.Sphere 2)) = D.beltIntersectionPoints 2 g)
    (hgood : D.IsTransverseBeltSphere hf hdim hindex g)
    (x y : Hemisphere.Sphere 2) (hx : x ∈ P) (hy : y ∈ P)
    (hxy : D.beltIntersectionSign 2 r g x * D.beltIntersectionSign 2 r g y = -1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        D.UpperLevel D.UpperLevel ∞,
      ∃ g' : C(Hemisphere.Sphere 2, D.UpperLevel),
        SupportedDiffeomorph.IsotopicToIdentity e ∧ (∀ z, g' z = e (g z)) ∧
        D.IsTransverseBeltSphere hf hdim hindex g' ∧
        ((P \ {x, y} : Finset (Hemisphere.Sphere 2)) : Set (Hemisphere.Sphere 2)) =
          D.beltIntersectionPoints 2 g' ∧
        (∀ z ∈ P \ {x, y}, (g' : Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 z] g) ∧
        (∑ z ∈ P \ {x, y}, (D.beltIntersectionSign 2 r g' z : ℤ)) =
          ∑ z ∈ P, (D.beltIntersectionSign 2 r g z : ℤ) := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  have hxB : x ∈ D.beltIntersectionPoints 2 g := hP ▸ hx
  have hyB : y ∈ D.beltIntersectionPoints 2 g := hP ▸ hy
  obtain ⟨e, g', hiso, heq, hg', hinj', hi', ht', hpoints, hgerm, hsign⟩ :=
    D.exists_signed_belt_cancellation_step hf hdim hindex hnull r g hg hinj hi ht
      x y hxB hyB hxy
  have hP' : ((P \ {x, y} : Finset (Hemisphere.Sphere 2)) : Set (Hemisphere.Sphere 2)) =
      D.beltIntersectionPoints 2 g' := by
    rw [hpoints, ← hP]
    simp only [Finset.coe_sdiff, Finset.coe_insert, Finset.coe_singleton]
  have hmem (z : Hemisphere.Sphere 2) (hz : z ∈ P \ {x, y}) :
      z ∈ D.beltIntersectionPoints 2 g' := hP' ▸ hz
  refine ⟨e, g', hiso, heq, ⟨hg', hinj', hi', ht'⟩, hP', ?_, ?_⟩
  · exact fun z hz => hgerm z (hmem z hz)
  · exact FiniteSignedCancellation.sum_sdiff_pair_of_eq P
      (D.beltIntersectionSign 2 r g) (D.beltIntersectionSign 2 r g')
      (x := x) (y := y) hx hy hxy
      (fun z hz => hsign z (hmem z hz))

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
