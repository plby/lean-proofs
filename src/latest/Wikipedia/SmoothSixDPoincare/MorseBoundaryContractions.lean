import Wikipedia.SmoothSixDPoincare.MorseSurgeryContractions
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryContractions

/-!
# Circle contractions across original Morse surgeries

In ambient dimension six this covers negative dimensions two and three.
The presentation, level structures, and smooth attaching sphere are all
constructed from the original function. The old boundary's circle
contractions are propagated to the entire new regular level.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

namespace SignedMorseChart

variable {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [TopologicalSpace R] [TopologicalSpace Y]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- Propagate contractions to the whole new boundary using the actual smooth
Morse attaching sphere. -/
theorem surgery_newBoundary_circle_nullhomotopies (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)] (hn : 0 < n)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f)
    (d : SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
      {x : M // f x = f p - ρ ^ 2} Y)
    (hpiece : ∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
      (PuncturedHandle.sphereToBall z.1, z.2))
    (hdim : 3 + n < Module.finrank ℝ E)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p - ρ ^ 2}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, Y), ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  have hattach := c.contMDiff_surgeryAttachingSphere n hf ρ hρ hblock hreg d hpiece
  apply d.newBoundary_circle_nullhomotopies n hn hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

end SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct the Morse surgery and prove propagation to the actual whole upper level
in the dimension range needed for middle handles. -/
theorem exists_morse_surgery_with_boundary_contractions {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p : M} (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      ∃ d : SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates
        {x : M // f x = f p - ρ ^ 2 ∧ x ∈
          frontier ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.normHandleMap ρ hρ hblock))}
        {x : M // f x = f p - ρ ^ 2} {x : M // f x = f p + ρ ^ 2},
        (∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
          (PuncturedHandle.sphereToBall z.1, z.2)) ∧
        (∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f) ∧
        (∀ x, f x = f p + ρ ^ 2 → x ∉ criticalPoints E f) ∧
        (∀ n : ℕ, 0 < n → Module.finrank ℝ c.NegativeCoordinates = n + 1 →
          3 + n < Module.finrank ℝ E →
          (∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p - ρ ^ 2}),
            ∃ q, g.Homotopic (ContinuousMap.const _ q)) →
          ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p + ρ ^ 2}),
            ∃ q, g.Homotopic (ContinuousMap.const _ q)) := by
  obtain ⟨ρ, hρ, c, hblock, d, hpiece, hlower, hupper, -⟩ :=
    exists_morse_surgery_with_contraction_transfer hf hm hp hunique
  refine ⟨ρ, hρ, c, hblock, d, hpiece, hlower, hupper, ?_⟩
  intro n hn hindex hdim hnull
  let _ : Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1) := ⟨hindex⟩
  exact c.surgery_newBoundary_circle_nullhomotopies n hn hf ρ hρ hblock hlower d hpiece hdim hnull

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
