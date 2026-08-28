import Wikipedia.SmoothSixDPoincare.MorseAttachingSphereSmooth
import Wikipedia.SmoothSixDPoincare.MorseLevelSurgery
import Wikipedia.SmoothSixDPoincare.SurgeryComplementContractions

/-!
# Complement contractions for the surgery constructed from the original Morse function

The attaching sphere is identified with the original chart core and proved
smooth in the actual lower-level manifold. For index two, old-level circle
contractions therefore give contractions in the new belt-sphere complement.
The old-level contraction property remains an explicit hypothesis here.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

namespace SignedMorseChart

variable {E M R Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace R] [TopologicalSpace Y]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
theorem attachingSphere_eq_attachingCoreMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (d : SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
      {x : M // f x = f p - ρ ^ 2} Y)
    (hpiece : ∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
      (PuncturedHandle.sphereToBall z.1, z.2)) :
    d.attachingSphere = c.attachingCoreMap ρ hρ hblock := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (d.oldPiece (u, PuncturedHandle.ballZero) : M) = _
  rw [hpiece]
  rfl

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

open Classical in
theorem contMDiff_surgeryAttachingSphere (n : ℕ)
    [Fact (Module.finrank ℝ c.NegativeCoordinates = n + 1)]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f)
    (d : SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
      {x : M // f x = f p - ρ ^ 2} Y)
    (hpiece : ∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
      (PuncturedHandle.sphereToBall z.1, z.2)) :
    letI := RegularLevel.chartedSpace hf hreg
    ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ d.attachingSphere := by
  let _ := RegularLevel.chartedSpace hf hreg
  rw [c.attachingSphere_eq_attachingCoreMap ρ hρ hblock d hpiece]
  exact c.contMDiff_attachingCoreMap n hf ρ hρ hblock hreg

variable [T2Space M]

open Classical in
/-- The smooth attaching-circle hypothesis is discharged by the actual native Morse formula. -/
theorem surgery_beltComplement_circle_nullhomotopies
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hreg : ∀ x, f x = f p - ρ ^ 2 → x ∉ criticalPoints E f)
    (d : SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates R
      {x : M // f x = f p - ρ ^ 2} Y)
    (hpiece : ∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
      (PuncturedHandle.sphereToBall z.1, z.2))
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 2)
    (hdim : 4 < Module.finrank ℝ E)
    (hnull : ∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p - ρ ^ 2}),
      ∃ q, g.Homotopic (ContinuousMap.const _ q)) :
    ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
      ∃ q, g.Homotopic (ContinuousMap.const _ q) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  let _ : Fact (Module.finrank ℝ c.NegativeCoordinates = 1 + 1) := ⟨hindex⟩
  have hattach := c.contMDiff_surgeryAttachingSphere 1 hf ρ hρ hblock hreg d hpiece
  apply d.beltComplement_circle_nullhomotopies_of_finrank_two hattach _ hnull
  rw [finrank_euclideanSpace_fin]
  omega

end SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct the actual surgery and its codimension-two complement-contraction transfer.
The only topological contraction premise concerns the old boundary, not the belt complement. -/
theorem exists_morse_surgery_with_contraction_transfer {f : M → ℝ}
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
        (Module.finrank ℝ c.NegativeCoordinates = 2 → 4 < Module.finrank ℝ E →
          (∀ g : C(Hemisphere.Sphere 1, {x : M // f x = f p - ρ ^ 2}),
            ∃ q, g.Homotopic (ContinuousMap.const _ q)) →
          ∀ g : C(Hemisphere.Sphere 1, d.NewComplement),
            ∃ q, g.Homotopic (ContinuousMap.const _ q)) := by
  obtain ⟨ρ, hρ, c, hblock, e, he, hlevel, hlower, hupper⟩ :=
    exists_morse_boundary_attachment_with_regular_levels hf hm hp hunique
  let d := c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e he
  have hpiece : ∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
      (PuncturedHandle.sphereToBall z.1, z.2) := fun _ => rfl
  exact ⟨ρ, hρ, c, hblock, d, hpiece, hlower, hupper,
    c.surgery_beltComplement_circle_nullhomotopies hf ρ hρ hblock hlower d hpiece⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
