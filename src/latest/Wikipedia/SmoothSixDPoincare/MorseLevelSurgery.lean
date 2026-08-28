import Wikipedia.SmoothSixDPoincare.NativeMorseBoundaryPair
import Wikipedia.SmoothSixDPoincare.MorseHomeomorphicAttachment
import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryTransport
import Wikipedia.SmoothSixDPoincare.SurgeryComplementHomeomorph

/-!
# Actual surgery presentations of the two Morse levels

The chart, handle, lower frontier identity, and boundary homeomorphism are all
constructed from the original smooth Morse function. The resulting presentation
uses the actual level subspaces, not abstract replacement boundaries.
-/

noncomputable section

open Set Metric Topology Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

namespace SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
def boundaryLevelHomeomorph (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2})
    (he : ∀ x, f (e x) = f p + ρ ^ 2 ↔ x.val ∈
      frontier ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock))) :
    frontier ({x | f x ≤ f p - ρ ^ 2} ∪ range (c.normHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x = f p + ρ ^ 2} :=
  (Homeomorph.setCongr (by rw [c.range_normHandleMap ρ hρ hblock])).trans
    (ClosedCover.frontierLevelHomeomorph
      ((isClosed_le hf continuous_const).union
        (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).isClosed_range) e he)

open Classical in
/-- The lower level and actual upper level, with their actual old attaching piece. -/
def levelSurgeryBoundaryPair (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2})
    (e : ↥({x | f x ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock)) ≃ₜ
      {x : M // f x ≤ f p + ρ ^ 2})
    (he : ∀ x, f (e x) = f p + ρ ^ 2 ↔ x.val ∈
      frontier ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.attachingHandleMap ρ hρ hblock))) :
    SurgeryBoundaryPair c.NegativeCoordinates c.PositiveCoordinates
      {x : M // f x = f p - ρ ^ 2 ∧ x ∈
        frontier ({y | f y ≤ f p - ρ ^ 2} ∪ range (c.normHandleMap ρ hρ hblock))}
      {x : M // f x = f p - ρ ^ 2} {x : M // f x = f p + ρ ^ 2} :=
  (c.attachmentBoundaryData hf ρ hρ hblock hlevel).surgeryBoundaryPair.changeNewBoundary
    (c.boundaryLevelHomeomorph hf ρ hρ hblock e he)

end SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

open Classical in
/-- Construct the full surgery presentation from the original uniquely valued Morse point. -/
theorem exists_morse_surgery_boundary_pair {f : M → ℝ}
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
        ∀ z, (d.oldPiece z : M) = c.normHandleMap ρ hρ hblock
          (PuncturedHandle.sphereToBall z.1, z.2) := by
  obtain ⟨ρ, hρ, c, hblock, e, he, hlevel⟩ :=
    exists_morse_boundary_attachment_with_lower_frontier hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, c.levelSurgeryBoundaryPair hf.continuous ρ hρ hblock hlevel e he,
    fun _ => rfl⟩

open Classical in
/-- The attaching-core and belt-sphere complements in the two original levels are homeomorphic. -/
theorem exists_morse_level_complement_homeomorph {f : M → ℝ}
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
        Nonempty (d.OldComplement ≃ₜ d.NewComplement) := by
  obtain ⟨ρ, hρ, c, hblock, d, hd⟩ := exists_morse_surgery_boundary_pair hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, d, hd, ⟨d.complementHomeomorph⟩⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
