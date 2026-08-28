import Wikipedia.HopfProblem.DegreeCollapseHandleCoreAttachment
import Wikipedia.SmoothSixDPoincare.MorseAttachmentExistence

/-!
# Native Morse bands are actual core-cell attachments up to homotopy

The positive disk factor is removed by the explicit relative deformation,
descended through the original attachment. The cell and its attaching
sphere keep their genuine coordinate-disk topology and native map into
the unchanged manifold.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCells

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)
  (ρ : ℝ) (hρ : 0 < ρ)
  (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
    closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)

/-- Every core cell has dimension at most the original real model dimension. -/
theorem core_dimension_le : Module.finrank ℝ c.NegativeCoordinates ≤ Module.finrank ℝ E := by
  classical
  change Module.finrank ℝ (EuclideanSpace ℝ (MorseHandle.Negative c.weights)) ≤ _
  rw [finrank_euclideanSpace]
  exact (Fintype.card_subtype_le (fun i => c.weights i = -1)).trans_eq (Fintype.card_fin _)

def coreCellMap : C(MorseHandle.UnitDisk c.NegativeCoordinates, M) :=
  (c.attachingHandleMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

theorem coreCellMap_injective : Function.Injective (coreCellMap c ρ hρ hblock) := by
  intro u v h
  exact congrArg Prod.fst (c.attachingHandleMap_injective ρ hρ hblock h)

theorem coreCellMap_lower_iff (u : MorseHandle.UnitDisk c.NegativeCoordinates) :
    f (coreCellMap c ρ hρ hblock u) ≤ f p - ρ ^ 2 ↔ ‖(u : c.NegativeCoordinates)‖ = 1 :=
  c.attachingHandleMap_lower_iff ρ hρ hblock (u, ⟨0, by simp⟩)

theorem image_core :
    (c.attachingHandleMap ρ hρ hblock) '' CoreAttachment.Core =
      range (coreCellMap c ρ hρ hblock) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    apply congrArg (c.attachingHandleMap ρ hρ hblock)
    exact Prod.ext rfl (Subtype.ext hz.symm)
  · rintro ⟨u, rfl⟩
    exact ⟨(u, ⟨0, by simp⟩), rfl, rfl⟩

variable [T2Space M] [CompactSpace M]

/-- The genuine core-cell attachment and full-handle attachment have the same homotopy type. -/
def cellHandleHomotopyEquiv (hf : Continuous f) :
    ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
      {u : MorseHandle.UnitDisk c.NegativeCoordinates | ‖(u : c.NegativeCoordinates)‖ = 1}
      (coreCellMap c ρ hρ hblock) ≃ₕ
    ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
      {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) := by
  let A := {x : M | f x ≤ f p - ρ ^ 2}
  have hA : IsCompact A := (isClosed_le hf continuous_const).isCompact
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let cell := ClosedAttachment.unionHomeomorph A _ (coreCellMap c ρ hρ hblock) hA
    (coreCellMap_injective c ρ hρ hblock) (coreCellMap_lower_iff c ρ hρ hblock)
  let core := CoreAttachment.coreUnionHomotopyEquiv A (c.attachingHandleMap ρ hρ hblock)
    (c.attachingHandleMap_injective ρ hρ hblock) (c.attachingHandleMap_lower_iff ρ hρ hblock)
  let mark := Homeomorph.setCongr
    (congrArg (fun S : Set M => A ∪ S) (image_core c ρ hρ hblock))
  exact cell.toHomotopyEquiv.trans (mark.symm.toHomotopyEquiv.trans
    (core.trans (c.attachingHandleUnionHomeomorph hf ρ hρ hblock).symm.toHomotopyEquiv))

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual Morse function supplies every geometric input of its core-cell attachment. -/
theorem exists_morse_cell_attachment
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hp : p ∈ criticalPoints E f)
    (hunique : ∀ x ∈ criticalPoints E f, f x = f p → x = p) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ), ∃ c : SignedMorseChart (E := E) f p,
      ∃ hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target,
      Nonempty (ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {u : MorseHandle.UnitDisk c.NegativeCoordinates | ‖(u : c.NegativeCoordinates)‖ = 1}
        (coreCellMap c ρ hρ hblock) ≃ₕ
          {x : M // f x ≤ f p + ρ ^ 2}) := by
  obtain ⟨ρ, hρ, c, hblock, ⟨e⟩⟩ := exists_morse_attachment hf hm hp hunique
  exact ⟨ρ, hρ, c, hblock, ⟨(cellHandleHomotopyEquiv c ρ hρ hblock hf.continuous).trans e⟩⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCells
