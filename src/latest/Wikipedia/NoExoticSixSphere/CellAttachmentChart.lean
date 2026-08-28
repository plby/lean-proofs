import Wikipedia.NoExoticSixSphere.PuncturedCellAttachment
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The actual open Euclidean chart of an attached cell

The characteristic map restricts to an open embedding on the disk's
interior. Composing with the normed-space unit-ball homeomorphism gives
the full coordinate chart required by two-cell point excision. Its
image is disjoint from the original base of the attachment.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Metric Topology TopologicalSpace

namespace NoExoticSixSphere.CellAttachmentChart

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ballInclusion : TopCat.of (ball (0 : E) 1) ⟶
    TopCat.of (PuncturedCellAttachment.Disk E) :=
  TopCat.ofHom (ContinuousMap.inclusion ball_subset_closedBall)

theorem ballInclusion_isOpenEmbedding : IsOpenEmbedding (ballInclusion (E := E)) :=
  IsOpenEmbedding.inclusion ball_subset_closedBall (isOpen_ball.preimage continuous_subtype_val)

theorem ballInclusion_not_boundary (x : ball (0 : E) 1) :
    ballInclusion x ∉ Set.range (PuncturedCellAttachment.boundary (E := E)) :=
  PuncturedCellAttachment.point_not_boundary x.val (mem_ball_zero_iff.mp x.property)

variable {A P : TopCat.{u}} {f : TopCat.of (sphere (0 : E) 1) ⟶ A}
  {i : A ⟶ P} {j : TopCat.of (PuncturedCellAttachment.Disk E) ⟶ P}
  (hP : IsPushout f PuncturedCellAttachment.boundary i j)

include hP in
theorem characteristic_isOpenEmbedding : IsOpenEmbedding (ballInclusion ≫ j) :=
  PushoutOutsideAttachment.comp_isOpenEmbedding hP ballInclusion
    ballInclusion_not_boundary ballInclusion_isOpenEmbedding

def openCell : Opens P :=
  ⟨Set.range (ballInclusion ≫ j), (characteristic_isOpenEmbedding hP).isOpen_range⟩

def chart : E ≃ₜ openCell hP :=
  Homeomorph.unitBall.trans (characteristic_isOpenEmbedding hP).isEmbedding.toHomeomorph

theorem chart_val (x : E) : (chart hP x).val = j (ballInclusion (Homeomorph.unitBall x)) := rfl

include hP in
theorem openCell_disjoint_base : Disjoint (openCell hP : Set P) (Set.range i) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨a, ha⟩
  exact PushoutOutsideAttachment.ne_other_of_notMem_range hP (ballInclusion_not_boundary x) a
    (hx.trans ha.symm)

include hP in
theorem mem_base_iff_not_mem_openCell (z : P) : z ∈ Set.range i ↔ z ∉ openCell hP := by
  constructor
  · intro hz hc
    exact Set.disjoint_left.mp (openCell_disjoint_base hP) hc hz
  · intro hz
    obtain (⟨a, ha⟩ | ⟨d, hd⟩) := Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) z
    · exact ⟨a, ha⟩
    · change j d = z at hd
      by_cases hb : d.val ∈ sphere (0 : E) 1
      · let s : sphere (0 : E) 1 := ⟨d.val, hb⟩
        have he : PuncturedCellAttachment.boundary s = d := rfl
        exact ⟨f s, (congrArg (fun k ↦ k s) hP.w).trans ((congrArg j he).trans hd)⟩
      · have hb' : d.val ∈ ball (0 : E) 1 :=
          lt_of_le_of_ne (mem_closedBall.mp d.property) (fun he ↦ hb he)
        exact False.elim (hz ⟨⟨d.val, hb'⟩, hd⟩)

end NoExoticSixSphere.CellAttachmentChart
