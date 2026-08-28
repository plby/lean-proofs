import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenHandleBody
import Wikipedia.HopfProblem.DegreeCollapseClosedTimeCutGluing
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyOpposite

/-!
# The original negative half is an actual opposite body

Its boundary is the same native boundary used by the positive-half
handle chain. Both inclusions are the original ambient point maps.
Gluing these two literal halves is homeomorphic to the unchanged closed
state, and the formulas on both complete halves are exact.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {B : Type} [TopologicalSpace B]

abbrev NegativeHalf (S : CollaredSevenState B) := {p : S.Space // S.time p ≤ 0}

theorem compactSpace_negativeHalf (S : CollaredSevenState B) : CompactSpace S.NegativeHalf :=
  isCompact_iff_compactSpace.mp
    (isClosed_le S.time_smooth.continuous continuous_const).isCompact

namespace ExcellentMorsePresentation

variable {S : CollaredSevenState B} (P : S.ExcellentMorsePresentation)

def oppositeHalf : SmoothBoundaryBody.Opposite P.halfBody := by
  let _ := S.compactSpace_negativeHalf
  let i : C(P.halfBody.boundary, S.NegativeHalf) :=
    ⟨fun p ↦ ⟨p.val, ((P.zero_iff p.val).mp (neg_eq_zero.mp p.property)).le⟩,
      continuous_subtype_val.subtype_mk _⟩
  exact {
    body := TopCat.of S.NegativeHalf
    bodyT2 := inferInstance
    bodyCompact := inferInstance
    inclusion := i
    closedEmbedding := i.continuous.isClosedEmbedding (fun p q h ↦
      Subtype.ext (congrArg (fun x : S.NegativeHalf ↦ x.val) h)) }

theorem oppositeHalf_inclusion_point (p : P.halfBody.boundary) :
    (P.oppositeHalf.inclusion p).val = p.val := rfl

def oppositeGluingHomeomorph : P.oppositeHalf.Glued ≃ₜ S.Space := by
  let _ := S.zeroAtlas
  let eB := P.halfBodyBoundaryDiffeomorph.symm.toHomeomorph
  let e := BoundaryGluing.congr P.halfBody.inclusion P.oppositeHalf.inclusion
    (ClosedTimeCut.positiveBoundary S.time) (ClosedTimeCut.negativeBoundary S.time)
    eB (Homeomorph.refl S.Half) (Homeomorph.refl S.NegativeHalf)
    (fun _ ↦ Subtype.ext rfl) (fun _ ↦ Subtype.ext rfl)
  exact e.trans (ClosedTimeCut.homeomorph S.time S.time_smooth.continuous)

theorem oppositeGluingHomeomorph_positive (p : S.Half) :
    P.oppositeGluingHomeomorph
      (BoundaryGluing.left P.halfBody.inclusion P.oppositeHalf.inclusion p) = p.val := rfl

theorem oppositeGluingHomeomorph_negative (p : S.NegativeHalf) :
    P.oppositeGluingHomeomorph
      (BoundaryGluing.right P.halfBody.inclusion P.oppositeHalf.inclusion p) = p.val := rfl

theorem oppositeHalf_nonempty [Nonempty B] : Nonempty P.oppositeHalf.body := by
  let b : B := Classical.choice inferInstance
  exact ⟨⟨(S.collar.zeroPoint b).val, (S.collar.zeroPoint_time b).le⟩⟩

end ExcellentMorsePresentation
end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
