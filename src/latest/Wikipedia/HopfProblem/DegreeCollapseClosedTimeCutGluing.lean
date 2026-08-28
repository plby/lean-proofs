import Wikipedia.SmoothSixDPoincare.BoundaryGluing
import Wikipedia.SmoothSixDPoincare.ClosedCoverHomeomorph
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Gluing the actual closed halves recovers the original time space

The positive and negative closed halves are identified along their
literal zero fiber. Explicit inverse continuous maps give the original
ambient space, with both whole-half inclusions retained point for point.
No compactness, manifold structure, or new topology is assumed.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.ClosedTimeCut

open Wikipedia.SmoothSixDPoincare

variable {M : Type*} [TopologicalSpace M] (t : M → ℝ)

def positiveBoundary : C({p : M // t p = 0}, {p : M // 0 ≤ t p}) :=
  ⟨fun p ↦ ⟨p.val, p.property.ge⟩, continuous_subtype_val.subtype_mk _⟩

def negativeBoundary : C({p : M // t p = 0}, {p : M // t p ≤ 0}) :=
  ⟨fun p ↦ ⟨p.val, p.property.le⟩, continuous_subtype_val.subtype_mk _⟩

theorem half_cover : {p : M | 0 ≤ t p} ∪ {p : M | t p ≤ 0} = univ := by
  ext p
  simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
  exact le_total 0 (t p)

theorem gluing_agree (p : {p : M // 0 ≤ t p}) (q : {p : M // t p ≤ 0})
    (he : p.val = q.val) :
    BoundaryGluing.left (positiveBoundary t) (negativeBoundary t) p =
      BoundaryGluing.right (positiveBoundary t) (negativeBoundary t) q := by
  let z : {x : M // t x = 0} :=
    ⟨p.val, le_antisymm ((congrArg t he).le.trans q.property) p.property⟩
  exact (BoundaryGluing.identification (positiveBoundary t) (negativeBoundary t) z).trans
    (congrArg (BoundaryGluing.right (positiveBoundary t) (negativeBoundary t)) (Subtype.ext he))

def homeomorph (ht : Continuous t) :
    BoundaryGluing.Space (positiveBoundary t) (negativeBoundary t) ≃ₜ M := by
  let i := positiveBoundary t
  let j := negativeBoundary t
  let F : C(BoundaryGluing.Space i j, M) := BoundaryGluing.desc i j
    ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩ (fun _ ↦ rfl)
  let G := ClosedCover.glue (half_cover t) (BoundaryGluing.left i j) (BoundaryGluing.right i j)
  have hGpos (p : {p : M // 0 ≤ t p}) : G p.val = BoundaryGluing.left i j p :=
    ClosedCover.glue_left (half_cover t) _ _ p
  have hGneg (p : {p : M // t p ≤ 0}) : G p.val = BoundaryGluing.right i j p :=
    ClosedCover.glue_right (half_cover t) _ _ (gluing_agree t) p
  refine
    { toFun := F
      invFun := G
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := F.continuous
      continuous_invFun := ClosedCover.continuous_glue (half_cover t)
        (isClosed_le continuous_const ht) (isClosed_le ht continuous_const) _ _
        (BoundaryGluing.left i j).continuous (BoundaryGluing.right i j).continuous (gluing_agree t) }
  · intro q
    exact BoundaryGluing.induction_on i j q (P := fun z ↦ G (F z) = z) hGpos hGneg
  · intro p
    rcases le_total 0 (t p) with hp | hp
    · exact congrArg F (hGpos ⟨p, hp⟩)
    · exact congrArg F (hGneg ⟨p, hp⟩)

theorem homeomorph_positive (ht : Continuous t) (p : {p : M // 0 ≤ t p}) :
    homeomorph t ht (BoundaryGluing.left (positiveBoundary t) (negativeBoundary t) p) = p.val := rfl

theorem homeomorph_negative (ht : Continuous t) (p : {p : M // t p ≤ 0}) :
    homeomorph t ht (BoundaryGluing.right (positiveBoundary t) (negativeBoundary t) p) =
      p.val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ClosedTimeCut
