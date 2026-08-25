import StackExchange.Puzzling139335.CornerSupport
import StackExchange.Puzzling139335.ThreeCorners.AngularOrder
import StackExchange.Puzzling139335.ThreeCorners.Rays
import StackExchange.Puzzling139335.ThreeCorners.FullCorners

/-!
# Ordered frames at three supporting right corners

Pairwise nonpositive bisector inner products give a circular order with at
least a quarter-turn between consecutive inward-ray angles.  Normalizing
the first corner to the origin puts the other two angles in the indicated
closed ranges, with either ordering of the two remaining corners.
-/

open Set

namespace Puzzling139335.ThreeCorners

noncomputable section

/-- Two norm-√2 directions, each nonacute to the origin's outward
bisector and mutually nonacute, have the required ordered angular frames. -/
theorem exists_ordered_angles (b c : Plane)
    (hb : ‖b‖ ^ 2 = (2 : ℝ)) (hc : ‖c‖ ^ 2 = (2 : ℝ))
    (hab : inner ℝ (!₂[-1, -1] : Plane) b ≤ 0)
    (hac : inner ℝ (!₂[-1, -1] : Plane) c ≤ 0)
    (hbc : inner ℝ b c ≤ 0) :
    ∃ θ φ : ℝ,
      θ ∈ Icc (Real.pi / 2) Real.pi ∧
      φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2) ∧
      ((b = outwardBisector θ ∧ c = outwardBisector φ) ∨
        (c = outwardBisector θ ∧ b = outwardBisector φ)) := by
  obtain ⟨θ, hθ, hbθ⟩ := exists_angle_of_inner_origin_nonpos b hb hab
  obtain ⟨φ, hφ, hcφ⟩ := exists_angle_of_inner_origin_nonpos c hc hac
  have hcos : Real.cos (φ - θ) ≤ 0 := by
    rw [hbθ, hcφ, outwardBisector_inner] at hbc
    linarith
  rcases angular_order_of_cos_sub_nonpos θ φ hθ.1 hθ.2 hφ.1 hφ.2 hcos with
    horder | horder
  · exact ⟨θ, φ, horder.1, horder.2, Or.inl ⟨hbθ, hcφ⟩⟩
  · exact ⟨φ, θ, horder.1, horder.2, Or.inr ⟨hcφ, hbθ⟩⟩

/-- Ordered inward frames for any three distinct supporting right corners
whose first outward bisector has been normalized to `(-1,-1)`. -/
theorem exists_ordered_angles_of_three_support_corners
    {P : Set Plane} {a b c : Plane}
    (ha : SupportCorner P a) (hb : SupportCorner P b) (hc : SupportCorner P c)
    (hOrigin : ha.bisector = !₂[-1, -1])
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ θ φ : ℝ,
      θ ∈ Icc (Real.pi / 2) Real.pi ∧
      φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2) ∧
      ((hb.bisector = outwardBisector θ ∧ hc.bisector = outwardBisector φ ∧
          P ⊆ supportCone b θ ∧ P ⊆ supportCone c φ) ∨
        (hc.bisector = outwardBisector θ ∧ hb.bisector = outwardBisector φ ∧
          P ⊆ supportCone c θ ∧ P ⊆ supportCone b φ)) := by
  have hab' := ha.bisectors_inner_nonpos hb hab
  have hac' := ha.bisectors_inner_nonpos hc hac
  rw [hOrigin] at hab' hac'
  obtain ⟨θ, φ, hθ, hφ, horder⟩ := exists_ordered_angles
    hb.bisector hc.bisector hb.bisector_norm_sq hc.bisector_norm_sq hab' hac'
    (hb.bisectors_inner_nonpos hc hbc)
  refine ⟨θ, φ, hθ, hφ, ?_⟩
  rcases horder with ⟨hbθ, hcφ⟩ | ⟨hcθ, hbφ⟩
  · exact Or.inl ⟨hbθ, hcφ, subset_supportCone_of_bisector hb hbθ,
      subset_supportCone_of_bisector hc hcφ⟩
  · exact Or.inr ⟨hcθ, hbφ, subset_supportCone_of_bisector hc hcθ,
      subset_supportCone_of_bisector hb hbφ⟩

/-- The coordinate support frame at the origin of a set lying in the
first quadrant.  No interior hypothesis is needed for the support frame. -/
def originSupportCorner {P : Set Plane} (hzero : (0 : Plane) ∈ P)
    (hQuadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1) : SupportCorner P 0 where
  mem := hzero
  firstNormal := !₂[-1, 0]
  secondNormal := !₂[0, -1]
  norm_firstNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_secondNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  orthogonal := by simp [Schoenflies.Plane.inner_eq]
  first_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr (hQuadrant x hx).1
  second_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr (hQuadrant x hx).2

@[simp] theorem originSupportCorner_bisector {P : Set Plane}
    (hzero : (0 : Plane) ∈ P) (hQuadrant : ∀ x ∈ P, 0 ≤ x 0 ∧ 0 ≤ x 1) :
    (originSupportCorner hzero hQuadrant).bisector = !₂[-1, -1] := by
  ext i
  fin_cases i <;> simp [SupportCorner.bisector, originSupportCorner]

/-- Three actual full square-corner types in a normalized placement admit
ordered inward frames.  The order exchanges the last two corners if needed;
the output retains their actual full-corner properties and chosen witnesses. -/
theorem exists_ordered_frames_of_full_corners {P : Set Plane} {b c : Plane}
    (hSubset : P ⊆ unitSquare) (hzero : (0 : Plane) ∈ P)
    (hb : UnitPairs.IsFullSquareCorner P b) (hc : UnitPairs.IsFullSquareCorner P c)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : b ≠ c) :
    ∃ b' c' : Plane, ∃ θ φ : ℝ,
      ((b' = b ∧ c' = c) ∨ (b' = c ∧ c' = b)) ∧
      θ ∈ Icc (Real.pi / 2) Real.pi ∧
      φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2) ∧
      UnitPairs.IsFullSquareCorner P b' ∧ UnitPairs.IsFullSquareCorner P c' ∧
      ∃ hB : SupportCorner P b', ∃ hC : SupportCorner P c',
        hB.bisector = outwardBisector θ ∧ hC.bisector = outwardBisector φ ∧
        P ⊆ supportCone b' θ ∧ P ⊆ supportCone c' φ := by
  obtain ⟨hB⟩ := hb.isSupportCorner
  obtain ⟨hC⟩ := hc.isSupportCorner
  let hA := originSupportCorner hzero (fun x hx =>
    ⟨(hSubset hx).1.1, (hSubset hx).2.1⟩)
  obtain ⟨θ, φ, hθ, hφ, horder⟩ := exists_ordered_angles_of_three_support_corners
    hA hB hC (originSupportCorner_bisector _ _) hb0.symm hc0.symm hbc
  rcases horder with ⟨hBθ, hCφ, hPB, hPC⟩ | ⟨hCθ, hBφ, hPC, hPB⟩
  · exact ⟨b, c, θ, φ, Or.inl ⟨rfl, rfl⟩, hθ, hφ, hb, hc,
      hB, hC, hBθ, hCφ, hPB, hPC⟩
  · exact ⟨c, b, θ, φ, Or.inr ⟨rfl, rfl⟩, hθ, hφ, hc, hb,
      hC, hB, hCθ, hBφ, hPC, hPB⟩

end

end Puzzling139335.ThreeCorners
