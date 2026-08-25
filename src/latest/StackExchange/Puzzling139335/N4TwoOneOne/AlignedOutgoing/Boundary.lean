import StackExchange.Puzzling139335.N4TwoOneOne.Isometries

/-!
# The image of the source base stays on the boundary

The normalized singleton maps are actual affine isometry equivalences.
Consequently, every point on the source bottom line stays outside the
interior of the corresponding image of any subset of the square. No
membership or boundary regularity assumption is needed for this statement.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.AlignedOutgoing

noncomputable section

/-- The bottom line has no interior points in any subset of the square. -/
theorem base_not_mem_interior {P : Set Plane} (hP : P ⊆ unitSquare) (t : ℝ) :
    (!₂[t, 0] : Plane) ∉ interior P := by
  intro hp
  let f : ℝ → Plane := fun y => !₂[t, y]
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hopen : IsOpen (f ⁻¹' interior P) := isOpen_interior.preimage hf
  have hsub : f ⁻¹' interior P ⊆ Icc (0 : ℝ) 1 := by
    intro y hy
    exact (hP (interior_subset hy)).2
  have hzero : (0 : ℝ) ∈ interior (Icc (0 : ℝ) 1) :=
    (hopen.subset_interior_iff.mpr hsub) hp
  simp only [interior_Icc, mem_Ioo, lt_self_iff_false, false_and] at hzero

/-- Every point of the right image of the bottom line is noninterior. -/
theorem right_base_not_mem_interior {P : Set Plane} (hP : P ⊆ unitSquare)
    (θ u v t : ℝ) :
    rightMap θ u v (!₂[t, 0] : Plane) ∉ interior (rightMap θ u v '' P) := by
  have he : (rightIsometry θ u v : Plane → Plane) = rightMap θ u v := by
    funext p
    exact rightIsometry_apply θ u v p
  rw [← he]
  exact fun hp => base_not_mem_interior hP t
    ((mem_interior_image_affineIsometry (rightIsometry θ u v)).mp hp)

/-- Every point of the left image of the bottom line is noninterior. -/
theorem left_base_not_mem_interior {P : Set Plane} (hP : P ⊆ unitSquare)
    (θ u v t : ℝ) :
    leftMap θ u v (!₂[t, 0] : Plane) ∉ interior (leftMap θ u v '' P) := by
  have he : (leftIsometry θ u v : Plane → Plane) = leftMap θ u v := by
    funext p
    exact leftIsometry_apply θ u v p
  rw [← he]
  exact fun hp => base_not_mem_interior hP t
    ((mem_interior_image_affineIsometry (leftIsometry θ u v)).mp hp)

end

end Puzzling139335.N4TwoOneOne.AlignedOutgoing
