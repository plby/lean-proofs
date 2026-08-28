import Wikipedia.HopfProblem.TriangleBoundaryCoordinates
import Wikipedia.HopfProblem.TriangleClosedDomainGeometry

/-!
# The finite boundary pieces of the actual half-Ford triangle

The three open sides exclude their elliptic endpoints. The first elliptic
center is the right endpoint of the circular arc, and the second center
is its left endpoint. These are actual subsets and points of the complex
plane, expressed in the coordinates used by the boundary charts.
-/

noncomputable section

open Complex Filter Metric Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The open left vertical boundary side. -/
def triangleOpenLeftSide : Set ℂ :=
  {z | z.re = stripLeft ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

/-- The open right vertical boundary side. -/
def triangleOpenRightSide : Set ℂ :=
  {z | z.re = -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖}

/-- The open circular boundary side, with both elliptic endpoints removed. -/
def triangleOpenCircleSide : Set ℂ :=
  {z | stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1}

@[simp] theorem mem_triangleOpenLeftSide {z : ℂ} :
    z ∈ triangleOpenLeftSide ↔ z.re = stripLeft ∧ 0 < z.im ∧ 1 < ‖z + 1‖ := Iff.rfl

@[simp] theorem mem_triangleOpenRightSide {z : ℂ} :
    z ∈ triangleOpenRightSide ↔ z.re = -1 / 2 ∧ 0 < z.im ∧ 1 < ‖z + 1‖ := Iff.rfl

@[simp] theorem mem_triangleOpenCircleSide {z : ℂ} :
    z ∈ triangleOpenCircleSide ↔
      stripLeft < z.re ∧ z.re < -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1 := Iff.rfl

theorem triangleOpenLeftSide_disjoint_rightSide :
    Disjoint triangleOpenLeftSide triangleOpenRightSide := by
  apply Set.disjoint_left.mpr
  intro z hL hR
  exact (ne_of_lt stripLeft_lt_right) (hL.1.symm.trans hR.1)

theorem triangleOpenLeftSide_disjoint_circleSide :
    Disjoint triangleOpenLeftSide triangleOpenCircleSide := by
  apply Set.disjoint_left.mpr
  intro z hL hC
  exact (ne_of_gt hC.1) hL.1

theorem triangleOpenRightSide_disjoint_circleSide :
    Disjoint triangleOpenRightSide triangleOpenCircleSide := by
  apply Set.disjoint_left.mpr
  intro z hR hC
  exact (ne_of_lt hC.2.1) hR.1

theorem triangleOpenLeftSide_disjoint_interior :
    Disjoint triangleOpenLeftSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hL hI
  exact (ne_of_gt hI.1) hL.1

theorem triangleOpenRightSide_disjoint_interior :
    Disjoint triangleOpenRightSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hR hI
  exact (ne_of_lt hI.2.1) hR.1

theorem triangleOpenCircleSide_disjoint_interior :
    Disjoint triangleOpenCircleSide triangleInterior := by
  apply Set.disjoint_left.mpr
  intro z hC hI
  exact (ne_of_gt hI.2.2.2) hC.2.2.2

theorem centerOne_coe_re : (centerOne : ℂ).re = -1 / 2 := by
  simp only [centerOne_val, Complex.sub_re, rho_re, Complex.one_re]
  norm_num

theorem centerTwo_coe_re : (centerTwo : ℂ).re = stripLeft := centerTwo_re

theorem centerTwo_coe_im : (centerTwo : ℂ).im = stripRight := centerTwo_im

theorem centerOne_norm_add_one : ‖(centerOne : ℂ) + 1‖ = 1 := by
  simpa only [centerOne_val, sub_add_cancel] using norm_rho

theorem centerTwo_norm_add_one : ‖(centerTwo : ℂ) + 1‖ = 1 := by
  have hsq : Complex.normSq ((centerTwo : ℂ) + 1) = 1 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
      Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im, centerTwo_re, centerTwo_im]
    nlinarith [width_sq]
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg ((centerTwo : ℂ) + 1)]

/-- A circle and a vertical line meet in at most one point of the upper
half-plane. This identifies the endpoints without selecting a square root. -/
theorem complex_eq_of_re_eq_norm_add_one_eq {z w : ℂ}
    (hr : z.re = w.re) (hz : 0 < z.im) (hw : 0 < w.im)
    (hn : ‖z + 1‖ = ‖w + 1‖) : z = w := by
  apply Complex.ext hr
  apply (sq_eq_sq₀ hz.le hw.le).mp
  have hsq : Complex.normSq (z + 1) = Complex.normSq (w + 1) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hn]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.one_re,
    Complex.add_im, Complex.one_im, add_zero, hr] at hsq
  nlinarith

/-- The first elliptic center is exactly the right circular endpoint. -/
theorem right_circle_endpoint_iff (z : ℂ) :
    (z.re = -1 / 2 ∧ 0 < z.im ∧ ‖z + 1‖ = 1) ↔ z = (centerOne : ℂ) := by
  constructor
  · rintro ⟨hr, hi, hn⟩
    exact complex_eq_of_re_eq_norm_add_one_eq
      (hr.trans centerOne_coe_re.symm) hi centerOne.im_pos
      (hn.trans centerOne_norm_add_one.symm)
  · rintro rfl
    exact ⟨centerOne_coe_re, centerOne.im_pos, centerOne_norm_add_one⟩

/-- The second elliptic center is exactly the left circular endpoint. -/
theorem left_circle_endpoint_iff (z : ℂ) :
    (z.re = stripLeft ∧ 0 < z.im ∧ ‖z + 1‖ = 1) ↔ z = (centerTwo : ℂ) := by
  constructor
  · rintro ⟨hr, hi, hn⟩
    exact complex_eq_of_re_eq_norm_add_one_eq
      (hr.trans centerTwo_coe_re.symm) hi centerTwo.im_pos
      (hn.trans centerTwo_norm_add_one.symm)
  · rintro rfl
    exact ⟨centerTwo_coe_re, centerTwo.im_pos, centerTwo_norm_add_one⟩

theorem mem_frontier_triangleInterior_iff_closedRegion {z : ℂ} :
    z ∈ frontier triangleInterior ↔ z ∈ triangleClosedRegion ∧ z ∉ triangleInterior := by
  rw [frontier, triangleInterior_isOpen.interior_eq, closure_triangleInterior]
  rfl

theorem triangleOpenLeftSide_subset_frontier :
    triangleOpenLeftSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  refine ⟨⟨hz.1.symm.le, ?_, hz.2.1, hz.2.2.le⟩, ?_⟩
  · simpa only [hz.1] using stripLeft_lt_right.le
  · exact fun h => Set.disjoint_left.mp triangleOpenLeftSide_disjoint_interior hz h

theorem triangleOpenRightSide_subset_frontier :
    triangleOpenRightSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  refine ⟨⟨?_, hz.1.le, hz.2.1, hz.2.2.le⟩, ?_⟩
  · simpa only [hz.1] using stripLeft_lt_right.le
  · exact fun h => Set.disjoint_left.mp triangleOpenRightSide_disjoint_interior hz h

theorem triangleOpenCircleSide_subset_frontier :
    triangleOpenCircleSide ⊆ frontier triangleInterior := by
  intro z hz
  rw [mem_frontier_triangleInterior_iff_closedRegion]
  exact ⟨⟨hz.1.le, hz.2.1.le, hz.2.2.1, hz.2.2.2.symm.le⟩,
    fun h => Set.disjoint_left.mp triangleOpenCircleSide_disjoint_interior hz h⟩

theorem centerOne_mem_triangleClosedRegion : (centerOne : ℂ) ∈ triangleClosedRegion := by
  refine ⟨?_, ?_, centerOne.im_pos, ?_⟩
  · rw [centerOne_coe_re]
    exact stripLeft_lt_right.le
  · rw [centerOne_coe_re]
  · rw [centerOne_norm_add_one]

theorem centerTwo_mem_triangleClosedRegion : (centerTwo : ℂ) ∈ triangleClosedRegion := by
  refine ⟨?_, ?_, centerTwo.im_pos, ?_⟩
  · rw [centerTwo_coe_re]
  · rw [centerTwo_coe_re]
    exact stripLeft_lt_right.le
  · rw [centerTwo_norm_add_one]

theorem centerOne_not_mem_triangleInterior : (centerOne : ℂ) ∉ triangleInterior := by
  intro hz
  have h := hz.2.1
  rw [centerOne_coe_re] at h
  exact lt_irrefl _ h

theorem centerTwo_not_mem_triangleInterior : (centerTwo : ℂ) ∉ triangleInterior := by
  intro hz
  have h := hz.1
  rw [centerTwo_coe_re] at h
  exact lt_irrefl _ h

theorem centerOne_mem_frontier_triangleInterior : (centerOne : ℂ) ∈ frontier triangleInterior :=
  mem_frontier_triangleInterior_iff_closedRegion.mpr
    ⟨centerOne_mem_triangleClosedRegion, centerOne_not_mem_triangleInterior⟩

theorem centerTwo_mem_frontier_triangleInterior : (centerTwo : ℂ) ∈ frontier triangleInterior :=
  mem_frontier_triangleInterior_iff_closedRegion.mpr
    ⟨centerTwo_mem_triangleClosedRegion, centerTwo_not_mem_triangleInterior⟩

theorem centerOne_mem_closure_triangleInterior : (centerOne : ℂ) ∈ closure triangleInterior := by
  rw [closure_triangleInterior]
  exact centerOne_mem_triangleClosedRegion

theorem centerTwo_mem_closure_triangleInterior : (centerTwo : ℂ) ∈ closure triangleInterior := by
  rw [closure_triangleInterior]
  exact centerTwo_mem_triangleClosedRegion

theorem centerOne_triangleInterior_nhdsWithin_neBot :
    NeBot (𝓝[triangleInterior] (centerOne : ℂ)) :=
  mem_closure_iff_nhdsWithin_neBot.mp centerOne_mem_closure_triangleInterior

theorem centerTwo_triangleInterior_nhdsWithin_neBot :
    NeBot (𝓝[triangleInterior] (centerTwo : ℂ)) :=
  mem_closure_iff_nhdsWithin_neBot.mp centerTwo_mem_closure_triangleInterior

@[simp] theorem centerOne_not_mem_triangleOpenLeftSide :
    (centerOne : ℂ) ∉ triangleOpenLeftSide := by
  simp only [mem_triangleOpenLeftSide, centerOne_norm_add_one, lt_self_iff_false, and_false,
    not_false_eq_true]

@[simp] theorem centerOne_not_mem_triangleOpenRightSide :
    (centerOne : ℂ) ∉ triangleOpenRightSide := by
  simp only [mem_triangleOpenRightSide, centerOne_norm_add_one, lt_self_iff_false, and_false,
    not_false_eq_true]

@[simp] theorem centerTwo_not_mem_triangleOpenLeftSide :
    (centerTwo : ℂ) ∉ triangleOpenLeftSide := by
  simp only [mem_triangleOpenLeftSide, centerTwo_norm_add_one, lt_self_iff_false, and_false,
    not_false_eq_true]

@[simp] theorem centerTwo_not_mem_triangleOpenRightSide :
    (centerTwo : ℂ) ∉ triangleOpenRightSide := by
  simp only [mem_triangleOpenRightSide, centerTwo_norm_add_one, lt_self_iff_false, and_false,
    not_false_eq_true]

@[simp] theorem centerOne_not_mem_triangleOpenCircleSide :
    (centerOne : ℂ) ∉ triangleOpenCircleSide := by
  intro hz
  have h := hz.2.1
  rw [centerOne_coe_re] at h
  exact lt_irrefl _ h

@[simp] theorem centerTwo_not_mem_triangleOpenCircleSide :
    (centerTwo : ℂ) ∉ triangleOpenCircleSide := by
  intro hz
  have h := hz.1
  rw [centerTwo_coe_re] at h
  exact lt_irrefl _ h

theorem centerOne_coe_ne_centerTwo : (centerOne : ℂ) ≠ (centerTwo : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  rw [centerOne_coe_re, centerTwo_coe_re] at hr
  exact (ne_of_gt stripLeft_lt_right) hr

/-- All five finite boundary pieces are mutually disjoint. -/
theorem triangleFiniteBoundaryPieces_pairwiseDisjoint :
    ([triangleOpenLeftSide, triangleOpenRightSide, triangleOpenCircleSide,
      {(centerOne : ℂ)}, {(centerTwo : ℂ)}] : List (Set ℂ)).Pairwise Disjoint := by
  simp only [List.pairwise_cons, List.forall_mem_cons, triangleOpenLeftSide_disjoint_rightSide,
    triangleOpenLeftSide_disjoint_circleSide, triangleOpenRightSide_disjoint_circleSide,
    Set.disjoint_singleton_right, Set.mem_singleton_iff,
    centerOne_not_mem_triangleOpenLeftSide, centerOne_not_mem_triangleOpenRightSide,
    centerOne_not_mem_triangleOpenCircleSide, centerTwo_not_mem_triangleOpenLeftSide,
    centerTwo_not_mem_triangleOpenRightSide, centerTwo_not_mem_triangleOpenCircleSide,
    centerOne_coe_ne_centerTwo.symm, not_false_eq_true, true_and]
  simp

/-- Every finite boundary point belongs to one of the three open sides
or is exactly one of the two elliptic endpoints. -/
theorem mem_frontier_triangleInterior_iff {z : ℂ} :
    z ∈ frontier triangleInterior ↔
      z ∈ triangleOpenLeftSide ∨ z ∈ triangleOpenRightSide ∨
        z ∈ triangleOpenCircleSide ∨ z = (centerOne : ℂ) ∨ z = (centerTwo : ℂ) := by
  constructor
  · intro hz
    obtain ⟨hR, hI⟩ := mem_frontier_triangleInterior_iff_closedRegion.mp hz
    rcases lt_or_eq_of_le hR.1 with hL | hL
    · rcases lt_or_eq_of_le hR.2.1 with hU | hU
      · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
        · exact (hI ⟨hL, hU, hR.2.2.1, hN⟩).elim
        · exact Or.inr (Or.inr (Or.inl ⟨hL, hU, hR.2.2.1, hN.symm⟩))
      · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
        · exact Or.inr (Or.inl ⟨hU, hR.2.2.1, hN⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ((right_circle_endpoint_iff z).mp ⟨hU, hR.2.2.1, hN.symm⟩))))
    · rcases lt_or_eq_of_le hR.2.2.2 with hN | hN
      · exact Or.inl ⟨hL.symm, hR.2.2.1, hN⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ((left_circle_endpoint_iff z).mp ⟨hL.symm, hR.2.2.1, hN.symm⟩))))
  · rintro (h | h | h | rfl | rfl)
    · exact triangleOpenLeftSide_subset_frontier h
    · exact triangleOpenRightSide_subset_frontier h
    · exact triangleOpenCircleSide_subset_frontier h
    · exact centerOne_mem_frontier_triangleInterior
    · exact centerTwo_mem_frontier_triangleInterior

theorem frontier_triangleInterior_eq :
    frontier triangleInterior = triangleOpenLeftSide ∪ triangleOpenRightSide ∪
      triangleOpenCircleSide ∪ {(centerOne : ℂ), (centerTwo : ℂ)} := by
  ext z
  simpa only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, or_assoc] using
    (mem_frontier_triangleInterior_iff (z := z))

theorem frontier_triangleInterior_im_lower_bound {z : ℂ} (hz : z ∈ frontier triangleInterior) :
    stripRight ≤ z.im :=
  triangleClosedRegion_im_lower_bound (mem_frontier_triangleInterior_iff_closedRegion.mp hz).1

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
