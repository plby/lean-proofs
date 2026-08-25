import StackExchange.Puzzling139335.CornerSupport
import StackExchange.Puzzling139335.ThreeCorners.FullBisector
import StackExchange.Puzzling139335.N7Geometry.TripleCornerBounds

/-!
# Excluding the exceptional top vertex in the opposite-parity triple case

The triangular bound has three explicit supporting corners.  If all three
vertices belong to the source set, a fourth supporting corner is impossible.
Its outward bisector would point northwest, and hence would have nonnegative
projection toward the origin, contradicting the support projection bound.
The top vertex itself is not a full right corner: two different supporting
bisectors there contradict the uniqueness of the bisector at a full corner.
-/

open Set

namespace Puzzling139335.N6.TripleOppositeParity

open TripleCornerBounds (triangle topVertex)

noncomputable section

private theorem sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := by positivity

private theorem sqrt_three_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_three_gt_one : 1 < Real.sqrt (3 : ℝ) := by
  nlinarith only [sqrt_three_sq, Real.sqrt_nonneg (3 : ℝ)]

private theorem triangle_y_le_x {x : Plane} (hx : x ∈ triangle) : x 1 ≤ x 0 := by
  have hm := mul_nonneg (sub_nonneg.mpr sqrt_three_gt_one.le) hx.1
  nlinarith only [hm, hx.2.1]

private theorem triangle_y_le_height {x : Plane} (hx : x ∈ triangle) :
    x 1 ≤ 1 / Real.sqrt 3 := by
  apply (le_div_iff₀ sqrt_three_pos).mpr
  nlinarith only [hx.2.1, hx.2.2]

private def originSupport {P : Set Plane} (hP : P ⊆ triangle) (h0 : (0 : Plane) ∈ P) :
    SupportCorner P 0 where
  mem := h0
  firstNormal := !₂[-1, 0]
  secondNormal := !₂[0, -1]
  norm_firstNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_secondNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  orthogonal := by norm_num [Schoenflies.Plane.inner_eq]
  first_support := by
    intro x hx
    have hnonneg : 0 ≤ x 0 := (hP hx).1.trans (triangle_y_le_x (hP hx))
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr hnonneg
  second_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr (hP hx).1

private def bottomRightSupport {P : Set Plane} (hP : P ⊆ triangle)
    (hB : (!₂[1, 0] : Plane) ∈ P) : SupportCorner P !₂[1, 0] where
  mem := hB
  firstNormal := !₂[1, 0]
  secondNormal := !₂[0, -1]
  norm_firstNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_secondNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  orthogonal := by norm_num [Schoenflies.Plane.inner_eq]
  first_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq] using sub_nonpos.mpr (hP hx).2.2
  second_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq] using neg_nonpos.mpr (hP hx).1

private def topSupport {P : Set Plane} (hP : P ⊆ triangle)
    (hU : topVertex ∈ P) : SupportCorner P topVertex where
  mem := hU
  firstNormal := !₂[1, 0]
  secondNormal := !₂[0, 1]
  norm_firstNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_secondNormal := by norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_two]
  orthogonal := by norm_num [Schoenflies.Plane.inner_eq]
  first_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq, topVertex] using sub_nonpos.mpr (hP hx).2.2
  second_support := by
    intro x hx
    simpa [Schoenflies.Plane.inner_eq, topVertex] using
      sub_nonpos.mpr (triangle_y_le_height (hP hx))

private def tiltedTopSupport {P : Set Plane} (hP : P ⊆ triangle)
    (hU : topVertex ∈ P) : SupportCorner P topVertex where
  mem := hU
  firstNormal := !₂[-(1 / 2 : ℝ), Real.sqrt 3 / 2]
  secondNormal := !₂[Real.sqrt 3 / 2, (1 / 2 : ℝ)]
  norm_firstNormal := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith only [sqrt_three_sq]
  norm_secondNormal := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith only [sqrt_three_sq]
  orthogonal := by simp [Schoenflies.Plane.inner_eq]; ring
  first_support := by
    intro x hx
    have hcancel : Real.sqrt (3 : ℝ) * (1 / Real.sqrt 3) = 1 := by
      field_simp [ne_of_gt sqrt_three_pos]
    simp only [Schoenflies.Plane.inner_eq, PiLp.sub_apply, topVertex,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith only [(hP hx).2.1, hcancel]
  second_support := by
    intro x hx
    have hx0 := mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Real.sqrt_nonneg (3 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2))
      (sub_nonpos.mpr (hP hx).2.2)
    have hx1 := sub_nonpos.mpr (triangle_y_le_height (hP hx))
    simp only [Schoenflies.Plane.inner_eq, PiLp.sub_apply, topVertex,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hx0, hx1]

/-- The acute top vertex of the source triangle cannot have a full square
corner germ in a subset of that triangle. -/
theorem not_full_topVertex {P : Set Plane} (hP : P ⊆ triangle) :
    ¬ UnitPairs.IsFullSquareCorner P topVertex := by
  intro hfull
  have hbis := hfull.bisector_eq (topSupport hP hfull.mem) (tiltedTopSupport hP hfull.mem)
  have hx := congrArg (fun v : Plane => v 0) hbis
  simp only [SupportCorner.bisector, topSupport, tiltedTopSupport, PiLp.add_apply,
    Matrix.cons_val_zero] at hx
  nlinarith only [hx, sqrt_three_sq]

/-- If the three vertices of the source triangle belong to the set, every
supporting right corner is one of those three vertices. -/
theorem supportCorner_eq_triangle_vertex {P : Set Plane} (hP : P ⊆ triangle)
    (h0 : (0 : Plane) ∈ P) (hB : (!₂[1, 0] : Plane) ∈ P) (hU : topVertex ∈ P)
    {C : Plane} (hC : SupportCorner P C) :
    C = 0 ∨ C = !₂[1, 0] ∨ C = topVertex := by
  by_cases hC0 : C = 0
  · exact Or.inl hC0
  by_cases hCB : C = !₂[1, 0]
  · exact Or.inr (Or.inl hCB)
  by_cases hCU : C = topVertex
  · exact Or.inr (Or.inr hCU)
  have hA := (originSupport hP h0).bisectors_inner_nonpos hC (Ne.symm hC0)
  have hB' := (bottomRightSupport hP hB).bisectors_inner_nonpos hC (Ne.symm hCB)
  have hU' := (topSupport hP hU).bisectors_inner_nonpos hC (Ne.symm hCU)
  have hAbis : (originSupport hP h0).bisector = !₂[-1, -1] := by
    ext i
    fin_cases i <;> simp [originSupport, SupportCorner.bisector]
  have hBbis : (bottomRightSupport hP hB).bisector = !₂[1, -1] := by
    ext i
    fin_cases i <;> simp [bottomRightSupport, SupportCorner.bisector]
  have hUbis : (topSupport hP hU).bisector = !₂[1, 1] := by
    ext i
    fin_cases i <;> simp [topSupport, SupportCorner.bisector]
  rw [hAbis, Schoenflies.Plane.inner_eq] at hA
  rw [hBbis, Schoenflies.Plane.inner_eq] at hB'
  rw [hUbis, Schoenflies.Plane.inner_eq] at hU'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, neg_one_mul, one_mul] at hA hB' hU'
  have hsum : hC.bisector 0 = -hC.bisector 1 := by linarith only [hA, hU']
  have hnonneg : 0 ≤ hC.bisector 1 := by linarith only [hB', hsum]
  have hproj := hC.bisector_projection h0
  have hprod := mul_nonneg hnonneg (sub_nonneg.mpr (triangle_y_le_x (hP hC.mem)))
  have hnorm : 0 < ‖C‖ := norm_pos_iff.mpr hC0
  exfalso
  rw [zero_sub, norm_neg, inner_neg_right, Schoenflies.Plane.inner_eq, hsum] at hproj
  nlinarith only [hproj, hprod, hnorm]

/-- The exceptional source vertex is absent when a second full right corner
distinct from the origin and bottom-right vertex belongs to the source set. -/
theorem topVertex_not_mem {P : Set Plane} (hP : P ⊆ triangle)
    (h0 : (0 : Plane) ∈ P) (hB : (!₂[1, 0] : Plane) ∈ P)
    {C : Plane} (hC : UnitPairs.IsFullSquareCorner P C)
    (hC0 : C ≠ 0) (hCB : C ≠ !₂[1, 0]) : topVertex ∉ P := by
  intro hU
  obtain ⟨hCsupport⟩ := hC.isSupportCorner
  rcases supportCorner_eq_triangle_vertex hP h0 hB hU hCsupport with h | h | h
  · exact hC0 h
  · exact hCB h
  · exact not_full_topVertex hP (h ▸ hC)

/-- Consequently the thirty-degree rotated source cannot touch the top side. -/
theorem not_mem_rotated_image_of_y_eq_one {P : Set Plane} (hP : P ⊆ triangle)
    (h0 : (0 : Plane) ∈ P) (hB : (!₂[1, 0] : Plane) ∈ P)
    {C : Plane} (hC : UnitPairs.IsFullSquareCorner P C)
    (hC0 : C ≠ 0) (hCB : C ≠ !₂[1, 0]) {v : Plane} (hv : v 1 = 1) :
    v ∉ TripleCornerBounds.R30 '' P := by
  intro hvP
  exact topVertex_not_mem hP h0 hB hC hC0 hCB
    (TripleCornerBounds.topVertex_mem_of_rotated_image_y_eq_one hP hvP hv)

end

end Puzzling139335.N6.TripleOppositeParity
