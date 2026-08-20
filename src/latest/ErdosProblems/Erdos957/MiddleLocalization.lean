import Mathlib
import ErdosProblems.Erdos957.GeometryCore

/-!
# Honest localization of the selected middle neighbour in Erdős 957

This module isolates the missing finite geometric step in the local
case classification.  The same aligned chart is used for the flat-chain
estimate and for the selected middle edge.  Once the global chord argument
has put an extreme neighbour in the seven-vertex cyclic window, the open
middle-cone inequalities exclude the four nonadjacent positions.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957MiddleLocalization

open Erdos957GeometryCore

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}

/-! ## Scalar bounds for the selected middle ray -/

/-- A unit point in the open sixty-degree inward cone has horizontal
coordinate strictly between `-1/2` and `1/2`. -/
lemma abs_fst_lt_half_of_unit_of_middleCone {v : ℝ × ℝ}
    (hv : Erdos957Cases13.sqDist Erdos957Cases13.origin v = 1)
    (hcone : Erdos957Cases13.InOpenMiddleCone v) :
    -(1 / 2 : ℝ) < v.1 ∧ v.1 < 1 / 2 := by
  have hspos : 0 < Erdos957Cases13.sqrtThree :=
    Erdos957Cases13.sqrtThree_pos
  have hssq : Erdos957Cases13.sqrtThree ^ 2 = 3 :=
    Erdos957Cases13.sqrtThree_sq
  have hunit : v.1 ^ 2 + v.2 ^ 2 = 1 := by
    simpa using hv
  have hyneg : v.2 < 0 := by
    rcases hcone with ⟨hleft, hright⟩
    linarith
  have hxSq : v.1 ^ 2 < 1 / 4 := by
    rcases le_total 0 v.1 with hx | hx
    · have hprod : 0 ≤ Erdos957Cases13.sqrtThree * v.1 :=
        mul_nonneg hspos.le hx
      have hlt := hcone.1
      have hsquare :
          (Erdos957Cases13.sqrtThree * v.1) ^ 2 < (-v.2) ^ 2 := by
        nlinarith
      have hmulSq :
          (Erdos957Cases13.sqrtThree * v.1) ^ 2 =
            Erdos957Cases13.sqrtThree ^ 2 * v.1 ^ 2 := by ring
      rw [hmulSq, hssq] at hsquare
      nlinarith
    · have hprod : 0 ≤ -Erdos957Cases13.sqrtThree * v.1 := by
        have : Erdos957Cases13.sqrtThree * v.1 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hspos.le hx
        linarith
      have hlt := hcone.2
      have hsquare :
          (-Erdos957Cases13.sqrtThree * v.1) ^ 2 < (-v.2) ^ 2 := by
        nlinarith
      have hnegSq :
          (-Erdos957Cases13.sqrtThree * v.1) ^ 2 =
            Erdos957Cases13.sqrtThree ^ 2 * v.1 ^ 2 := by ring
      rw [hnegSq, hssq] at hsquare
      nlinarith
  constructor <;> nlinarith

/-- Two unit incidences, measured in an aligned chart, put the second point
within horizontal distance one of the selected middle point. -/
lemma abs_fst_sub_le_one_of_adj
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    {m w : Vertex A} (hmw : (unitDistanceGraph A).Adj m w) :
    |(C.coord i w).1 - (C.coord i m).1| ≤ 1 := by
  have hsquare := C.sqDist_coord i m w
  change dist (m : Point) (w : Point) = 1 at hmw
  rw [hmw] at hsquare
  simp only [Erdos957Cases13.sqDist] at hsquare
  rw [abs_le]
  constructor <;>
    nlinarith [sq_nonneg ((C.coord i w).2 - (C.coord i m).2)]

/-- Hence an extreme unit neighbour of the selected middle has horizontal
coordinate strictly between `-3/2` and `3/2`. -/
lemma extreme_neighbor_fst_bounds
    (C : P.AlignedChartData) (i : {p // p ∈ P.H})
    {m w : Vertex A}
    (hsm : (unitDistanceGraph A).Adj i.1 m)
    (hcone : Erdos957Cases13.InOpenMiddleCone (C.coord i m))
    (hmw : (unitDistanceGraph A).Adj m w) :
    -(3 / 2 : ℝ) < (C.coord i w).1 ∧ (C.coord i w).1 < 3 / 2 := by
  have hmiddleUnit : Erdos957Cases13.sqDist
      Erdos957Cases13.origin (C.coord i m) = 1 := by
    rw [show Erdos957Cases13.origin = C.coord i i.1 by
      simpa [Erdos957Cases13.origin] using (C.coord_source i).symm]
    rw [C.sqDist_coord]
    change dist (i.1 : Point) (m : Point) = 1 at hsm
    rw [hsm]
    norm_num
  have hm := abs_fst_lt_half_of_unit_of_middleCone hmiddleUnit hcone
  have hw := abs_fst_sub_le_one_of_adj C i hmw
  rw [abs_le] at hw
  constructor <;> linarith

/-! ## The four nonadjacent positions leave the middle-neighbour strip -/

private lemma right_angle_bounds
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    |F.rightAngle i 0| ≤ Real.pi / 45 ∧
      |F.rightAngle i 1| ≤ Real.pi / 45 ∧
      |F.rightAngle i 2| ≤ Real.pi / 45 ∧
      |F.rightAngle i 3| ≤ Real.pi / 45 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.rightFlatAngles i hi
  exact Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3

private lemma left_angle_bounds
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    |F.leftAngle i 0| ≤ Real.pi / 45 ∧
      |F.leftAngle i 1| ≤ Real.pi / 45 ∧
      |F.leftAngle i 2| ≤ Real.pi / 45 ∧
      |F.leftAngle i 3| ≤ Real.pi / 45 := by
  obtain ⟨h0, h1, h2, h3⟩ := F.leftFlatAngles i hi
  exact Erdos957Locality.four_edge_angles_near_horizontal h0 h1 h2 h3

/-- The second and third forward hull vertices are already to the right of
`x=3/2`. -/
lemma right_two_three_fst_gt_three_halves
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    (3 / 2 : ℝ) < (F.chart.rightOrbitCoord P i 2).1 ∧
      (3 / 2 : ℝ) < (F.chart.rightOrbitCoord P i 3).1 := by
  obtain ⟨ha0, ha1, ha2, _ha3⟩ := right_angle_bounds F i hi
  have h0 := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    (F.rightRadius_ge_one i 0) ha0 (F.rightPolar i 0).1
  have h1 := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    (F.rightRadius_ge_one i 1) ha1 (F.rightPolar i 1).1
  have h2 := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    (F.rightRadius_ge_one i 2) ha2 (F.rightPolar i 2).1
  norm_num at h0 h1 h2
  have hz : (F.chart.rightOrbitCoord P i 0).1 = 0 := by simp
  constructor <;> linarith

/-- After reflection, the second and third backward hull vertices satisfy the
same right-going estimate. -/
lemma left_two_three_reflected_fst_gt_three_halves
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) :
    (3 / 2 : ℝ) < (F.chart.leftOrbitReflectedCoord P i 2).1 ∧
      (3 / 2 : ℝ) < (F.chart.leftOrbitReflectedCoord P i 3).1 := by
  obtain ⟨ha0, ha1, ha2, _ha3⟩ := left_angle_bounds F i hi
  have h0 := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    (F.leftRadius_ge_one i 0) ha0 (F.leftPolar i 0).1
  have h1 := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    (F.leftRadius_ge_one i 1) ha1 (F.leftPolar i 1).1
  have h2 := Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
    (F.leftRadius_ge_one i 2) ha2 (F.leftPolar i 2).1
  norm_num at h0 h1 h2
  have hz : (F.chart.leftOrbitReflectedCoord P i 0).1 = 0 := by simp
  constructor <;> linarith

/-! ## Seven-window localization -/

/-- The seven cyclic positions centered at the source. -/
def sevenHullWindow (P : CyclicHullData A) (i : {p // p ∈ P.H}) :
    Finset (Vertex A) :=
  Finset.univ.image fun j : Fin 7 ↦ (sevenShift P.next j i).1

@[simp] lemma sevenShift_zero {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (0 : Fin 7) i = (next⁻¹ ^ 3) i := by
  simp [sevenShift]

@[simp] lemma sevenShift_one {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (1 : Fin 7) i = (next⁻¹ ^ 2) i := by
  simp [sevenShift, pow_succ]

@[simp] lemma sevenShift_two {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (2 : Fin 7) i = next⁻¹ i := by
  simp [sevenShift, pow_succ]

@[simp] lemma sevenShift_three {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (3 : Fin 7) i = i := by
  simp [sevenShift, pow_succ]

@[simp] lemma sevenShift_four {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (4 : Fin 7) i = next i := by
  simp [sevenShift, pow_succ]

@[simp] lemma sevenShift_five {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (5 : Fin 7) i = (next ^ 2) i := by
  simp [sevenShift, pow_succ]

@[simp] lemma sevenShift_six {I : Type*} (next : Equiv.Perm I) (i : I) :
    sevenShift next (6 : Fin 7) i = (next ^ 3) i := by
  simp [sevenShift, pow_succ]

/-- Core localization theorem.  The global large-diameter chord argument is
used only through `hwWindow`; everything after that premise is the checked
flat-chain/middle-cone calculation. -/
theorem eq_source_or_prev_or_next_of_mem_sevenHullWindow
    (F : P.FlatAlignedFrameData) (i : {p // p ∈ P.H})
    (hi : P.IsFlat i) {m w : Vertex A}
    (hsm : (unitDistanceGraph A).Adj i.1 m)
    (hcone : Erdos957Cases13.InOpenMiddleCone (F.chart.coord i m))
    (hmw : (unitDistanceGraph A).Adj m w)
    (hwWindow : w ∈ sevenHullWindow P i) :
    w = i.1 ∨ w = (P.next⁻¹ i).1 ∨ w = (P.next i).1 := by
  have hwBounds := extreme_neighbor_fst_bounds F.chart i hsm hcone hmw
  have hright := right_two_three_fst_gt_three_halves F i hi
  have hleft := left_two_three_reflected_fst_gt_three_halves F i hi
  rcases Finset.mem_image.mp hwWindow with ⟨j, _hj, hjw⟩
  fin_cases j
  · change (((P.next⁻¹) ^ 3) i).1 = w at hjw
    have hx := hleft.2
    change (3 / 2 : ℝ) <
      -(F.chart.coord i (((P.next⁻¹) ^ 3) i).1).1 at hx
    rw [hjw] at hx
    exfalso
    linarith [hwBounds.1]
  · have hjw' : (((P.next⁻¹) ^ 2) i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    have hx := hleft.1
    change (3 / 2 : ℝ) <
      -(F.chart.coord i (((P.next⁻¹) ^ 2) i).1).1 at hx
    rw [hjw'] at hx
    exfalso
    linarith [hwBounds.1]
  · have hjw' : (P.next⁻¹ i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    exact Or.inr (Or.inl hjw'.symm)
  · have hjw' : i.1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    exact Or.inl hjw'.symm
  · have hjw' : (P.next i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    exact Or.inr (Or.inr hjw'.symm)
  · have hjw' : ((P.next ^ 2) i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    have hx := hright.1
    change (3 / 2 : ℝ) <
      (F.chart.coord i ((P.next ^ 2) i).1).1 at hx
    rw [hjw'] at hx
    exfalso
    linarith [hwBounds.2]
  · have hjw' : ((P.next ^ 3) i).1 = w := by
      simpa [sevenShift, pow_succ] using hjw
    have hx := hright.2
    change (3 / 2 : ℝ) <
      (F.chart.coord i ((P.next ^ 3) i).1).1 at hx
    rw [hjw'] at hx
    exfalso
    linarith [hwBounds.2]

end Erdos957MiddleLocalization
