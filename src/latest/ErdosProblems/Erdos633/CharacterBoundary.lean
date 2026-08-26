import ErdosProblems.Erdos633.BoundaryAdditivity
import ErdosProblems.Erdos633.AngleCharacters
import ErdosProblems.Erdos633.BoundarySigns
import Mathlib.Analysis.Complex.Angle

/-!
# The integer character equations of an actual congruent tiling

Unoriented angles suffice to evaluate the sign character on incident edges:
the two possible argument signs have the same character value. A character
extended by zero handles arbitrary tile orientations, including reflections.
-/

namespace Erdos633

open scoped BigOperators

theorem coordinateDirection_neg (α β : ℝ) (w : ℤ × ℤ) :
    coordinateDirection α β (-w) =
      Complex.exp ((-angleFromCoordinates α β w : ℂ) * Complex.I) := by
  have h : angleFromCoordinates α β (-w) = -angleFromCoordinates α β w := by
    change ((-w.1 : ℤ) : ℝ) * α + ((-w.2 : ℤ) : ℝ) * β =
      -((w.1 : ℝ) * α + (w.2 : ℝ) * β)
    push_cast
    ring
  rw [coordinateDirection, h, Complex.ofReal_neg]

theorem direction_character_of_unit_angle {α β : ℝ} (u v : ℤ)
    (φ : ℂ → ℝ)
    (hrot : ∀ w z, φ (coordinateDirection α β w * z) = directionSign u v w * φ z)
    (w : ℤ × ℤ) {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hangle : InnerProductGeometry.angle x y = angleFromCoordinates α β w) :
    φ x = directionSign u v w * φ y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hn : ‖x / y‖ = 1 := by rw [norm_div, hx, hy, div_one]
  have he : Complex.exp (((x / y).arg : ℂ) * Complex.I) = x / y := by
    simpa only [hn, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I (x / y)
  have ha : |(x / y).arg| = angleFromCoordinates α β w :=
    (Complex.angle_eq_abs_arg hx0 hy0).symm.trans hangle
  have hcase : coordinateDirection α β w = x / y ∨
      coordinateDirection α β (-w) = x / y := by
    by_cases harg : 0 ≤ (x / y).arg
    · rw [abs_of_nonneg harg] at ha
      exact Or.inl (by rw [coordinateDirection, ← ha]; exact he)
    · have harg' : (x / y).arg < 0 := lt_of_not_ge harg
      rw [abs_of_neg harg'] at ha
      have hneg : -angleFromCoordinates α β w = (x / y).arg := by linarith
      exact Or.inr (by rw [coordinateDirection_neg, ← Complex.ofReal_neg, hneg]; exact he)
  rcases hcase with h | h
  · have hp : coordinateDirection α β w * y = x := by rw [h, div_mul_cancel₀ _ hy0]
    rw [← hp, hrot]
  · have hp : coordinateDirection α β (-w) * y = x := by rw [h, div_mul_cancel₀ _ hy0]
    rw [← hp, hrot, directionSign_neg]

theorem exists_based_direction_character {α β : ℝ}
    (hind : IntegerIndependentAngles α β) (πc : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates α β πc) (u v : ℤ)
    (hsign : directionSign u v πc = -1) (base : ℂ) (hbase : base ≠ 0) :
    ∃ φ : ℂ → ℝ,
      (∀ z, φ (-z) = -φ z) ∧ φ base = 1 ∧
      (∀ w z, φ (coordinateDirection α β w * z) = directionSign u v w * φ z) ∧
      (∀ z, φ z = 0 ∨ φ z = 1 ∨ φ z = -1) := by
  let φ (z : ℂ) := extendedDirectionSign α β u v (z / base)
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · intro z
    dsimp [φ]
    rw [neg_div, extendedDirectionSign_odd hind πc hπ u v hsign]
  · dsimp [φ]
    rw [div_self hbase, ← coordinateDirection_zero α β,
      extendedDirectionSign_apply_direction hind πc hπ, directionSign_zero]
  · intro w z
    dsimp [φ]
    rw [mul_div_assoc, extendedDirectionSign_rotation hind πc hπ]
  · intro z
    exact extendedDirectionSign_cases α β u v (z / base)

theorem Triangle.orientationSign_ne_zero (P : Triangle) : P.orientationSign ≠ 0 := by
  intro h
  have hs := P.orientationSign_mul_self
  rw [h, zero_mul] at hs
  norm_num at hs

theorem Triangle.angle_unitEdge_neg (P : Triangle) (k l : Fin 3) :
    InnerProductGeometry.angle (P.unitEdgeVector k) (-P.unitEdgeVector l) =
      InnerProductGeometry.angle (P.edgeVector k) (-P.edgeVector l) := by
  rw [Triangle.unitEdgeVector, Triangle.unitEdgeVector, ← smul_neg,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (inv_pos.mpr (P.sideLength_pos k)),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (inv_pos.mpr (P.sideLength_pos l)),
    Triangle.orientedEdgeVector, Triangle.orientedEdgeVector, ← smul_neg,
    InnerProductGeometry.angle_smul_smul P.orientationSign_ne_zero]

theorem Triangle.angle_unitEdge_zero_neg_two (P : Triangle) :
    InnerProductGeometry.angle (P.unitEdgeVector 0) (-P.unitEdgeVector 2) = P.angleB := by
  rw [P.angle_unitEdge_neg]
  change InnerProductGeometry.angle (P.c - P.b) (-(P.b - P.a)) =
    InnerProductGeometry.angle (P.a - P.b) (P.c - P.b)
  rw [neg_sub, InnerProductGeometry.angle_comm]

theorem Triangle.angle_unitEdge_one_neg_two (P : Triangle) :
    InnerProductGeometry.angle (P.unitEdgeVector 1) (-P.unitEdgeVector 2) = P.angleA := by
  rw [P.angle_unitEdge_neg]
  change InnerProductGeometry.angle (P.a - P.c) (-(P.b - P.a)) =
    InnerProductGeometry.angle (P.b - P.a) (P.c - P.a)
  rw [neg_sub]
  have h := InnerProductGeometry.angle_neg_neg (P.c - P.a) (P.b - P.a)
  simp only [neg_sub] at h
  exact h.trans (InnerProductGeometry.angle_comm _ _)

theorem Triangle.signedBoundary_character_factor (P : Triangle) {α β : ℝ}
    (u v : ℤ) (φ : ℂ → ℝ) (hodd : ∀ z, φ (-z) = -φ z)
    (hrot : ∀ w z, φ (coordinateDirection α β w * z) = directionSign u v w * φ z)
    (A B : ℤ × ℤ) (hA : P.angleA = angleFromCoordinates α β A)
    (hB : P.angleB = angleFromCoordinates α β B) :
    P.signedBoundary φ = φ (P.unitEdgeVector 2) *
      (P.sideLength 2 - directionSign u v B * P.sideLength 0 -
        directionSign u v A * P.sideLength 1) := by
  have h0 := direction_character_of_unit_angle u v φ hrot B
    (P.norm_unitEdgeVector 0) (by rw [norm_neg, P.norm_unitEdgeVector])
    (P.angle_unitEdge_zero_neg_two.trans hB)
  have h1 := direction_character_of_unit_angle u v φ hrot A
    (P.norm_unitEdgeVector 1) (by rw [norm_neg, P.norm_unitEdgeVector])
    (P.angle_unitEdge_one_neg_two.trans hA)
  rw [hodd] at h0 h1
  unfold Triangle.signedBoundary
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change P.sideLength 0 * φ (P.unitEdgeVector 0) +
    (P.sideLength 1 * φ (P.unitEdgeVector 1) +
      P.sideLength 2 * φ (P.unitEdgeVector 2)) = _
  rw [h0, h1]
  ring

theorem angleFromCoordinates_sub (α β : ℝ) (w z : ℤ × ℤ) :
    angleFromCoordinates α β (w - z) =
      angleFromCoordinates α β w - angleFromCoordinates α β z := by
  dsimp [angleFromCoordinates]
  push_cast
  ring

/-- The previously abstract integer boundary-sign equations now follow from
actual geometric tilings and their actual Euclidean angle coordinates. -/
theorem CongruentTiling.integerBoundarySigns
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hind : IntegerIndependentAngles R.angleA R.angleB) (πc B C : ℤ × ℤ)
    (hπ : Real.pi = angleFromCoordinates R.angleA R.angleB πc)
    (hB : P.angleB = angleFromCoordinates R.angleA R.angleB B)
    (hC : P.angleC = angleFromCoordinates R.angleA R.angleB C) :
    IntegerBoundarySigns (R.sideLength 0) (R.sideLength 1) (R.sideLength 2)
      (P.sideLength 0) (P.sideLength 1) (P.sideLength 2) πc B C := by
  intro u v hsign
  have hbase : P.unitEdgeVector 2 ≠ 0 := by
    intro h
    have hn := P.norm_unitEdgeVector 2
    rw [h, norm_zero] at hn
    norm_num at hn
  obtain ⟨φ, hodd, hφ, hrot, hcases⟩ := exists_based_direction_character
    hind πc hπ u v hsign (P.unitEdgeVector 2) hbase
  have hA : P.angleA = angleFromCoordinates R.angleA R.angleB (πc - B - C) := by
    rw [angleFromCoordinates_sub, angleFromCoordinates_sub, ← hπ, ← hB, ← hC]
    linarith [P.angle_sum]
  have houter := P.signedBoundary_character_factor u v φ hodd hrot (πc - B - C) B hA hB
  rw [hφ, one_mul] at houter
  let D := R.sideLength 2 - directionSign u v (0, 1) * R.sideLength 0 -
    directionSign u v (1, 0) * R.sideLength 1
  have ht (i : Fin N) : (T.labelledTile i).signedBoundary φ =
      φ ((T.labelledTile i).unitEdgeVector 2) * D := by
    have ha : (T.labelledTile i).angleA = angleFromCoordinates R.angleA R.angleB (1, 0) := by
      simpa [angleFromCoordinates, Triangle.cornerAngle] using T.labelledTile_cornerAngle i 0
    have hb : (T.labelledTile i).angleB = angleFromCoordinates R.angleA R.angleB (0, 1) := by
      simpa [angleFromCoordinates, Triangle.cornerAngle] using T.labelledTile_cornerAngle i 1
    have h := (T.labelledTile i).signedBoundary_character_factor u v φ hodd hrot
      (1, 0) (0, 1) ha hb
    simpa only [T.labelledTile_sideLength] using h
  have hi (i : Fin N) : ∃ m : ℤ, (m : ℝ) = φ ((T.labelledTile i).unitEdgeVector 2) := by
    rcases hcases ((T.labelledTile i).unitEdgeVector 2) with h | h | h
    · exact ⟨0, by simpa using h.symm⟩
    · exact ⟨1, by simpa using h.symm⟩
    · exact ⟨-1, by simpa using h.symm⟩
  choose m hm using hi
  refine ⟨∑ i, m i, ?_⟩
  have hsum := T.signedBoundary_eq_sum φ hodd
  simp_rw [ht, ← hm] at hsum
  rw [← Finset.sum_mul, ← Int.cast_sum, houter] at hsum
  change signedTriangleBoundary u v πc B C _ _ _ = (↑(∑ i, m i) : ℝ) * D
  rw [← hsum]
  simp only [signedTriangleBoundary, directionSign_sub, directionSign_add, hsign]
  ring

end Erdos633
