import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPivotComplexConstraints

/-!
# Equality in the pivot norm bound forces the parameter midpoint

For a preimage of the selected target, squared pivot norm one implies
both parameters are `π/2`, provided the parameters lie in `[0,π]`.
No assertion that every target preimage has pivot norm one is made here.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicComplexPlane QuaternionicSymmetricMatrices QuaternionicColumns

local notation "ℍ" => Quaternion ℝ

theorem schurPivot_unit_column (s t : ℝ) (B : Space (Fin 3))
    (hp : Quaternion.normSq (schurPivot s t B) = 1) :
    (rotation s t B).val 0 1 = 0 ∧ (rotation s t B).val 2 1 = 0 := by
  rw [schurPivot_normSq] at hp
  have he := (div_eq_iff (ne_of_gt (realDenominator_pos s t B))).mp hp
  have hbound := normSq_entry_le_one (rotation s t B) 1 1
  have hden := realDenominator_ge_one s t B
  have h11 : Quaternion.normSq ((rotation s t B).val 1 1) = 1 := by nlinarith [he]
  have hcol := sum_normSq_column (rotation s t B) 1
  rw [Fin.sum_univ_three, h11] at hcol
  have h0 : 0 ≤ Quaternion.normSq ((rotation s t B).val 0 1) := Quaternion.normSq_nonneg
  have h2 : 0 ≤ Quaternion.normSq ((rotation s t B).val 2 1) := Quaternion.normSq_nonneg
  constructor
  · apply Quaternion.normSq_eq_zero.mp
    nlinarith
  · apply Quaternion.normSq_eq_zero.mp
    nlinarith

theorem target_angleComplex_zero_of_pivot_unit (s t : ℝ) (B : Space (Fin 3))
    (h : firstColumnFormula s t B = targetColumn)
    (hp : Quaternion.normSq (schurPivot s t B) = 1) : angleComplex s t = 0 := by
  obtain ⟨h01, h21⟩ := schurPivot_unit_column s t B hp
  have hP : schurPivot s t B ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hp
    norm_num at hp
  have h0 := target_pivot_row s t B h 0
  change (rotation s t B).val 0 1 + (rotation s t B).val 0 0 * schurPivot s t B =
    (targetAlpha : ℍ) * referenceSquare s t at h0
  rw [h01, zero_add] at h0
  have h2 := target_pivot_row s t B h 1
  change (rotation s t B).val 2 1 + (rotation s t B).val 2 0 * schurPivot s t B =
    (targetBeta : ℍ) * referenceSquare s t at h2
  rw [h21, zero_add] at h2
  have hcomm : (targetBeta : ℍ) * (targetAlpha : ℍ) =
      (targetAlpha : ℍ) * (targetBeta : ℍ) := by
    rw [← Quaternion.coeComplex_mul, ← Quaternion.coeComplex_mul, mul_comm]
  have he : (targetBeta : ℍ) * (rotation s t B).val 0 0 =
      (targetAlpha : ℍ) * (rotation s t B).val 2 0 := by
    apply mul_right_cancel₀ hP
    rw [mul_assoc, h0, ← mul_assoc, hcomm, mul_assoc, ← h2, ← mul_assoc]
  have hw : targetBeta * angleComplex s t = 0 := by
    simpa [complexPart_mul, complexPart_coeComplex, coordinate_coeComplex,
      complexPart_rotation] using congrArg complexPart he
  exact (mul_eq_zero.mp hw).resolve_left targetBeta_ne_zero

theorem target_midpoint_of_pivot_unit (s t : ℝ) (B : Space (Fin 3))
    (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi)
    (h : firstColumnFormula s t B = targetColumn)
    (hp : Quaternion.normSq (schurPivot s t B) = 1) :
    s = Real.pi / 2 ∧ t = Real.pi / 2 := by
  have hw := target_angleComplex_zero_of_pivot_unit s t B h hp
  have hc : Real.cos s = 0 := congrArg Complex.re hw
  have hi : Real.sin s * Real.cos t = 0 := congrArg Complex.im hw
  have hmid : Real.pi / 2 ∈ Set.Icc 0 Real.pi := by
    constructor <;> linarith [Real.pi_pos]
  have hs' : s = Real.pi / 2 :=
    Real.strictAntiOn_cos.injOn hs hmid (hc.trans Real.cos_pi_div_two.symm)
  rw [hs', Real.sin_pi_div_two, one_mul] at hi
  exact ⟨hs', Real.strictAntiOn_cos.injOn ht hmid (hi.trans Real.cos_pi_div_two.symm)⟩

theorem target_pivot_normSq_lt_one_away (s t : ℝ) (B : Space (Fin 3))
    (hs : s ∈ Set.Icc 0 Real.pi) (ht : t ∈ Set.Icc 0 Real.pi)
    (h : firstColumnFormula s t B = targetColumn)
    (hne : ¬(s = Real.pi / 2 ∧ t = Real.pi / 2)) :
    Quaternion.normSq (schurPivot s t B) < 1 := by
  apply lt_of_le_of_ne (schurPivot_normSq_le_one s t B)
  exact fun hp ↦ hne (target_midpoint_of_pivot_unit s t B hs ht h hp)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
