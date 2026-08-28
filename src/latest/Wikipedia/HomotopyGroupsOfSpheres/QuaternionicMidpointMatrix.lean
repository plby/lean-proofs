import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointComponents

/-!
# The symmetric matrix is determined by a complex midpoint target

A target column `(α,β)` with `α` purely imaginary and `β` nonzero real
determines the entire symmetric matrix up to its unit middle entry. If the
determinant is one and `α²-β²=-1`, that entry has cube equal to minus one.
These statements are conditional only on the specified midpoint target;
they are not a classification of preimages at other parameter values.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicComplexPlane

def targetMatrix (α β : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![α, 0, β; 0, 1, 0; β, 0, α]

theorem targetMatrix_det (α β : ℂ) : (targetMatrix α β).det = α ^ 2 - β ^ 2 := by
  simp [targetMatrix, Matrix.det_fin_three, Matrix.cons_val_two, pow_two]

theorem midpoint_entry_row_zero (B : Space (Fin 3))
    (h0 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = 0)
    (h1 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = 0)
    (r : Fin 2) : B.val.val (remainingRow r) 0 =
      complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B r) * B.val.val 1 1 := by
  have h10 := (midpoint_coordinate_zero_iff B).mp h0
  have hu := midpoint_middle_entry_unitary B h0 h1
  rw [midpoint_complexPart, h10, Complex.normSq_zero, add_zero, inv_one, one_smul,
    mul_assoc, hu.1, mul_one]

theorem midpoint_target_matrix (B : Space (Fin 3)) (α β : ℂ)
    (hα : star α = -α) (hβ : star β = β) (hβ0 : β ≠ 0)
    (h0 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = 0)
    (h1 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = 0)
    (hc0 : complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = α)
    (hc1 : complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = β) :
    B.val.val = B.val.val 1 1 • targetMatrix α β := by
  have h10 := (midpoint_coordinate_zero_iff B).mp h0
  have h01 : B.val.val 0 1 = 0 := (symmetric_entry B 0 1).trans h10
  have h21 : B.val.val 2 1 = 0 := (midpoint_coordinate_one B h10).symm.trans h1
  have h12 : B.val.val 1 2 = 0 := (symmetric_entry B 1 2).trans h21
  have h00 : B.val.val 0 0 = α * B.val.val 1 1 := by
    simpa only [hc0, remainingRow, Matrix.cons_val_zero] using midpoint_entry_row_zero B h0 h1 0
  have h20 : B.val.val 2 0 = β * B.val.val 1 1 := by
    simpa only [hc1, remainingRow, Matrix.cons_val_one, Matrix.cons_val_zero] using
      midpoint_entry_row_zero B h0 h1 1
  have h02 : B.val.val 0 2 = β * B.val.val 1 1 := (symmetric_entry B 0 2).trans h20
  have hphase : B.val.val 1 1 ≠ 0 := by
    intro hz
    have hu := (midpoint_middle_entry_unitary B h0 h1).1
    simp only [hz, star_zero, zero_mul] at hu
    exact zero_ne_one hu
  have hs : star (α * B.val.val 1 1) * (β * B.val.val 1 1) +
      star (β * B.val.val 1 1) * B.val.val 2 2 = 0 := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 0 2)
      (Unitary.coe_star_mul_self B.val)
    simpa only [Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three, h00, h02,
      h10, h20, star_zero, zero_mul, add_zero, Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 2)]
      using he
  have hp : (star (B.val.val 1 1) * β) * (B.val.val 2 2 - α * B.val.val 1 1) = 0 := by
    calc
      _ = star (α * B.val.val 1 1) * (β * B.val.val 1 1) +
          star (β * B.val.val 1 1) * B.val.val 2 2 := by
        rw [star_mul, star_mul, hα, hβ]
        ring
      _ = 0 := hs
  have h22 : B.val.val 2 2 = α * B.val.val 1 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (mul_ne_zero (star_ne_zero.mpr hphase) hβ0))
  apply Matrix.ext
  intro r q
  fin_cases r <;> fin_cases q <;>
    simp [targetMatrix, Matrix.cons_val_two, h00, h01, h02, h10, h12, h20, h21, h22, mul_comm]

theorem midpoint_middle_cube (B : Space (Fin 3)) (α β : ℂ)
    (hα : star α = -α) (hβ : star β = β) (hβ0 : β ≠ 0)
    (hpoly : α ^ 2 - β ^ 2 = -1) (hdet : B.val.val.det = 1)
    (h0 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = 0)
    (h1 : coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = 0)
    (hc0 : complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = α)
    (hc1 : complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = β) :
    B.val.val 1 1 ^ 3 = -1 := by
  have h := congrArg Matrix.det (midpoint_target_matrix B α β hα hβ hβ0 h0 h1 hc0 hc1)
  rw [hdet, Matrix.det_smul, Fintype.card_fin, targetMatrix_det, hpoly, mul_neg_one] at h
  exact neg_eq_iff_eq_neg.mp h.symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
