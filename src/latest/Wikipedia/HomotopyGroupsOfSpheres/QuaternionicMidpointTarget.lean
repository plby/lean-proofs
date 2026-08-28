import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointMatrix

/-!
# Exact midpoint classification for the selected target column

For the column `(i/2,√3/2)`, the midpoint preimage condition is equivalent
to a scalar multiple of one specified symmetric matrix, with the unit
scalar satisfying `u³=-1`. The parameter-midpoint restriction is explicit.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicComplexPlane

local notation "ℍ" => Quaternion ℝ

def targetAlpha : ℂ := Complex.I / 2

def targetBeta : ℂ := ((Real.sqrt 3 / 2 : ℝ) : ℂ)

def targetColumn : Fin 2 → ℍ := ![(targetAlpha : ℍ), (targetBeta : ℍ)]

theorem targetAlpha_star : star targetAlpha = -targetAlpha := by
  simp [targetAlpha, neg_div]

theorem targetBeta_star : star targetBeta = targetBeta := by
  simp [targetBeta]

theorem targetBeta_ne_zero : targetBeta ≠ 0 := by
  have h : 0 < Real.sqrt (3 : ℝ) / 2 := by positivity
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt h)

theorem target_polynomial : targetAlpha ^ 2 - targetBeta ^ 2 = -1 := by
  have hs : ((Real.sqrt (3 : ℝ) : ℂ)) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  norm_num [targetAlpha, targetBeta, div_pow, hs]

theorem midpoint_target_constraints (B : Space (Fin 3))
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) B = targetColumn) :
    coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = 0 ∧
    coordinate (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = 0 ∧
    complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 0) = targetAlpha ∧
    complexPart (firstColumnFormula (Real.pi / 2) (Real.pi / 2) B 1) = targetBeta := by
  rw [h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem midpoint_target_forward (B : Space (Fin 3)) (hdet : B.val.val.det = 1)
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) B = targetColumn) :
    ∃ u : unitary ℂ, u.val ^ 3 = -1 ∧
      B.val.val = u.val • targetMatrix targetAlpha targetBeta := by
  obtain ⟨h0, h1, hc0, hc1⟩ := midpoint_target_constraints B h
  refine ⟨⟨B.val.val 1 1, midpoint_middle_entry_unitary B h0 h1⟩, ?_, ?_⟩
  · exact midpoint_middle_cube B targetAlpha targetBeta targetAlpha_star targetBeta_star
      targetBeta_ne_zero target_polynomial hdet h0 h1 hc0 hc1
  · exact midpoint_target_matrix B targetAlpha targetBeta targetAlpha_star targetBeta_star
      targetBeta_ne_zero h0 h1 hc0 hc1

theorem midpoint_target_of_matrix (B : Space (Fin 3)) (u : unitary ℂ)
    (hB : B.val.val = u.val • targetMatrix targetAlpha targetBeta) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) B = targetColumn := by
  have hcancel (a : ℂ) : u.val * a * star u.val = a := by
    calc
      _ = a * (u.val * star u.val) := by ring
      _ = a := by rw [u.property.2, mul_one]
  have h10 : B.val.val 1 0 = 0 := by
    rw [hB]
    simp [targetMatrix]
  have hmiddle (r : Fin 2) : B.val.val (remainingRow r) 1 = 0 := by
    rw [hB]
    fin_cases r <;> simp [remainingRow, targetMatrix, Matrix.cons_val_two]
  have hfirst (r : Fin 2) : B.val.val (remainingRow r) 0 * star (B.val.val 1 1) =
      ![targetAlpha, targetBeta] r := by
    fin_cases r
    · simpa [hB, remainingRow, targetMatrix, Matrix.cons_val_two] using hcancel targetAlpha
    · simpa [hB, remainingRow, targetMatrix, Matrix.cons_val_two] using hcancel targetBeta
  funext r
  rw [midpoint_of_zero_entry B h10 r, hmiddle r, hfirst r]
  simp only [embed, Quaternion.coeComplex_zero, zero_mul, add_zero]
  fin_cases r <;> rfl

theorem midpoint_target_iff (B : Space (Fin 3)) (hdet : B.val.val.det = 1) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) B = targetColumn ↔
      ∃ u : unitary ℂ, u.val ^ 3 = -1 ∧
        B.val.val = u.val • targetMatrix targetAlpha targetBeta := by
  constructor
  · exact midpoint_target_forward B hdet
  · rintro ⟨u, _, hB⟩
    exact midpoint_target_of_matrix B u hB

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
