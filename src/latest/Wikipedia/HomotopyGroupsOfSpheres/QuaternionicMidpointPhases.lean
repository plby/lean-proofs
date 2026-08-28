import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointTarget

/-!
# The three scalar phases of the midpoint target matrices

The determinant constraint is solved explicitly. This classifies the
possible symmetric matrices at the midpoint, not their sphere preimages.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices

def targetPhasePlus : ℂ := 1 / 2 + Complex.I * targetBeta

def targetPhaseMinus : ℂ := 1 / 2 - Complex.I * targetBeta

theorem targetBeta_sq : targetBeta ^ 2 = 3 / 4 := by
  have hs : ((Real.sqrt (3 : ℝ) : ℂ)) ^ 2 = 3 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  norm_num [targetBeta, div_pow, hs]

theorem targetPhase_sum : targetPhasePlus + targetPhaseMinus = 1 := by
  simp only [targetPhasePlus, targetPhaseMinus]
  ring

theorem targetPhase_mul : targetPhasePlus * targetPhaseMinus = 1 := by
  calc
    _ = 1 / 4 - Complex.I ^ 2 * targetBeta ^ 2 := by
      simp only [targetPhasePlus, targetPhaseMinus]
      ring
    _ = 1 := by rw [Complex.I_sq, targetBeta_sq]; norm_num

theorem targetPhasePlus_star : star targetPhasePlus = targetPhaseMinus := by
  simp [targetPhasePlus, targetPhaseMinus, targetBeta_star, sub_eq_add_neg]

theorem targetPhaseMinus_star : star targetPhaseMinus = targetPhasePlus := by
  rw [← targetPhasePlus_star, star_star]

theorem targetPhasePlus_unitary : targetPhasePlus ∈ unitary ℂ := by
  constructor
  · rw [targetPhasePlus_star, mul_comm, targetPhase_mul]
  · rw [targetPhasePlus_star, targetPhase_mul]

theorem targetPhaseMinus_unitary : targetPhaseMinus ∈ unitary ℂ := by
  constructor
  · rw [targetPhaseMinus_star, targetPhase_mul]
  · rw [targetPhaseMinus_star, mul_comm, targetPhase_mul]

theorem targetPhase_factorization (u : ℂ) :
    (u + 1) * (u - targetPhasePlus) * (u - targetPhaseMinus) = u ^ 3 + 1 := by
  calc
    _ = u ^ 3 + u ^ 2 * (1 - (targetPhasePlus + targetPhaseMinus)) +
        u * (targetPhasePlus * targetPhaseMinus -
          (targetPhasePlus + targetPhaseMinus)) + targetPhasePlus * targetPhaseMinus := by ring
    _ = u ^ 3 + 1 := by rw [targetPhase_sum, targetPhase_mul]; ring

theorem cube_eq_neg_one_iff (u : ℂ) :
    u ^ 3 = -1 ↔ u = -1 ∨ u = targetPhasePlus ∨ u = targetPhaseMinus := by
  rw [← add_eq_zero_iff_eq_neg, ← targetPhase_factorization,
    mul_eq_zero, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, sub_eq_zero]
  exact or_assoc

theorem targetPhasePlus_cube : targetPhasePlus ^ 3 = -1 :=
  (cube_eq_neg_one_iff _).mpr (Or.inr (Or.inl rfl))

theorem targetPhaseMinus_cube : targetPhaseMinus ^ 3 = -1 :=
  (cube_eq_neg_one_iff _).mpr (Or.inr (Or.inr rfl))

theorem midpoint_target_three_matrices (B : Space (Fin 3)) (hdet : B.val.val.det = 1) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) B = targetColumn ↔
      B.val.val = (-1 : ℂ) • targetMatrix targetAlpha targetBeta ∨
      B.val.val = targetPhasePlus • targetMatrix targetAlpha targetBeta ∨
      B.val.val = targetPhaseMinus • targetMatrix targetAlpha targetBeta := by
  constructor
  · intro h
    obtain ⟨u, hu, hB⟩ := midpoint_target_forward B hdet h
    rcases (cube_eq_neg_one_iff u.val).mp hu with hphase | hphase | hphase
    · exact Or.inl (hphase ▸ hB)
    · exact Or.inr (Or.inl (hphase ▸ hB))
    · exact Or.inr (Or.inr (hphase ▸ hB))
  · intro h
    rcases h with hB | hB | hB
    · exact midpoint_target_of_matrix B ⟨-1, by constructor <;> norm_num⟩ hB
    · exact midpoint_target_of_matrix B ⟨targetPhasePlus, targetPhasePlus_unitary⟩ hB
    · exact midpoint_target_of_matrix B ⟨targetPhaseMinus, targetPhaseMinus_unitary⟩ hB

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
