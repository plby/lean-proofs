import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, 9, 2). -/

namespace Erdos633b

def finiteAngleTable16 : Finset (ℕ × ℕ × ℕ) :=
  {(24, 3, 5),
   (34, 5, 7),
   (44, 7, 9),
   (53, 7, 11),
   (54, 9, 11),
   (63, 9, 13)}

theorem finite_angle_table_16_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, 9, 2) →
      cornerAnglePair P Q R (1, 9, 2) ∈ finiteAngleTable16.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_16_valid :
    ∀ v ∈ finiteAngleTable16,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
