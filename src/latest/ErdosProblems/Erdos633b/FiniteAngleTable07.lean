import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 11, 2). -/

namespace Erdos633b

def finiteAngleTable07 : Finset (ℕ × ℕ × ℕ) :=
  {(33, 5, 6),
   (44, 7, 8),
   (55, 9, 10),
   (66, 11, 12)}

theorem finite_angle_table_07_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 11, 2) →
      cornerAnglePair P Q R (0, 11, 2) ∈ finiteAngleTable07.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_07_valid :
    ∀ v ∈ finiteAngleTable07,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
