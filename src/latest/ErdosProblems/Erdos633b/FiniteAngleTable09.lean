import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, -5, -1). -/

namespace Erdos633b

def finiteAngleTable09 : Finset (ℕ × ℕ × ℕ) :=
  {(9, 1, 2),
   (13, 2, 3),
   (17, 3, 4),
   (21, 4, 5),
   (22, 3, 5),
   (25, 5, 6),
   (30, 5, 7),
   (31, 4, 7),
   (35, 5, 8),
   (40, 5, 9)}

theorem finite_angle_table_09_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, -5, -1) →
      cornerAnglePair P Q R (1, -5, -1) ∈ finiteAngleTable09.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_09_valid :
    ∀ v ∈ finiteAngleTable09,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
