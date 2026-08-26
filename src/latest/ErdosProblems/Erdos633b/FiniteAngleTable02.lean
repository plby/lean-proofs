import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 4, 1). -/

namespace Erdos633b

def finiteAngleTable02 : Finset (ℕ × ℕ × ℕ) :=
  {(8, 1, 2),
   (12, 1, 3),
   (12, 2, 3),
   (16, 3, 4),
   (20, 2, 5),
   (20, 3, 5),
   (20, 4, 5),
   (28, 3, 7),
   (28, 4, 7),
   (32, 3, 8),
   (36, 4, 9),
   (44, 4, 11)}

theorem finite_angle_table_02_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 4, 1) →
      cornerAnglePair P Q R (0, 4, 1) ∈ finiteAngleTable02.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_02_valid :
    ∀ v ∈ finiteAngleTable02,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
