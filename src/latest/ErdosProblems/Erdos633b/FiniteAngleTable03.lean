import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 5, 1). -/

namespace Erdos633b

def finiteAngleTable03 : Finset (ℕ × ℕ × ℕ) :=
  {(15, 2, 3),
   (20, 3, 4),
   (25, 4, 5),
   (30, 5, 6),
   (35, 5, 7)}

theorem finite_angle_table_03_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 5, 1) →
      cornerAnglePair P Q R (0, 5, 1) ∈ finiteAngleTable03.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_03_valid :
    ∀ v ∈ finiteAngleTable03,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
