import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (5, 5, 3). -/

namespace Erdos633b

def finiteAngleTable25 : Finset (ℕ × ℕ × ℕ) :=
  ∅

theorem finite_angle_table_25_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (5, 5, 3) →
      cornerAnglePair P Q R (5, 5, 3) ∈ finiteAngleTable25.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_25_valid :
    ∀ v ∈ finiteAngleTable25,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
