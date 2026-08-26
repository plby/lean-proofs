import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (3, 1, 1). -/

namespace Erdos633b

def finiteAngleTable20 : Finset (ℕ × ℕ × ℕ) :=
  ∅

theorem finite_angle_table_20_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (3, 1, 1) →
      cornerAnglePair P Q R (3, 1, 1) ∈ finiteAngleTable20.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_20_valid :
    ∀ v ∈ finiteAngleTable20,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
