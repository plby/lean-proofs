import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, -6, -1). -/

namespace Erdos633b

def finiteAngleTable08 : Finset (ℕ × ℕ × ℕ) :=
  {(21, 3, 4),
   (26, 4, 5),
   (31, 5, 6),
   (36, 6, 7)}

theorem finite_angle_table_08_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, -6, -1) →
      cornerAnglePair P Q R (1, -6, -1) ∈ finiteAngleTable08.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_08_valid :
    ∀ v ∈ finiteAngleTable08,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
