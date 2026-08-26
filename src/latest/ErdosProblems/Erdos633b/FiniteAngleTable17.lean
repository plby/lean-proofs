import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, 10, 2). -/

namespace Erdos633b

def finiteAngleTable17 : Finset (ℕ × ℕ × ℕ) :=
  {(27, 4, 5),
   (38, 6, 7),
   (49, 8, 9),
   (60, 10, 11)}

theorem finite_angle_table_17_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, 10, 2) →
      cornerAnglePair P Q R (1, 10, 2) ∈ finiteAngleTable17.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_17_valid :
    ∀ v ∈ finiteAngleTable17,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
