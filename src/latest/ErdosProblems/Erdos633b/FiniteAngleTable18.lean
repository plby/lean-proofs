import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (2, -1, 0). -/

namespace Erdos633b

def finiteAngleTable18 : Finset (ℕ × ℕ × ℕ) :=
  {(7, 1, 2),
   (8, 1, 2),
   (9, 1, 2)}

theorem finite_angle_table_18_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (2, -1, 0) →
      cornerAnglePair P Q R (2, -1, 0) ∈ finiteAngleTable18.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_18_valid :
    ∀ v ∈ finiteAngleTable18,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
