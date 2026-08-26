import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (3, 4, 2). -/

namespace Erdos633b

def finiteAngleTable23 : Finset (ℕ × ℕ × ℕ) :=
  {(13, 2, 5),
   (15, 2, 6),
   (20, 4, 7),
   (24, 4, 9),
   (28, 4, 11)}

theorem finite_angle_table_23_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (3, 4, 2) →
      cornerAnglePair P Q R (3, 4, 2) ∈ finiteAngleTable23.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_23_valid :
    ∀ v ∈ finiteAngleTable23,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
