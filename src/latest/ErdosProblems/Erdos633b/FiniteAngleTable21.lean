import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (3, 2, 1). -/

namespace Erdos633b

def finiteAngleTable21 : Finset (ℕ × ℕ × ℕ) :=
  {(7, 1, 2),
   (9, 1, 3),
   (11, 1, 4),
   (12, 2, 3),
   (13, 1, 5),
   (15, 1, 6),
   (16, 2, 5),
   (20, 2, 7),
   (24, 2, 9),
   (28, 2, 11)}

theorem finite_angle_table_21_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (3, 2, 1) →
      cornerAnglePair P Q R (3, 2, 1) ∈ finiteAngleTable21.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_21_valid :
    ∀ v ∈ finiteAngleTable21,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
