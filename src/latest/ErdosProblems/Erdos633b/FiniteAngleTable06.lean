import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 9, 2). -/

namespace Erdos633b

def finiteAngleTable06 : Finset (ℕ × ℕ × ℕ) :=
  {(9, 1, 2),
   (18, 3, 4),
   (27, 5, 6),
   (36, 5, 8),
   (36, 7, 8),
   (45, 7, 10),
   (45, 9, 10),
   (54, 7, 12),
   (63, 9, 14),
   (72, 9, 16)}

theorem finite_angle_table_06_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 9, 2) →
      cornerAnglePair P Q R (0, 9, 2) ∈ finiteAngleTable06.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_06_valid :
    ∀ v ∈ finiteAngleTable06,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
