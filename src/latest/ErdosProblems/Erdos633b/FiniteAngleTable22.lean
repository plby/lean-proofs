import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (3, 3, 1). -/

namespace Erdos633b

def finiteAngleTable22 : Finset (ℕ × ℕ × ℕ) :=
  {(9, 1, 2),
   (12, 1, 3),
   (15, 1, 4),
   (15, 2, 3),
   (18, 1, 5),
   (21, 1, 6),
   (21, 2, 5),
   (21, 3, 4),
   (24, 3, 5),
   (27, 2, 7),
   (30, 3, 7),
   (33, 2, 9),
   (33, 3, 8),
   (39, 2, 11),
   (39, 3, 10),
   (42, 3, 11),
   (48, 3, 13),
   (51, 3, 14),
   (57, 3, 16),
   (60, 3, 17)}

theorem finite_angle_table_22_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (3, 3, 1) →
      cornerAnglePair P Q R (3, 3, 1) ∈ finiteAngleTable22.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_22_valid :
    ∀ v ∈ finiteAngleTable22,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
