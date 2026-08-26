import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 3, 1). -/

namespace Erdos633b

def finiteAngleTable01 : Finset (ℕ × ℕ × ℕ) :=
  {(9, 1, 3),
   (12, 1, 4),
   (15, 1, 5),
   (15, 2, 5),
   (15, 3, 5),
   (18, 1, 6),
   (21, 1, 7),
   (21, 2, 7),
   (21, 3, 7),
   (24, 3, 8),
   (27, 2, 9),
   (30, 3, 10),
   (33, 2, 11),
   (33, 3, 11),
   (39, 2, 13),
   (39, 3, 13),
   (42, 3, 14),
   (48, 3, 16),
   (51, 3, 17),
   (57, 3, 19),
   (60, 3, 20)}

theorem finite_angle_table_01_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 3, 1) →
      cornerAnglePair P Q R (0, 3, 1) ∈ finiteAngleTable01.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_01_valid :
    ∀ v ∈ finiteAngleTable01,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
