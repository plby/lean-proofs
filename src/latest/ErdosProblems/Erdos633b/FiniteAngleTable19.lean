import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (2, 3, 1). -/

namespace Erdos633b

def finiteAngleTable19 : Finset (ℕ × ℕ × ℕ) :=
  {(8, 1, 2),
   (11, 1, 3),
   (13, 2, 3),
   (14, 1, 4),
   (17, 1, 5),
   (18, 3, 4),
   (19, 2, 5),
   (20, 1, 6),
   (21, 3, 5),
   (25, 2, 7),
   (27, 3, 7),
   (30, 3, 8),
   (31, 2, 9),
   (36, 3, 10),
   (37, 2, 11),
   (39, 3, 11),
   (45, 3, 13),
   (48, 3, 14),
   (54, 3, 16),
   (57, 3, 17),
   (63, 3, 19)}

theorem finite_angle_table_19_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (2, 3, 1) →
      cornerAnglePair P Q R (2, 3, 1) ∈ finiteAngleTable19.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_19_valid :
    ∀ v ∈ finiteAngleTable19,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
