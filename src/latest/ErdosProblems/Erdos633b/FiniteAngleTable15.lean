import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, 8, 2). -/

namespace Erdos633b

def finiteAngleTable15 : Finset (ℕ × ℕ × ℕ) :=
  {(13, 2, 3),
   (21, 2, 5),
   (22, 4, 5),
   (30, 4, 7),
   (31, 6, 7),
   (38, 4, 9),
   (40, 8, 9),
   (47, 6, 11),
   (48, 8, 11),
   (55, 6, 13),
   (56, 8, 13),
   (64, 8, 15),
   (72, 8, 17),
   (80, 8, 19)}

theorem finite_angle_table_15_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, 8, 2) →
      cornerAnglePair P Q R (1, 8, 2) ∈ finiteAngleTable15.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_15_valid :
    ∀ v ∈ finiteAngleTable15,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
