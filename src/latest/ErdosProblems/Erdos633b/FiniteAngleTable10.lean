import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, -4, -1). -/

namespace Erdos633b

def finiteAngleTable10 : Finset (ℕ × ℕ × ℕ) :=
  {(7, 1, 2),
   (11, 1, 3),
   (15, 1, 4),
   (17, 3, 5),
   (18, 2, 5),
   (24, 4, 7),
   (25, 3, 7),
   (26, 2, 7),
   (29, 3, 8),
   (32, 4, 9),
   (37, 3, 10),
   (40, 4, 11),
   (41, 3, 11),
   (48, 4, 13),
   (56, 4, 15)}

theorem finite_angle_table_10_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, -4, -1) →
      cornerAnglePair P Q R (1, -4, -1) ∈ finiteAngleTable10.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_10_valid :
    ∀ v ∈ finiteAngleTable10,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
