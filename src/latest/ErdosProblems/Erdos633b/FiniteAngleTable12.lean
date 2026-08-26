import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, 5, 2). -/

namespace Erdos633b

def finiteAngleTable12 : Finset (ℕ × ℕ × ℕ) :=
  {(13, 1, 5),
   (18, 1, 7),
   (19, 3, 7),
   (21, 2, 8),
   (25, 5, 9),
   (29, 3, 11),
   (30, 5, 11),
   (31, 2, 12),
   (34, 3, 13),
   (35, 5, 13),
   (41, 2, 16),
   (44, 3, 17),
   (45, 5, 17),
   (49, 3, 19),
   (50, 5, 19),
   (55, 5, 21),
   (59, 3, 23),
   (60, 5, 23),
   (70, 5, 27),
   (75, 5, 29),
   (80, 5, 31),
   (85, 5, 33),
   (95, 5, 37),
   (100, 5, 39),
   (105, 5, 41)}

theorem finite_angle_table_12_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, 5, 2) →
      cornerAnglePair P Q R (1, 5, 2) ∈ finiteAngleTable12.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_12_valid :
    ∀ v ∈ finiteAngleTable12,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
