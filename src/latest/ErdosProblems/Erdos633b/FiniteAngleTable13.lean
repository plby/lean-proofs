import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, 6, 2). -/

namespace Erdos633b

def finiteAngleTable13 : Finset (ℕ × ℕ × ℕ) :=
  {(16, 2, 5),
   (19, 2, 6),
   (22, 2, 7),
   (23, 4, 7),
   (25, 2, 8),
   (28, 2, 9),
   (29, 4, 9),
   (31, 2, 10),
   (34, 2, 11),
   (35, 4, 11),
   (36, 6, 11),
   (37, 2, 12),
   (40, 2, 13),
   (41, 4, 13),
   (42, 6, 13),
   (47, 4, 15),
   (53, 4, 17),
   (54, 6, 17),
   (59, 4, 19),
   (60, 6, 19),
   (65, 4, 21),
   (71, 4, 23),
   (72, 6, 23),
   (77, 4, 25),
   (78, 6, 25),
   (83, 4, 27),
   (90, 6, 29),
   (96, 6, 31),
   (108, 6, 35),
   (114, 6, 37),
   (126, 6, 41)}

theorem finite_angle_table_13_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, 6, 2) →
      cornerAnglePair P Q R (1, 6, 2) ∈ finiteAngleTable13.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_13_valid :
    ∀ v ∈ finiteAngleTable13,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
