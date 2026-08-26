import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, 7, 2). -/

namespace Erdos633b

def finiteAngleTable14 : Finset (ℕ × ℕ × ℕ) :=
  {(11, 1, 3),
   (18, 1, 5),
   (19, 3, 5),
   (26, 3, 7),
   (27, 5, 7),
   (29, 2, 8),
   (34, 5, 9),
   (35, 7, 9),
   (40, 3, 11),
   (41, 5, 11),
   (42, 7, 11),
   (47, 3, 13),
   (48, 5, 13),
   (49, 7, 13),
   (56, 7, 15),
   (62, 5, 17),
   (63, 7, 17),
   (69, 5, 19),
   (70, 7, 19),
   (76, 5, 21),
   (83, 5, 23),
   (84, 7, 23),
   (91, 7, 25),
   (98, 7, 27),
   (105, 7, 29),
   (112, 7, 31),
   (119, 7, 33)}

theorem finite_angle_table_14_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, 7, 2) →
      cornerAnglePair P Q R (1, 7, 2) ∈ finiteAngleTable14.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_14_valid :
    ∀ v ∈ finiteAngleTable14,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
