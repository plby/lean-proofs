import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (1, -3, -1). -/

namespace Erdos633b

def finiteAngleTable11 : Finset (ℕ × ℕ × ℕ) :=
  {(11, 1, 4),
   (13, 2, 5),
   (14, 1, 5),
   (17, 1, 6),
   (18, 3, 7),
   (19, 2, 7),
   (20, 1, 7),
   (21, 3, 8),
   (25, 2, 9),
   (27, 3, 10),
   (30, 3, 11),
   (31, 2, 11),
   (36, 3, 13),
   (37, 2, 13),
   (39, 3, 14),
   (45, 3, 16),
   (48, 3, 17),
   (54, 3, 19),
   (57, 3, 20),
   (63, 3, 22)}

theorem finite_angle_table_11_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (1, -3, -1) →
      cornerAnglePair P Q R (1, -3, -1) ∈ finiteAngleTable11.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_11_valid :
    ∀ v ∈ finiteAngleTable11,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
