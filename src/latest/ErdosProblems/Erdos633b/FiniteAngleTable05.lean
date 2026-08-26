import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 7, 2). -/

namespace Erdos633b

def finiteAngleTable05 : Finset (ℕ × ℕ × ℕ) :=
  {(7, 1, 2),
   (14, 1, 4),
   (21, 1, 6),
   (21, 2, 6),
   (28, 3, 8),
   (28, 5, 8),
   (35, 2, 10),
   (35, 3, 10),
   (35, 7, 10),
   (42, 5, 12),
   (42, 7, 12),
   (49, 3, 14),
   (49, 5, 14),
   (56, 3, 16),
   (56, 5, 16),
   (56, 7, 16),
   (63, 5, 18),
   (63, 7, 18),
   (70, 7, 20),
   (77, 5, 22),
   (77, 7, 22),
   (84, 5, 24),
   (84, 7, 24),
   (91, 5, 26),
   (91, 7, 26),
   (98, 5, 28),
   (105, 7, 30),
   (112, 7, 32),
   (119, 7, 34),
   (126, 7, 36),
   (133, 7, 38),
   (140, 7, 40)}

theorem finite_angle_table_05_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 7, 2) →
      cornerAnglePair P Q R (0, 7, 2) ∈ finiteAngleTable05.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_05_valid :
    ∀ v ∈ finiteAngleTable05,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
