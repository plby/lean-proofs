import ErdosProblems.Erdos633b.FiniteAngleTableBase

/-! Kernel-checked rational intersections for local relation (0, 5, 2). -/

namespace Erdos633b

def finiteAngleTable04 : Finset (ℕ × ℕ × ℕ) :=
  {(15, 1, 6),
   (15, 2, 6),
   (20, 1, 8),
   (20, 3, 8),
   (25, 2, 10),
   (25, 3, 10),
   (30, 5, 12),
   (35, 2, 14),
   (35, 3, 14),
   (35, 5, 14),
   (40, 3, 16),
   (40, 5, 16),
   (45, 5, 18),
   (50, 3, 20),
   (55, 3, 22),
   (55, 5, 22),
   (60, 5, 24),
   (65, 5, 26),
   (70, 5, 28),
   (80, 5, 32),
   (85, 5, 34),
   (90, 5, 36),
   (95, 5, 38),
   (105, 5, 42)}

theorem finite_angle_table_04_exhaustive :
    ∀ (P : Fin 22) (Q : Fin 6) (R : Fin 2),
      AdmissibleCornerData P Q R (0, 5, 2) →
      cornerAnglePair P Q R (0, 5, 2) ∈ finiteAngleTable04.image angleTablePair := by
  decide +kernel

theorem finite_angle_table_04_valid :
    ∀ v ∈ finiteAngleTable04,
      3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
      v.2.1 + 2 * v.2.2 < v.1 := by
  decide

end Erdos633b
