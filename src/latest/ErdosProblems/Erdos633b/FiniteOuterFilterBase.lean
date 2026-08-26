import ErdosProblems.Erdos633b.ActualFiniteAngleCandidates
import ErdosProblems.Erdos633b.RationalPositiveSineParity

/-! Finite integer tests necessary for a sorted outer-angle pair. -/

namespace Erdos633b

def finiteCornerReachable (v : ℕ × ℕ × ℕ) (a : ℕ) : Prop :=
  ∃ q : Fin 6, ∃ r : Fin 2,
    q.val * v.2.2 + r.val * (v.1 - v.2.1 - v.2.2) ≤ a ∧
    (a - (q.val * v.2.2 + r.val * (v.1 - v.2.1 - v.2.2))) % v.2.1 = 0

instance (v : ℕ × ℕ × ℕ) (a : ℕ) : Decidable (finiteCornerReachable v a) := by
  unfold finiteCornerReachable
  infer_instance

def finiteOuterIntegerTests (v : ℕ × ℕ × ℕ) (a b : ℕ) : Prop :=
  ∀ k : Fin v.1, k.val.Coprime (2 * v.1) →
    angleResidueSum v.1 k.val (angleTableWeights v) =
      angleResidueSum v.1 k.val (angleTableWeights (v.1, a, b)) ∧
    ((∀ i, Even (k.val * angleTableWeights v i / v.1)) →
      ∀ i, Even (k.val * angleTableWeights (v.1, a, b) i / v.1))

instance (v : ℕ × ℕ × ℕ) (a b : ℕ) : Decidable (finiteOuterIntegerTests v a b) := by
  unfold finiteOuterIntegerTests
  infer_instance

def FiniteOuterAdmissible (v : ℕ × ℕ × ℕ) (a b : ℕ) : Prop :=
  0 < a ∧ a < b ∧ a + 2 * b < v.1 ∧ (a, b) ≠ (v.2.1, v.2.2) ∧
    (∀ i : Fin 3, finiteCornerReachable v (angleTableWeights (v.1, a, b) i)) ∧
    finiteOuterIntegerTests v a b

instance (v : ℕ × ℕ × ℕ) (a b : ℕ) : Decidable (FiniteOuterAdmissible v a b) := by
  unfold FiniteOuterAdmissible
  infer_instance

namespace Tiling

theorem integer_corner_row_eq {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 0 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ j, d.tile.angle j = (w j : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N)) (i : Fin 3) :
    ∑ j, d.cornerAngleCount i j * w j = a i := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : Real.pi / N ≠ 0 := (div_pos Real.pi_pos hN').ne'
  have he : ((∑ j, d.cornerAngleCount i j * w j : ℕ) : ℝ) = (a i : ℝ) := by
    apply mul_right_cancel₀ hδ
    rw [Nat.cast_sum, Finset.sum_mul, ← ha i, d.angle_eq_sum_counts i]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.cast_mul, hw j]
    ring
  exact_mod_cast he

theorem finite_corner_reachable_of_row {T : Triangle} {n : ℕ} (d : Tiling T n)
    (v : ℕ × ℕ × ℕ) (a : ℕ) (i : Fin 3)
    (hQ : d.cornerColumnCount 1 ≤ 5) (hR : d.cornerColumnCount 2 ≤ 1)
    (he : ∑ j, d.cornerAngleCount i j * angleTableWeights v j = a) :
    finiteCornerReachable v a := by
  have hq := (d.corner_count_le_column i 1).trans hQ
  have hr := (d.corner_count_le_column i 2).trans hR
  refine ⟨⟨d.cornerAngleCount i 1, by omega⟩, ⟨d.cornerAngleCount i 2, by omega⟩, ?_, ?_⟩
  all_goals
    simp only [Fin.sum_univ_three, angleTableWeights, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] at he
  · dsimp only
    omega
  · dsimp only
    have hs : a - (d.cornerAngleCount i 1 * v.2.2 +
        d.cornerAngleCount i 2 * (v.1 - v.2.1 - v.2.2)) =
        d.cornerAngleCount i 0 * v.2.1 := by omega
    rw [hs]
    exact Nat.mul_mod_left _ _

end Tiling
end Erdos633b
