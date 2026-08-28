import Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing
import Wikipedia.HomotopyGroupsOfSpheres.RealMatrixSquareNorm

/-! # The actual diagonal commutator bound on symmetric trace-zero mixing directions -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing

open RealMatrixSquareNorm

variable {N : Type*} [Fintype N] [DecidableEq N] {r : ℕ}

private theorem scalar_gap_bound (x y : ℝ) (hx : 4 * Real.pi ≤ |x|) :
    16 * Real.pi ^ 2 * y ^ 2 ≤ (x * y) ^ 2 := by
  have hsq : (4 * Real.pi) ^ 2 ≤ x ^ 2 := by
    have h := (sq_le_sq₀ (by positivity : 0 ≤ 4 * Real.pi) (abs_nonneg x)).mpr hx
    simpa only [sq_abs] using h
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg y)
  nlinarith only [hm]

theorem mixing_commutator_bound (b : N) (e : Fin r ↪ N) (α : N → ℝ)
    (hgap : ∀ j, 4 * Real.pi ≤ |α b - α (e j)|) (c : Fin r → ℝ) :
    16 * Real.pi ^ 2 * squareNorm (mixingLinear b e c) ≤
      squareNorm (commutator (Matrix.diagonal α) (mixingLinear b e c)) := by
  have hsep (i j : N) (hij : mixingLinear b e c i j ≠ 0) :
      4 * Real.pi ≤ |α i - α j| := by
    obtain ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := mixingLinear_support b e c i j hij
    · exact hgap k
    · simpa only [abs_sub_comm] using hgap k
  have hentry (i j : N) :
      16 * Real.pi ^ 2 * (mixingLinear b e c i j) ^ 2 ≤
        (commutator (Matrix.diagonal α) (mixingLinear b e c) i j) ^ 2 := by
    rw [diagonal_commutator_apply]
    by_cases hij : mixingLinear b e c i j = 0
    · simp only [hij, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    · exact scalar_gap_bound _ _ (hsep i j hij)
  simp only [squareNorm, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hentry i j))

theorem mixing_squareNorm_pos (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j)
    (c : Fin r → ℝ) (hc : c ≠ 0) : 0 < squareNorm (mixingLinear b e c) := by
  apply squareNorm_pos
  intro h
  exact hc (mixingLinear_injective b e he (h.trans (mixingLinear b e).map_zero.symm))

theorem mixing_commutator_strict (b : N) (e : Fin r ↪ N) (he : ∀ j, b ≠ e j)
    (α : N → ℝ) (hgap : ∀ j, 4 * Real.pi ≤ |α b - α (e j)|)
    (c : Fin r → ℝ) (hc : c ≠ 0) :
    4 * Real.pi ^ 2 * squareNorm (mixingLinear b e c) <
      squareNorm (commutator (Matrix.diagonal α) (mixingLinear b e c)) := by
  have hb := mixing_commutator_bound b e α hgap c
  have hp := mul_pos (sq_pos_of_pos Real.pi_pos) (mixing_squareNorm_pos b e he c hc)
  linarith

end Wikipedia.HomotopyGroupsOfSpheres.RealSymmetricMixing
