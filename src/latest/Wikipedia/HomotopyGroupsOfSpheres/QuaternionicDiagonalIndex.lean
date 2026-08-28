import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMixingMatrices

/-! # A uniform commutator estimate on the quaternionic diagonal mixing family -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator

variable {n : ℕ}

theorem diagonal_mixing_commutator_bound (α : Fin (n + 1) → ℝ)
    (hfast : 3 * Real.pi ≤ α 0) (hslow : ∀ a : Fin n, Real.pi ≤ α a.succ)
    (c : Fin n → ℝ) :
    16 * Real.pi ^ 2 * squareNorm (mixingSkewLinear n c).val ≤
      squareNorm (commutator (realAction n (Matrix.diagonal (fun a => α a • QuaternionicScalars.i)))
        (mixingSkewLinear n c).val) := by
  have hterm (a : Fin n) : 16 * Real.pi ^ 2 * c a ^ 2 ≤ ((α 0 + α a.succ) * c a) ^ 2 := by
    have hs : 4 * Real.pi ≤ α 0 + α a.succ := by linarith [hslow a]
    have hsq : (4 * Real.pi) ^ 2 ≤ (α 0 + α a.succ) ^ 2 :=
      (sq_le_sq₀ (by positivity) (by linarith [Real.pi_pos])).mpr hs
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg (c a))
    nlinarith only [hm]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a)
  rw [← Finset.mul_sum] at hsum
  rw [squareNorm_diagonal_commutator_mixing]
  change 16 * Real.pi ^ 2 * squareNorm (realAction n (mixingMatrix QuaternionicScalars.j c)) ≤ _
  rw [squareNorm_realAction_mixing QuaternionicScalars.j QuaternionicScalars.norm_j]
  linarith

theorem mixing_squareNorm_pos (c : Fin n → ℝ) (hc : c ≠ 0) :
    0 < squareNorm (mixingSkewLinear n c).val := by
  apply lt_of_le_of_ne (squareNorm_nonneg _)
  intro h
  have hz : mixingSkewLinear n c = 0 :=
    Subtype.ext ((squareNorm_eq_zero_iff _).mp h.symm)
  exact hc (mixingSkewLinear_injective n (hz.trans (mixingSkewLinear n).map_zero.symm))

/-- Every nonzero member satisfies the strict bound needed for a negative second variation. -/
theorem diagonal_mixing_commutator_strict (α : Fin (n + 1) → ℝ)
    (hfast : 3 * Real.pi ≤ α 0) (hslow : ∀ a : Fin n, Real.pi ≤ α a.succ)
    (c : Fin n → ℝ) (hc : c ≠ 0) :
    4 * Real.pi ^ 2 * squareNorm (mixingSkewLinear n c).val <
      squareNorm (commutator (realAction n (Matrix.diagonal (fun a => α a • QuaternionicScalars.i)))
        (mixingSkewLinear n c).val) := by
  have hb := diagonal_mixing_commutator_bound α hfast hslow c
  have hp := mul_pos (sq_pos_of_pos Real.pi_pos) (mixing_squareNorm_pos c hc)
  linarith

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
