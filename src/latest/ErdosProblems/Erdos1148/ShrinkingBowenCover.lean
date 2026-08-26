import ErdosProblems.Erdos1148.GaussParameterGridCover
import ErdosProblems.Erdos1148.NearbyGaussParameters
import ErdosProblems.Erdos1148.LiftForwardClose

/-! # Shrinking the radius of a Bowen cover costs a time-independent factor -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_shrunk_lift_cover {η δ S : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (hδ : 0 < δ) (hS : 0 ≤ S)
    (E : Set SL(2, ℝ)) (hE : LiftForwardClose η S E) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ (32 * η / δ + 1) ^ 3 ∧ (∀ i, IsCompact (B i)) ∧
      E ⊆ ⋃ i, B i ∧ ∀ i, LiftForwardClose δ S (B i) := by
  by_cases hne : E.Nonempty
  · obtain ⟨g₀, hg₀⟩ := hne
    let d := δ / 8
    have hd : 0 < d := by dsimp [d]; positivity
    let R : Set BoundedGaussParameters := {p | |p.val.1| ≤ 2 * η * Real.exp (-S) ∧
      |p.val.2.1| ≤ 2 * η ∧ |p.val.2.2 - 1| ≤ η}
    have hER : E ⊆ gaussParameterFrame g₀ '' R := by
      intro g hg
      have htube : EntryForwardBowenTube η (η * Real.exp (-S)) (g₀⁻¹ * g) := by
        apply (entryForwardBowenTube_iff_flow_closeness hS _).mpr
        intro t ht
        have heq : diagonalFlow (-t) * (g₀⁻¹ * g) * diagonalFlow t =
            (g₀ * diagonalFlow t)⁻¹ * (g * diagonalFlow t) := by rw [diagonalFlow_neg]; group
        rw [heq]
        exact hE g₀ hg₀ g hg t ht
      obtain ⟨p, hp, hr, hx, hh⟩ := exists_boundedGaussParameters_of_forward_tube hηsmall g₀ g htube
      exact ⟨p, ⟨by simpa only [mul_assoc] using hr, hx, hh⟩, hp⟩
    obtain ⟨Nr, a, hNr, _, hrcov⟩ := exists_real_interval_grid
      (a := -(2 * η * Real.exp (-S))) (b := 2 * η * Real.exp (-S))
      (by linarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hη) (Real.exp_pos (-S))])
      (mul_pos hd (Real.exp_pos _))
    obtain ⟨Nx, b, hNx, _, hxcov⟩ := exists_real_interval_grid
      (a := -(2 * η)) (b := 2 * η) (by linarith) hd
    obtain ⟨Nh, c, hNh, _, hhcov⟩ := exists_real_interval_grid
      (a := 1 - η) (b := 1 + η) (by linarith) hd
    have hNr' : (Nr : ℝ) ≤ 32 * η / δ + 1 := by
      have heq : (2 * η * Real.exp (-S) - -(2 * η * Real.exp (-S))) /
          (d * Real.exp (-S)) + 1 = 32 * η / δ + 1 := by
        dsimp only [d]
        field_simp [hδ.ne', Real.exp_ne_zero]
        <;> ring
      exact hNr.trans_eq heq
    have hNx' : (Nx : ℝ) ≤ 32 * η / δ + 1 := by
      have heq : (2 * η - -(2 * η)) / d + 1 = 32 * η / δ + 1 := by
        dsimp only [d]
        field_simp [hδ.ne']
        <;> ring
      exact hNx.trans_eq heq
    have hNh' : (Nh : ℝ) ≤ 32 * η / δ + 1 := by
      have heq : (1 + η - (1 - η)) / d + 1 = 16 * η / δ + 1 := by
        dsimp only [d]
        field_simp [hδ.ne']
        <;> ring
      have hbound := hNh.trans_eq heq
      exact hbound.trans (add_le_add
        (div_le_div_of_nonneg_right (by linarith only [hη] : 16 * η ≤ 32 * η) hδ.le) le_rfl)
    obtain ⟨N, B, hN, hB, hcov, hclose⟩ := exists_gauss_lift_cover_of_parameter_grids hd.le hS g₀ R
      a b c (fun p hp => hrcov _ (abs_le.mp hp.1)) (fun p hp => hxcov _ (abs_le.mp hp.2.1))
      (fun p hp => hhcov _ (by
        have h := abs_le.mp hp.2.2
        constructor <;> linarith only [h.1, h.2]))
    refine ⟨N, B, ?_, hB, hER.trans hcov, ?_⟩
    · rw [hN, Nat.cast_mul, Nat.cast_mul]
      have hL : 0 ≤ 32 * η / δ + 1 := by positivity
      have hprod := mul_le_mul
        (mul_le_mul hNr' hNx' (Nat.cast_nonneg _) hL) hNh' (Nat.cast_nonneg _) (mul_nonneg hL hL)
      exact hprod.trans_eq (by ring)
    · simpa only [show 8 * d = δ by dsimp [d]; ring] using hclose
  · refine ⟨0, Fin.elim0, ?_, ?_, ?_, ?_⟩
    · simp only [Nat.cast_zero]
      positivity
    · intro i
      exact Fin.elim0 i
    · simp only [Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_subset]
    · intro i
      exact Fin.elim0 i

end Erdos1148.DukeArithmetic
