import ErdosProblems.Erdos1148.SmallAvoidanceCover
import ErdosProblems.Erdos1148.FiniteShrinkingBowenCover

/-! # Small-prefactor avoidance covers at any prescribed positive radius -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped MatrixGroups

theorem exists_small_compact_avoidance_cover_at_radius {K U : Set ModularOrbitSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hne : U.Nonempty) {δ : ℝ} (hδ : 0 < δ)
    {q : ℝ} (hq : 0 < q) : ∀ᶠ n : ℕ in atTop,
      ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
        (N : ℝ) ≤ q * Real.exp n ∧
        K ∩ finiteOrbitAvoidance modularTimeOne U n ⊆ ⋃ i, modularMk '' B i ∧
        (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose δ n (B i) := by
  obtain ⟨r, hr, hrsmall, hcover⟩ := exists_small_compact_avoidance_cover hK hU hne
  let C := (32 * r / δ + 1) ^ 3
  have hC : 0 < C := by dsimp only [C]; positivity
  have hevent := hcover (q / C) (div_pos hq hC)
  filter_upwards [hevent] with n hn
  obtain ⟨N, B, hN, hcov, _, hB⟩ := hn
  obtain ⟨M, D, hM, hD, hBD, hclose⟩ := exists_shrunk_finite_lift_cover hr
    (by linarith) hδ (Nat.cast_nonneg n) B hB
  refine ⟨M, D, ?_, ?_, hD, hclose⟩
  · change (M : ℝ) ≤ (N : ℝ) * C at hM
    calc
      (M : ℝ) ≤ (N : ℝ) * C := hM
      _ ≤ (q / C * Real.exp n) * C := mul_le_mul_of_nonneg_right hN hC.le
      _ = q * Real.exp n := by field_simp [hC.ne']
  · intro x hx
    obtain ⟨i, g, hg, rfl⟩ := Set.mem_iUnion.mp (hcov hx)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hBD (Set.mem_iUnion.mpr ⟨i, hg⟩))
    exact Set.mem_iUnion.mpr ⟨j, g, hj, rfl⟩

end Erdos1148.DukeArithmetic
