import ErdosProblems.Erdos1148.GoodAvoidanceLiftCover
import ErdosProblems.Erdos1148.CompactInitialLiftCover
import ErdosProblems.Erdos1148.CompactCoherentCover

/-! # A strict exponential cover saving on trajectories with few exceptional blocks -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped MatrixGroups

theorem exists_good_avoidance_block_cover {K U : Set ModularOrbitSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 192 ∧ ∃ n : ℕ, 0 < n ∧
      ∀ K' : Set ModularOrbitSpace, IsCompact K' → ∃ M : ℝ, 0 < M ∧ ∀ k : ℕ,
        ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
          (N : ℝ) ≤ M * (Real.exp n / 2) ^ k ∧
          K' ∩ goodAvoidanceBlocks K U n k ⊆ ⋃ i, modularMk '' B i ∧
          (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose η ((k : ℝ) * n) (B i) := by
  obtain ⟨η, hη, hηsmall, hrefine⟩ := exists_avoidance_block_refinement hK hU hne
  obtain ⟨a, ha, haone, haC⟩ := exists_avoidance_block_cost_parameter
    (by norm_num : (1 : ℝ) ≤ 33 ^ 3)
  have hevent := hrefine η hη le_rfl (a ^ 2) (sq_pos_of_pos ha)
  obtain ⟨n, hnref, hn⟩ := (hevent.and (eventually_gt_atTop (0 : ℕ))).exists
  refine ⟨η, hη, hηsmall, n, hn, ?_⟩
  intro K' hK'
  obtain ⟨N₀, E, hEcover, hEclose⟩ := exists_compact_initial_lift_cover hK' hη
  let M := (N₀ : ℝ) * 33 ^ 3 + 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro k
  let F : Fin N₀ → Set SL(2, ℝ) := fun i => E i ∩ modularMk ⁻¹' goodAvoidanceBlocks K U n k
  have hF (i : Fin N₀) : LiftCoverBound η ((k : ℝ) * n) (F i) ((Real.exp n / 2) ^ k) := by
    obtain ⟨L, B, hL, hcov, hclose⟩ := good_avoidance_blocks_lift_cover hη (by linarith)
      ha.le haone haC n K U hnref (E i) (hEclose i) k
    exact LiftCoverBound.of_cover B hL hcov hclose
  have hUnion := LiftCoverBound.iUnion F hF
  obtain ⟨N, B, hN, hcov, hB, hclose⟩ := hUnion.exists_compact_cover hη
    (by linarith) (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n))
  refine ⟨N, B, ?_, ?_, hB, hclose⟩
  · simp only [Fintype.card_fin] at hN
    have hbase : 0 ≤ (Real.exp (n : ℝ) / 2) ^ k := by positivity
    calc
      (N : ℝ) ≤ ((N₀ : ℝ) * (Real.exp n / 2) ^ k) * 33 ^ 3 := hN
      _ ≤ M * (Real.exp n / 2) ^ k := by dsimp only [M]; nlinarith only [hbase]
  · rintro x ⟨hxK, hxGood⟩
    obtain ⟨i, g, hg, rfl⟩ := Set.mem_iUnion.mp (hEcover hxK)
    have hgF : g ∈ ⋃ j, F j := Set.mem_iUnion.mpr ⟨i, hg, hxGood⟩
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov hgF)
    exact Set.mem_iUnion.mpr ⟨j, g, hj, rfl⟩

end Erdos1148.DukeArithmetic
