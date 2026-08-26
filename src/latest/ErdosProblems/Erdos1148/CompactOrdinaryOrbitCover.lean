import ErdosProblems.Erdos1148.CompactInitialLiftCover
import ErdosProblems.Erdos1148.CompactCoherentCover
import ErdosProblems.Erdos1148.UniformOrdinaryRefinement
import ErdosProblems.Erdos1148.FiniteLiftCoverUnion

/-! # Ordinary forward orbit covers over a compact starting set -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_compact_ordinary_orbit_cover {K : Set ModularOrbitSpace} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ T : ℝ, 0 ≤ T → ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ M * Real.exp T ∧ K ⊆ ⋃ i, modularMk '' B i ∧
      (∀ i, IsCompact (B i)) ∧ ∀ i, LiftForwardClose η T (B i) := by
  obtain ⟨N₀, E, hcover, hclose⟩ := exists_compact_initial_lift_cover hK hη
  let M := (N₀ : ℝ) * (33 ^ 3 * 33 ^ 3) + 1
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro T hT
  have hE (i : Fin N₀) : LiftCoverBound η T (E i) (33 ^ 3 * Real.exp T) := by
    obtain ⟨N, C, hN, hC, hB⟩ := exists_uniform_ordinary_lift_refinement hη hηsmall
      (le_refl 0) hT (E i) (hclose i)
    exact ⟨N, C, hN, hC, by simpa only [zero_add] using hB⟩
  have hUnion := LiftCoverBound.iUnion E hE
  obtain ⟨N, B, hN, hcov, hB, hcloseB⟩ := hUnion.exists_compact_cover hη hηsmall hT
  refine ⟨N, B, ?_, ?_, hB, hcloseB⟩
  · simp only [Fintype.card_fin] at hN
    calc
      (N : ℝ) ≤ ((N₀ : ℝ) * (33 ^ 3 * Real.exp T)) * 33 ^ 3 := hN
      _ ≤ M * Real.exp T := by dsimp only [M]; nlinarith only [Real.exp_pos T]
  · intro x hx
    obtain ⟨i, g, hg, rfl⟩ := Set.mem_iUnion.mp (hcover hx)
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_iUnion.mpr ⟨i, hg⟩))
    exact Set.mem_iUnion.mpr ⟨j, g, hj, rfl⟩

end Erdos1148.DukeArithmetic
