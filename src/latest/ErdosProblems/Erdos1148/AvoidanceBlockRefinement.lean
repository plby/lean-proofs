import ErdosProblems.Erdos1148.FixedRadiusAvoidanceCover
import ErdosProblems.Erdos1148.CompactImageLiftRefinement
import ErdosProblems.Erdos1148.FiniteLiftCoverComposition

/-! # A compact-start avoidance block has arbitrarily small refinement prefactor -/

namespace Erdos1148.DukeArithmetic

open Filter
open scoped MatrixGroups

theorem exists_avoidance_block_refinement {K U : Set ModularOrbitSpace}
    (hK : IsCompact K) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 192 ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ q : ℝ, 0 < q → ∀ᶠ n : ℕ in atTop, ∀ S : ℝ, 0 ≤ S →
        ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
          (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ K) →
          (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ finiteOrbitAvoidance modularTimeOne U n) →
          LiftCoverBound η (S + n) E (q * Real.exp n) := by
  obtain ⟨η₀, hη₀, hηsmall, hinj⟩ := exists_compact_modular_injective_radius hK
  refine ⟨η₀, hη₀, hηsmall, ?_⟩
  intro η hη hηle q hq
  have hevent := exists_small_compact_avoidance_cover_at_radius hK hU hne hη hq
  filter_upwards [hevent] with n hn
  obtain ⟨N, B, hN, hcov, _, hB⟩ := hn
  intro S hS E hE hEK hEU
  obtain ⟨C, hC, hclose⟩ := exists_compact_image_lift_refinement hS (Nat.cast_nonneg n)
    (hinj η hη.le hηle) hE hEK B hB
    (fun g hg => hcov ⟨hEK g hg, hEU g hg⟩)
  exact ⟨N, C, hN, hC, hclose⟩

end Erdos1148.DukeArithmetic
