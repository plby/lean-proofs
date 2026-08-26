import ErdosProblems.Erdos1148.AvoidanceBlockRefinement
import ErdosProblems.Erdos1148.UniformOrdinaryRefinement

/-! # Iterating inexpensive avoidance blocks and ordinary exceptional blocks -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups BigOperators

theorem marked_avoidance_block_lift_cover {η q : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 2)
    (hq : 0 ≤ q) (n : ℕ) (K U : Set ModularOrbitSpace)
    (hrefine : ∀ S : ℝ, 0 ≤ S → ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ K) →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ finiteOrbitAvoidance modularTimeOne U n) →
      LiftCoverBound η (S + n) E (q * Real.exp n))
    (E : Set SL(2, ℝ)) (hstart : LiftForwardClose η 0 E)
    (bad : ℕ → Prop) [DecidablePred bad] (k : ℕ)
    (hgood : ∀ j < k, ¬bad j → ∀ g ∈ E,
      modularMk (g * diagonalFlow ((j : ℝ) * n)) ∈ K ∩
        finiteOrbitAvoidance modularTimeOne U n) :
    LiftCoverBound η ((k : ℝ) * n) E
      (∏ j ∈ Finset.range k, if bad j then (33 : ℝ) ^ 3 * Real.exp n else q * Real.exp n) := by
  let cost : ℕ → ℝ := fun j => if bad j then (33 : ℝ) ^ 3 * Real.exp n else q * Real.exp n
  have hcost (j : ℕ) : 0 ≤ cost j := by dsimp [cost]; split_ifs <;> positivity
  have hstart' : LiftCoverBound η ((0 : ℕ) * (n : ℝ)) E 1 := by
    simpa only [Nat.cast_zero, zero_mul] using hstart.coverBound
  have hcover := LiftCoverBound.iterate_upto (η := η) (M := 1) (E := E)
    (fun j : ℕ => (j : ℝ) * n) cost hcost hstart' k
  have hstep : ∀ j < k, ∀ F ⊆ E, LiftForwardClose η ((j : ℝ) * n) F →
      LiftCoverBound η (((j + 1 : ℕ) : ℝ) * n) F (cost j) := by
    intro j hj F hFE hF
    by_cases hb : bad j
    · obtain ⟨N, C, hN, hC, hclose⟩ := exists_uniform_ordinary_lift_refinement hη hηsmall
        (mul_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg n)) (Nat.cast_nonneg n) F hF
      refine ⟨N, C, ?_, hC, ?_⟩
      · simpa only [cost, if_pos hb] using hN
      · simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hclose
    · have h := hrefine ((j : ℝ) * n) (by positivity) F hF
        (fun g hg => (hgood j hj hb g (hFE hg)).1)
        (fun g hg => (hgood j hj hb g (hFE hg)).2)
      simpa only [cost, if_neg hb, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h
  simpa only [one_mul] using hcover hstep

end Erdos1148.DukeArithmetic
