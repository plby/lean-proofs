import ErdosProblems.Erdos1148.MarkedAvoidanceBlocks
import ErdosProblems.Erdos1148.AvoidanceBlockCost
import ErdosProblems.Erdos1148.OrbitAvoidanceShift

/-! # A coherent cover for a fixed avoidance-block itinerary -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups BigOperators

def modularAvoidanceBlockPattern (K U : Set ModularOrbitSpace) (n k : ℕ) (p : Finset ℕ) :
    Set ModularOrbitSpace :=
  finiteOrbitAvoidance modularTimeOne U (k * n) ∩
    {x | ∀ j < k, (modularTimeOne^[j * n] x ∉ K ↔ j ∈ p)}

theorem fixed_avoidance_pattern_lift_cover {η a : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (ha : 0 ≤ a) (haone : a ≤ 1)
    (haC : a * (33 : ℝ) ^ 3 ≤ 1 / 4) (n : ℕ) (K U : Set ModularOrbitSpace)
    (hrefine : ∀ S : ℝ, 0 ≤ S → ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ K) →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ finiteOrbitAvoidance modularTimeOne U n) →
      LiftCoverBound η (S + n) E (a ^ 2 * Real.exp n))
    (E : Set SL(2, ℝ)) (hE : LiftForwardClose η 0 E)
    (k : ℕ) (p : Finset ℕ) (hp : p ⊆ Finset.range k) (hhalf : 2 * p.card ≤ k) :
    LiftCoverBound η ((k : ℝ) * n) (E ∩ modularMk ⁻¹' modularAvoidanceBlockPattern K U n k p)
      ((Real.exp n / 4) ^ k) := by
  classical
  let F := E ∩ modularMk ⁻¹' modularAvoidanceBlockPattern K U n k p
  have hgood : ∀ j < k, j ∉ p → ∀ g ∈ F,
      modularMk (g * diagonalFlow ((j : ℝ) * n)) ∈ K ∩
        finiteOrbitAvoidance modularTimeOne U n := by
    intro j hj hjp g hg
    have hpattern : modularMk g ∈ modularAvoidanceBlockPattern K U n k p := hg.2
    have heq : modularMk (g * diagonalFlow ((j : ℝ) * n)) =
        modularTimeOne^[j * n] (modularMk g) := by
      rw [modularTimeOne_iterate_mk, Nat.cast_mul]
    rw [heq]
    refine ⟨?_, finiteOrbitAvoidance_shift_block hj hpattern.1⟩
    by_contra hnot
    exact hjp ((hpattern.2 j hj).mp hnot)
  have h := marked_avoidance_block_lift_cover hη hηsmall (sq_nonneg a) n K U hrefine F
    (hE.mono Set.inter_subset_left) (fun j => j ∈ p) k hgood
  apply h.mono_bound
  have hfilter : (Finset.range k).filter (fun j => j ∈ p) = p := by
    ext j
    exact ⟨fun hj => (Finset.mem_filter.mp hj).2, fun hj => Finset.mem_filter.mpr ⟨hp hj, hj⟩⟩
  have hc := avoidance_block_product_bound (Finset.range k) (fun j => j ∈ p)
    ha haone (by norm_num : (1 : ℝ) ≤ 33 ^ 3) haC (Real.exp_pos (n : ℝ)).le
    (by simpa only [hfilter, Finset.card_range] using hhalf)
  simpa only [Finset.card_range] using hc

end Erdos1148.DukeArithmetic
