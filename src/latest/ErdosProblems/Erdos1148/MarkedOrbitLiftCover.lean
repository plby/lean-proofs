import ErdosProblems.Erdos1148.CompactStepRefinement
import ErdosProblems.Erdos1148.UniformOrdinaryRefinement
import ErdosProblems.Erdos1148.FiniteLiftCoverComposition

/-! # Covering marked orbit itineraries, branching only at exceptional steps -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups BigOperators

theorem marked_orbit_lift_cover {η : ℝ} {K₀ : Set ModularOrbitSpace}
    (hηpos : 0 < η) (hη : η ≤ 1 / 2)
    (hradius : ∀ g h : SL(2, ℝ), modularMk g ∈ K₀ →
      EntryCloseOne (η * Real.exp 1) (g⁻¹ * h) →
      (modularMk g, modularMk h) ∈ modularClosePairs η → EntryCloseOne η (g⁻¹ * h))
    (E : Set SL(2, ℝ)) (hstart : LiftForwardClose η 0 E)
    (bad : ℕ → Prop) [DecidablePred bad] (n : ℕ)
    (hgood : ∀ k < n, ¬bad (k + 1) →
      (∀ g ∈ E, modularMk (g * diagonalFlow ((k + 1 : ℕ) : ℝ)) ∈ K₀) ∧
      (∀ g ∈ E, ∀ h ∈ E,
        (modularMk (g * diagonalFlow ((k + 1 : ℕ) : ℝ)),
          modularMk (h * diagonalFlow ((k + 1 : ℕ) : ℝ))) ∈ modularClosePairs η)) :
    LiftCoverBound η (n : ℝ) E
      ((33 ^ 3 * Real.exp 1) ^ ((Finset.range n).filter (fun k => bad (k + 1))).card) := by
  let K : ℝ := 33 ^ 3 * Real.exp 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let cost : ℕ → ℝ := fun k => if bad (k + 1) then K else 1
  have hcost (k : ℕ) : 0 ≤ cost k := by dsimp [cost]; split_ifs <;> positivity
  have hstart' : LiftCoverBound η ((0 : ℕ) : ℝ) E 1 := by
    simpa only [Nat.cast_zero] using hstart.coverBound
  have hcover := LiftCoverBound.iterate_upto (η := η) (M := 1) (E := E)
    (fun k : ℕ => (k : ℝ)) cost hcost hstart' n
  have hstep : ∀ k < n, ∀ F ⊆ E, LiftForwardClose η (k : ℝ) F →
      LiftCoverBound η ((k + 1 : ℕ) : ℝ) F (cost k) := by
    intro k hk F hFE hF
    by_cases hb : bad (k + 1)
    · obtain ⟨N, C, hN, hC, hclose⟩ := exists_uniform_ordinary_lift_refinement hηpos hη
        (Nat.cast_nonneg k) (by norm_num : (0 : ℝ) ≤ 1) F hF
      refine ⟨N, C, ?_, hC, ?_⟩
      · simpa only [cost, if_pos hb, K] using hN
      · simpa only [Nat.cast_add, Nat.cast_one] using hclose
    · obtain ⟨hcore, hpairs⟩ := hgood k hk hb
      have hclose := hF.extend_over_compact_atom (Nat.cast_nonneg k) hradius
        (fun g hg => by simpa only [Nat.cast_add, Nat.cast_one] using hcore g (hFE hg))
        (fun g hg h hh => by
          simpa only [Nat.cast_add, Nat.cast_one] using hpairs g (hFE hg) h (hFE hh))
      simpa only [cost, if_neg hb, Nat.cast_add, Nat.cast_one] using hclose.coverBound
  have h := hcover hstep
  have hprod : (∏ k ∈ Finset.range n, cost k) =
      K ^ ((Finset.range n).filter (fun k => bad (k + 1))).card := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const]
  simpa only [one_mul, hprod, K] using h

end Erdos1148.DukeArithmetic
