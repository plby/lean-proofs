import ErdosProblems.Erdos1148.FixedAvoidancePatternCover
import ErdosProblems.Erdos1148.GoodAvoidanceBlocks
import ErdosProblems.Erdos1148.FiniteLiftCoverUnion

/-! # Summing inexpensive itinerary covers over all admissible block patterns -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem good_avoidance_blocks_lift_cover {η a : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 2) (ha : 0 ≤ a) (haone : a ≤ 1)
    (haC : a * (33 : ℝ) ^ 3 ≤ 1 / 4) (n : ℕ) (K U : Set ModularOrbitSpace)
    (hrefine : ∀ S : ℝ, 0 ≤ S → ∀ E : Set SL(2, ℝ), LiftForwardClose η S E →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ K) →
      (∀ g ∈ E, modularMk (g * diagonalFlow S) ∈ finiteOrbitAvoidance modularTimeOne U n) →
      LiftCoverBound η (S + n) E (a ^ 2 * Real.exp n))
    (E : Set SL(2, ℝ)) (hE : LiftForwardClose η 0 E) (k : ℕ) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ (Real.exp n / 2) ^ k ∧
      E ∩ modularMk ⁻¹' goodAvoidanceBlocks K U n k ⊆ ⋃ i, B i ∧
      ∀ i, LiftForwardClose η ((k : ℝ) * n) (B i) := by
  classical
  let P := halfBadPatterns k
  let F : P → Set SL(2, ℝ) := fun p => E ∩ modularMk ⁻¹' modularAvoidanceBlockPattern K U n k p.val
  have hF (p : P) : LiftCoverBound η ((k : ℝ) * n) (F p) ((Real.exp n / 4) ^ k) := by
    have hp := (mem_halfBadPatterns k p.val).mp p.property
    exact fixed_avoidance_pattern_lift_cover hη hηsmall ha haone haC n K U hrefine E hE k p hp.1 hp.2
  have hUnion := LiftCoverBound.iUnion F hF
  have hcard : (Fintype.card P : ℝ) ≤ (2 : ℝ) ^ k := by
    have hreal : ((halfBadPatterns k).card : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast halfBadPatterns_card_le k
    simpa only [Fintype.card_coe, P] using hreal
  have hbound : (Fintype.card P : ℝ) * (Real.exp n / 4) ^ k ≤ (Real.exp n / 2) ^ k := by
    calc
      _ ≤ (2 : ℝ) ^ k * (Real.exp n / 4) ^ k := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := avoidance_pattern_factor k (Real.exp n)
  obtain ⟨N, B, hN, hcov, hclose⟩ := hUnion.mono_bound hbound
  refine ⟨N, B, hN, ?_, hclose⟩
  rintro g ⟨hgE, hg⟩
  let p := orbitBlockPattern modularTimeOne Kᶜ n k (modularMk g)
  have hp : p ∈ P := (mem_halfBadPatterns k p).mpr
    ⟨orbitBlockPattern_subset_range _ _ _ _ _, hg.2⟩
  rw [hcov]
  refine Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hgE, hg.1, ?_⟩
  intro j hj
  constructor
  · intro hbad
    exact (mem_orbitBlockPattern modularTimeOne Kᶜ n k (modularMk g) j).mpr ⟨hj, hbad⟩
  · intro hmem
    exact ((mem_orbitBlockPattern modularTimeOne Kᶜ n k (modularMk g) j).mp hmem).2

end Erdos1148.DukeArithmetic
