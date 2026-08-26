import ErdosProblems.Erdos117.PrimeCoverBound
import ErdosProblems.Erdos117.DirectProducts

/-!
# Assembling the actual Sylow covers

For a finite class-two group, the factor clique bounds are chosen at their
actual attained values. Abelian Sylow factors contribute no logarithmic
cost. Every central-series length is controlled by the order of the ambient
derived subgroup.
-/

namespace Erdos117

open scoped BigOperators

/-- The explicit local bound already proved for every class-two prime group. -/
noncomputable def primeCoverLogBound (p n L : ℕ) : ℝ :=
  Real.log 2 / 2 * n + 2 * L +
    48 * Real.sqrt n * ((L : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) *
      Real.sqrt ((L : ℝ) + Nat.clog p ((2 * n) ^ 2) + 1) +
    Real.log p * L * L * Nat.clog p ((2 * n) ^ 2)

open scoped Classical in
/-- A class-two group has an actual product cover with no cost from its
abelian Sylow factors. All factor clique bounds and lengths are constructed. -/
theorem exists_class_two_sylow_cover_exact {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ c L k : (Nat.card G).primeFactors → ℕ,
      (∀ p, NoncommutingBound (default : Sylow p.val G) (c p)) ∧
      (∀ p, 1 ≤ c p) ∧
      (∀ p, ¬IsMulCommutative (default : Sylow p.val G) → 3 ≤ c p) ∧
      (∏ p, c p) ≤ n ∧
      (∀ p, p.val ^ L p = Nat.card (commutator (default : Sylow p.val G))) ∧
      HasAbelianCover G (∏ p, k p) ∧
      Real.log (∏ p, k p : ℕ) ≤
        ∑ p, if IsMulCommutative (default : Sylow p.val G) then 0
          else primeCoverLogBound p.val (c p) (L p) := by
  classical
  have := isNilpotent_of_class_two hG
  let e := nilpotentSylowEquiv (G := G)
  obtain ⟨c, hc, hc1, hc3, hprod⟩ :=
    exists_factor_clique_bounds (noncommutingBound_mulEquiv e.symm hn)
  have hlocal (p : (Nat.card G).primeFactors) :
      ∃ L k : ℕ, p.val ^ L = Nat.card (commutator (default : Sylow p.val G)) ∧
        HasAbelianCover (default : Sylow p.val G) k ∧
        Real.log k ≤ if IsMulCommutative (default : Sylow p.val G) then 0
          else primeCoverLogBound p.val (c p) L := by
    have : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    by_cases hcomm : IsMulCommutative (default : Sylow p.val G)
    · have := hcomm
      refine ⟨0, 1, ?_, hasAbelianCover_one, ?_⟩
      · rw [pow_zero, commutator_eq_bot]
        simp
      · simp [hcomm]
    · obtain ⟨L, k, hcard, hcover, hlog⟩ := exists_class_two_prime_cover
        (default : Sylow p.val G).isPGroup'
        (class_two_subgroup hG (default : Sylow p.val G)) (hc p)
      refine ⟨L, k, ?_, hcover, ?_⟩
      · exact hcard.symm
      · simpa only [if_neg hcomm, primeCoverLogBound] using hlog
  choose L k hcard hk hcost using hlocal
  refine ⟨c, L, k, hc, hc1, hc3, hprod, hcard, ?_, ?_⟩
  · exact hasAbelianCover_mulEquiv e (hasAbelianCover_pi hk)
  · have hk0 (p : (Nat.card G).primeFactors) : (k p : ℝ) ≠ 0 := by
      have hpos := one_le_of_noncommutingBound (noncommutingBound_of_abelianCover (hk p))
      exact_mod_cast (by omega : k p ≠ 0)
    rw [Nat.cast_prod, Real.log_prod (fun p _ => hk0 p)]
    exact Finset.sum_le_sum (fun p _ => hcost p)

open scoped Classical in
/-- The factor orders in the exact construction are at most the order of
the ambient derived subgroup. -/
theorem exists_class_two_sylow_cover {G : Type*} [Group G] [Finite G]
    (hG : commutator G ≤ Subgroup.center G) {n : ℕ} (hn : NoncommutingBound G n) :
    ∃ c L k : (Nat.card G).primeFactors → ℕ,
      (∀ p, NoncommutingBound (default : Sylow p.val G) (c p)) ∧
      (∀ p, 1 ≤ c p) ∧
      (∀ p, ¬IsMulCommutative (default : Sylow p.val G) → 3 ≤ c p) ∧
      (∏ p, c p) ≤ n ∧
      (∀ p, p.val ^ L p ≤ Nat.card (commutator G)) ∧
      HasAbelianCover G (∏ p, k p) ∧
      Real.log (∏ p, k p : ℕ) ≤
        ∑ p, if IsMulCommutative (default : Sylow p.val G) then 0
          else primeCoverLogBound p.val (c p) (L p) := by
  obtain ⟨c, L, k, hc, hc1, hc3, hprod, hcard, hcover, hlog⟩ :=
    exists_class_two_sylow_cover_exact hG hn
  refine ⟨c, L, k, hc, hc1, hc3, hprod, ?_, hcover, hlog⟩
  intro p
  rw [hcard]
  exact commutator_subgroup_card_le ((default : Sylow p.val G) : Subgroup G)

end Erdos117
