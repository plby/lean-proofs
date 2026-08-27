/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTInitialSieveBudget
import ErdosProblems.Erdos4b.FGKMTFreshPrimeReserve
import ErdosProblems.Erdos4b.FGKMTIntervalCover

/-! # Unconditional complete covers at the stronger FGKMT18 scale -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_complete_source_covers :
    ∃ (c : ℝ) (M : ℕ), 0 < c ∧ 2 ≤ M ∧ ∀ᶠ x : ℕ in atTop,
      ∃ cover : ResidueCover (⌊sourceIntervalLength c x⌋₊ - x),
        ∀ p ∈ cover.primes, p ≤ M * x := by
  obtain ⟨c, K, hc, _, hsieve⟩ := exists_initial_sieve_budget
  obtain ⟨M, hM, hreserve⟩ := exists_fresh_prime_reserve K
  refine ⟨c, M, hc, hM, ?_⟩
  filter_upwards [hsieve, hreserve] with x hx hR
  obtain ⟨r, hr⟩ := hx
  have hcard : (initialResidueSurvivors x ⌊sourceIntervalLength c x⌋₊ r).card ≤
      (commonPinnedPrimeSet ((M * x) / 2) (M * x)).card := by
    exact_mod_cast hr.trans hR.1
  obtain ⟨cover, hcover⟩ := exists_interval_cover_of_survivors r
    (fun p hp => (mem_commonPinnedPrimeSet.mp hp).2.2) hR.2 hcard
  refine ⟨cover, ?_⟩
  intro p hp
  rw [hcover] at hp
  obtain hp | hp := Finset.mem_union.mp hp
  · exact (Nat.mem_primesLE.mp hp).1.trans (Nat.le_mul_of_pos_left x (by omega))
  · exact (mem_commonPinnedPrimeSet.mp hp).2.1

end

end Erdos4b.FGKMT
