import ErdosProblems.Erdos4.FGKMTCompleteCover
import ErdosProblems.Erdos4.FGKMTGrowingCleanupParameters
import ErdosProblems.Erdos4.FGKMTReservePrimes

/-! Unconditional full interval covers at every sufficiently large FGKMT endpoint. -/

namespace Erdos4.FGKMT

open Filter Classical ChebyshevIntervals

theorem exists_growing_interval_cover :
    ∃ (c : ℝ) (K : ℕ), 0 < c ∧ 1 ≤ K ∧ ∀ᶠ x : ℕ in atTop,
      ∃ cover : Erdos4.ResidueCover (growingGapLength c x),
        cover.modulus ≤ primorial (K * x) := by
  obtain ⟨c, C, hc, hC, hprimeCover⟩ := exists_growing_prime_covering
  obtain ⟨K, hK, hreserve⟩ := exists_growing_reserve (C + 1 + 3 * Real.log 2)
  refine ⟨c, K, hc, hK, ?_⟩
  filter_upwards [hprimeCover, hreserve, eventually_growing_zero_parameters hc,
    eventually_growing_smooth_bound hc, eventually_primeCounting_upper,
    eventually_growing_outer_log_budget, eventually_ge_atTop 2]
    with x hprimeCover hreserve hzero hsmooth hπ hlogs hx
  let Y := growingGapLength c x
  let sieve := growingRandomPrimes x
  let sources := growingSourcePrimes x
  let targets := primeInterval x Y
  let reserve := primeInterval x (K * x)
  let smooth := Nat.smoothNumbersUpTo Y (growingRandomEnd x + 1)
  let : ∀ l : sieve, Fact l.val.Prime :=
    fun l => ⟨(ArithmeticFibers.mem_primeWindow.mp l.property).1⟩
  obtain ⟨a, b, hmiss⟩ := hprimeCover
  let missed := remainingPrimeTargets sieve sources targets Y a b
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlogs.1
  have hmissNat : missed.card ≤
      (sourceSurvivors sources targets (initialSurvivors (growingRandomValue x) Y targets a) b).card := by
    dsimp only [missed, remainingPrimeTargets]
    exact Finset.card_image_le
  have hmiss' : (missed.card : ℝ) ≤ C * x / Real.log (x : ℝ) := by
    have hh : (missed.card : ℝ) ≤
        ((sourceSurvivors sources targets (initialSurvivors (growingRandomValue x) Y targets a) b).card : ℝ) := by
      exact_mod_cast hmissNat
    exact hh.trans hmiss
  have hsmooth' : (smooth.card : ℝ) ≤ (x : ℝ) / Real.log (x : ℝ) := by
    apply hsmooth.trans
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg x) hLpos (by nlinarith [hlogs.1])
  have hπ' : (x.primesLE.card : ℝ) ≤ (3 * Real.log 2) * x / Real.log (x : ℝ) := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using hπ
  have hcardNat : (missed ∪ (smooth ∪ x.primesLE)).card ≤
      missed.card + (smooth.card + x.primesLE.card) :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
  have hcard : (missed ∪ (smooth ∪ x.primesLE)).card ≤ reserve.card := by
    have hreal : ((missed ∪ (smooth ∪ x.primesLE)).card : ℝ) ≤ (reserve.card : ℝ) := by
      calc
        _ ≤ (missed.card : ℝ) + ((smooth.card : ℝ) + x.primesLE.card) := by exact_mod_cast hcardNat
        _ ≤ C * x / Real.log (x : ℝ) +
            ((x : ℝ) / Real.log (x : ℝ) + (3 * Real.log 2) * x / Real.log (x : ℝ)) :=
          add_le_add hmiss' (add_le_add hsmooth' hπ')
        _ = (C + 1 + 3 * Real.log 2) * x / Real.log (x : ℝ) := by ring
        _ ≤ _ := hreserve
    exact_mod_cast hreal
  have hxK : x ≤ K * x := by
    simpa only [one_mul] using Nat.mul_le_mul_right x hK
  exact exists_complete_cover_from_choices sieve sources reserve hzero.1
    (hzero.2.1.trans hzero.2.2.1) hzero.2.2.1 (Nat.div_le_self x 32) hxK hzero.2.2.2
    (fun p hp => (ArithmeticFibers.mem_primeWindow.mp hp).2)
    (fun p hp => mem_growingSourcePrimes.mp hp)
    (fun p hp => mem_primeInterval.mp hp) a b hcard

end Erdos4.FGKMT
