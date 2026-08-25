import ErdosProblems.Erdos237b.Qualitative

/-!
# The analytic interface needed for the qualitative proof

The installed bounded-gaps package already proves positivity from normalized
sieve asymptotics for arbitrary tuples and thresholds. Its final application
only requests two primes. The first theorem here handles every threshold.

The premise in `qualitativePrimeTuples_of_positiveSieveExcess` is explicit:
positive sieve excess for arbitrary requested prime counts.
`Unconditional.lean` supplies it from the checked dyadic construction.
-/

namespace Erdos237b

open BoundedGaps BoundedGaps.Maynard Filter

/-- Positive sieve excess above `m` gives arbitrarily late translates with
at least `m + 1` primes, for any finite tuple. -/
theorem prime_shifts_of_positive_excess {H : Finset ℕ} {m : ℕ}
    (hpos : HasEventuallyPositiveSieveExcess H m) :
    InfinitelyOftenAtLeastPrimeShifts H (m + 1) := by
  obtain ⟨N₀, hN₀⟩ := hpos
  intro T
  obtain ⟨w, hw, hexcess⟩ := hN₀ (max N₀ (T + 1)) (le_max_left _ _)
  obtain ⟨n, hn, hcount⟩ := exists_primeShiftCount_gt_of_sieveExcess_pos hw hexcess
  have hNn := (Finset.mem_Ico.mp hn).1
  have hTN : T + 1 ≤ max N₀ (T + 1) := le_max_right _ _
  have hcountNat : m < primeShiftCount H n := by exact_mod_cast hcount
  exact ⟨n, by omega, hcountNat⟩

/-- Reuse the generic normalized-asymptotics theorem from `BoundedGaps`,
without the fixed tuple or the two-prime specialization. -/
theorem prime_shifts_of_normalized_asymptotics {H : Finset ℕ} {m : ℕ} {I J : ℝ}
    (weights : ℕ → ℕ → ℝ) (scale : ℕ → ℝ)
    (hmargin : 0 < J - m * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hweights : ∀ᶠ N : ℕ in atTop,
      ∀ n ∈ Finset.Ico N (2 * N), 0 ≤ weights N n)
    (hS1 : Tendsto (fun N => sieveWeightSum N (weights N) / scale N)
      atTop (nhds I))
    (hS2 : Tendsto (fun N => primeWeightedSieveSum H N (weights N) / scale N)
      atTop (nhds J)) :
    InfinitelyOftenAtLeastPrimeShifts H (m + 1) :=
  prime_shifts_of_positive_excess
    (hasEventuallyPositiveSieveExcess_of_normalized_asymptotics
      weights scale hmargin hscale hweights hS1 hS2)

/-- Positive sieve excess for each requested count gives the qualitative theorem. -/
theorem qualitativePrimeTuples_of_positiveSieveExcess
    (h : ∀ m : ℕ, ∃ k : ℕ, ∀ H : Finset ℕ, H.card = k →
      IsAdmissible H → HasEventuallyPositiveSieveExcess H m) :
    QualitativePrimeTuples := by
  intro m
  obtain ⟨k, hk⟩ := h m
  refine ⟨k, fun H hcard hH => ?_⟩
  obtain ⟨n, _, hn⟩ := prime_shifts_of_positive_excess (hk H hcard hH) 0
  exact ⟨n, (Nat.le_succ m).trans hn⟩

theorem hasEventuallyPositiveSieveExcess_of_lower_sequence {H : Finset ℕ} {rho I J : ℝ}
    (weights : ℕ → ℕ → ℝ) (scale b : ℕ → ℝ) (hmargin : 0 < J - rho * I)
    (hscale : ∀ᶠ N : ℕ in atTop, 0 < scale N)
    (hweights : ∀ N n, 0 ≤ weights N n)
    (hS1 : Tendsto (fun N => sieveWeightSum N (weights N) / scale N) atTop (nhds I))
    (hb : Tendsto b atTop (nhds J))
    (hble : ∀ᶠ N : ℕ in atTop, b N ≤ primeWeightedSieveSum H N (weights N) / scale N) :
    HasEventuallyPositiveSieveExcess H rho := by
  have hlim := hb.sub (hS1.const_mul rho)
  have hpos := hlim.eventually (isOpen_Ioi.mem_nhds hmargin)
  have hevent : ∀ᶠ N : ℕ in atTop, 0 < sieveExcess H N rho (weights N) := by
    filter_upwards [hscale, hpos, hble] with N hs hp hbN
    have hdiff : 0 < primeWeightedSieveSum H N (weights N) / scale N -
        rho * (sieveWeightSum N (weights N) / scale N) := by exact lt_of_lt_of_le hp (by linarith)
    have heq : sieveExcess H N rho (weights N) = scale N *
        (primeWeightedSieveSum H N (weights N) / scale N -
          rho * (sieveWeightSum N (weights N) / scale N)) := by
      unfold sieveExcess
      field_simp
    rw [heq]
    exact mul_pos hs hdiff
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hevent
  exact ⟨N₀, fun N hN => ⟨weights N, fun n _ => hweights N n, hN₀ N hN⟩⟩

end Erdos237b
