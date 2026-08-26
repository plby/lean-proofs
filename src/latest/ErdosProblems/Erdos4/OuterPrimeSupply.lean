import ErdosProblems.Erdos4.OuterAccuracy

/-!
# Source and reserve primes on the concrete ray

Both fixed-ratio prime intervals contain a positive fixed multiple of
`X / log t` primes. Their endpoints are exact integers, and their
separation from the random sieve and divisor cutoff is elementary.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterPrimeSupply

open SmoothParameters ChebyshevIntervals OuterRay OuterAccuracy

theorem source_range (a r : ℕ) {p : ℕ} (hp : p ∈ sourcePrimes a r) :
    p.Prime ∧ 16 * base a r < p ∧ p ≤ frontier a r := mem_primeInterval.mp hp

theorem reserve_range (a r : ℕ) {p : ℕ} (hp : p ∈ reservePrimes a r) :
    p.Prime ∧ base a r < p ∧ p ≤ 16 * base a r := mem_primeInterval.mp hp

theorem source_gt_radius (a r : ℕ) {p : ℕ} (hp : p ∈ sourcePrimes a r) :
    primaryFrontier a r ^ 5 < p := by
  have ht : 1 ≤ primaryFrontier a r := (primaryFrontier_pos a r)
  have hpow : primaryFrontier a r ^ 5 ≤ base a r := Nat.pow_le_pow_right ht (by norm_num)
  have hh := (source_range a r hp).2.1
  omega

theorem source_gt_majorant (a r : ℕ) {p : ℕ} (hp : p ∈ sourcePrimes a r) :
    primaryFrontier a r ^ 2 < p := by
  have ht : 1 ≤ primaryFrontier a r := (primaryFrontier_pos a r)
  have hpow : primaryFrontier a r ^ 2 ≤ primaryFrontier a r ^ 5 := Nat.pow_le_pow_right ht (by norm_num)
  exact hpow.trans_lt (source_gt_radius a r hp)

theorem source_reserve_disjoint (a r : ℕ) : Disjoint (sourcePrimes a r) (reservePrimes a r) := by
  apply Finset.disjoint_left.mpr
  intro p hp hs
  have h₁ := (source_range a r hp).2.1
  have h₂ := (reserve_range a r hs).2.2
  omega

theorem random_source_disjoint (a r : ℕ) : Disjoint (randomPrimes a r) (sourcePrimes a r) := by
  apply Finset.disjoint_left.mpr
  intro p hp hs
  have h₁ := (mem_primeInterval.mp hp).2.2
  have h₂ := (source_range a r hs).2.1
  have h₃ := smooth_le_base a r
  omega

theorem random_reserve_disjoint (a r : ℕ) : Disjoint (randomPrimes a r) (reservePrimes a r) := by
  apply Finset.disjoint_left.mpr
  intro p hp hs
  have h₁ := (mem_primeInterval.mp hp).2.2
  have h₂ := (reserve_range a r hs).2.1
  have h₃ := smooth_le_base a r
  omega

theorem exists_prime_supply :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, ∀ᶠ r : ℕ in atTop,
      16 ≤ primaryFrontier a r ∧
      c * frontier a r / Real.log (primaryFrontier a r : ℝ) ≤ (sourcePrimes a r).card ∧
      c * frontier a r / Real.log (primaryFrontier a r : ℝ) ≤ (reservePrimes a r).card := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 25600, by positivity, ?_⟩
  intro a
  have hlargeBase : Tendsto (fun r : ℕ => 16 * base a r) atTop atTop :=
    tendsto_atTop_mono (fun r => by omega : ∀ r, base a r ≤ 16 * base a r) (tendsto_base a)
  filter_upwards [(tendsto_primary a).eventually (eventually_ge_atTop 16),
    (tendsto_base a).eventually eventually_primeInterval_lower,
    hlargeBase.eventually eventually_primeInterval_lower] with r ht hres hsrc
  have htpos : (0 : ℝ) < primaryFrontier a r := by exact_mod_cast primaryFrontier_pos a r
  have hlogt : 0 < Real.log (primaryFrontier a r : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < primaryFrontier a r by omega))
  have hbpos : (0 : ℝ) < base a r := by exact_mod_cast base_pos a r
  have hlogb : Real.log (base a r : ℝ) = 50 * Real.log (primaryFrontier a r : ℝ) := by
    rw [OuterRay.base, Nat.cast_pow, Real.log_pow]
    norm_num
  have hlog16 : Real.log (16 : ℝ) ≤ Real.log (primaryFrontier a r : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast ht)
  have hlogsrc : Real.log (16 * base a r : ℕ) ≤ 100 * Real.log (primaryFrontier a r : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hbpos.ne', hlogb]
    linarith
  have hnonneg : 0 ≤ Real.log 2 * base a r / Real.log (primaryFrontier a r : ℝ) := by positivity
  have htarget : (Real.log 2 / 25600) * frontier a r / Real.log (primaryFrontier a r : ℝ) =
      (1 / 100 : ℝ) * (Real.log 2 * base a r / Real.log (primaryFrontier a r : ℝ)) := by
    rw [OuterRay.frontier, Nat.cast_mul, Nat.cast_ofNat]
    ring
  refine ⟨ht, ?_, ?_⟩
  · have hcard : (primeInterval (16 * base a r) (16 * (16 * base a r))).card =
        (sourcePrimes a r).card := by
      unfold sourcePrimes OuterRay.frontier
      congr 2
      ring
    rw [htarget]
    calc
      _ ≤ (16 / 100 : ℝ) * (Real.log 2 * base a r / Real.log (primaryFrontier a r : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = Real.log 2 * (16 * base a r : ℕ) / (100 * Real.log (primaryFrontier a r : ℝ)) := by
        push_cast
        ring
      _ ≤ Real.log 2 * (16 * base a r : ℕ) / Real.log (16 * base a r : ℕ) :=
        div_le_div_of_nonneg_left (by positivity)
          (Real.log_pos (by exact_mod_cast (show 1 < 16 * base a r by have := hsrc.1; omega))) hlogsrc
      _ ≤ _ := by simpa only [hcard] using hsrc.2
  · rw [htarget]
    calc
      _ ≤ (1 / 50 : ℝ) * (Real.log 2 * base a r / Real.log (primaryFrontier a r : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hnonneg
      _ = Real.log 2 * base a r / Real.log (base a r : ℝ) := by rw [hlogb]; ring
      _ ≤ _ := hres.2

end Erdos4.OuterPrimeSupply
