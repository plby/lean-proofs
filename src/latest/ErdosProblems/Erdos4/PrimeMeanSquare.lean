import ErdosProblems.Erdos4.PrimitiveCharacterFamily
import ErdosProblems.Erdos4.SelbergHarmonicMass

/-!
# A weak prime-supported large sieve with elementary cutoffs

Take the prime-gap scale to be `x = t^50`, the divisor radius `R = t^5`,
the character-conductor bound `Q = t^10`, and the Selberg cutoff `D = t^2`.
The same cutoff works for every endpoint `N >= x`, including the larger
target-prime interval. This avoids taking integer parts of fractional powers.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.PrimeMeanSquare

open PrimitiveCharacterFamily SelbergCoefficients

theorem eventually_good_cutoff :
    ∀ᶠ t : ℕ in atTop, 2 ≤ t ∧ Real.log t ≤ harmonicMass (t ^ 2) := by
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp
    SelbergHarmonicMass.eventually_log_div_two_le_harmonicMass
  refine Filter.eventually_atTop.mpr ⟨max 2 D₀, ?_⟩
  intro t ht
  have ht2 : 2 ≤ t := (le_max_left 2 D₀).trans ht
  have htD : D₀ ≤ t := (le_max_right 2 D₀).trans ht
  have htsq : t ≤ t ^ 2 := by nlinarith
  have h := (hD₀ (t ^ 2) (htD.trans htsq)).2
  have hlog : Real.log ((t ^ 2 : ℕ) : ℝ) / 2 = Real.log t := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  exact ⟨ht2, hlog ▸ h⟩

theorem sieve_constant_le {t N m : ℕ} (ht : 2 ≤ t)
    (hH : Real.log t ≤ harmonicMass (t ^ 2)) (hN : t ^ 50 ≤ N) (hm : m ≤ t ^ 20) :
    (N : ℝ) / harmonicMass (t ^ 2) + (t : ℝ) ^ 8 + (m : ℝ) * (t : ℝ) ^ 28 ≤
      2 * (N : ℝ) / Real.log t := by
  have htR : (1 : ℝ) < t := by exact_mod_cast ht
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos htR
  have hNcast : (t : ℝ) ^ 50 ≤ N := by exact_mod_cast hN
  have hmcast : (m : ℝ) ≤ (t : ℝ) ^ 20 := by exact_mod_cast hm
  have hmain : (N : ℝ) / harmonicMass (t ^ 2) ≤ (N : ℝ) / Real.log t :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) hlog hH
  have hsmall : (t : ℝ) ^ 8 ≤ (t : ℝ) ^ 48 := pow_le_pow_right₀ htR.le (by norm_num)
  have herror : (m : ℝ) * (t : ℝ) ^ 28 ≤ (t : ℝ) ^ 48 := by
    calc
      (m : ℝ) * (t : ℝ) ^ 28 ≤ (t : ℝ) ^ 20 * (t : ℝ) ^ 28 :=
        mul_le_mul_of_nonneg_right hmcast (by positivity)
      _ = (t : ℝ) ^ 48 := by rw [← pow_add]
  have hlogsmall : 2 * Real.log (t : ℝ) ≤ (t : ℝ) ^ 2 := by
    have hh := Real.log_le_sub_one_of_pos (lt_trans zero_lt_one htR)
    nlinarith [sq_nonneg ((t : ℝ) - 1)]
  have hbudget : 2 * (t : ℝ) ^ 48 ≤ (N : ℝ) / Real.log t := by
    apply (le_div_iff₀ hlog).mpr
    calc
      2 * (t : ℝ) ^ 48 * Real.log t = (2 * Real.log t) * (t : ℝ) ^ 48 := by ring
      _ ≤ (t : ℝ) ^ 2 * (t : ℝ) ^ 48 := mul_le_mul_of_nonneg_right hlogsmall (by positivity)
      _ = (t : ℝ) ^ 50 := by rw [← pow_add]
      _ ≤ N := hNcast
  rw [mul_div_assoc]
  linarith

theorem prime_mean_square_at_good_cutoff {I : Type*} [Fintype I]
    {t : ℕ} (ht : 2 ≤ t) (hH : Real.log t ≤ harmonicMass (t ^ 2))
    (family : I → Entry) (hvalid : ∀ i, Valid (family i)) (hinjective : Function.Injective family)
    (hQ : ∀ i, (family i).1 ≤ t ^ 10) (N : ℕ) (hN : t ^ 50 ≤ N)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime ∧ t ^ 2 < p ∧ p ≤ N)
    (a : I → ℂ) :
    (∑ p ∈ primes, ‖∑ i, a i * value (family i) p‖ ^ 2) ≤
      (2 * (N : ℝ) / Real.log t) * ∑ i, ‖a i‖ ^ 2 := by
  have hD : 1 ≤ t ^ 2 := by nlinarith
  have hcard : Fintype.card I ≤ t ^ 20 := by
    simpa only [← pow_mul] using card_family_le_square family hvalid hinjective hQ
  have hconstant : (N : ℝ) / harmonicMass (t ^ 2) + ((t ^ 2 : ℕ) : ℝ) ^ 4 +
      (Fintype.card I : ℝ) * (((t ^ 10 : ℕ) : ℝ) ^ 2 * ((t ^ 2 : ℕ) : ℝ) ^ 4) ≤
        2 * (N : ℝ) / Real.log t := by
    convert sieve_constant_le ht hH hN hcard using 1
    push_cast
    ring
  exact (prime_mean_square_le family hvalid hinjective hD hQ N primes hprimes a).trans
    (mul_le_mul_of_nonneg_right hconstant (Finset.sum_nonneg (fun i _hi => sq_nonneg _)))

theorem prime_mean_square_dual_at_good_cutoff {I : Type*} [Fintype I]
    {t : ℕ} (ht : 2 ≤ t) (hH : Real.log t ≤ harmonicMass (t ^ 2))
    (family : I → Entry) (hvalid : ∀ i, Valid (family i)) (hinjective : Function.Injective family)
    (hQ : ∀ i, (family i).1 ≤ t ^ 10) (N : ℕ) (hN : t ^ 50 ≤ N)
    (primes : Finset ℕ) (hprimes : ∀ p ∈ primes, p.Prime ∧ t ^ 2 < p ∧ p ≤ N)
    (a : primes → ℂ) :
    (∑ i, ‖∑ p : primes, a p * value (family i) p‖ ^ 2) ≤
      (2 * (N : ℝ) / Real.log t) * ∑ p : primes, ‖a p‖ ^ 2 := by
  have hD : 1 ≤ t ^ 2 := by nlinarith
  have hcard : Fintype.card I ≤ t ^ 20 := by
    simpa only [← pow_mul] using card_family_le_square family hvalid hinjective hQ
  have hconstant : (N : ℝ) / harmonicMass (t ^ 2) + ((t ^ 2 : ℕ) : ℝ) ^ 4 +
      (Fintype.card I : ℝ) * (((t ^ 10 : ℕ) : ℝ) ^ 2 * ((t ^ 2 : ℕ) : ℝ) ^ 4) ≤
        2 * (N : ℝ) / Real.log t := by
    convert sieve_constant_le ht hH hN hcard using 1
    push_cast
    ring
  exact (prime_mean_square_dual_le family hvalid hinjective hD hQ N primes hprimes a).trans
    (mul_le_mul_of_nonneg_right hconstant (Finset.sum_nonneg (fun p _hp => sq_nonneg _)))

/-- The good-cutoff condition is discharged: the estimate holds for every
sufficiently large integer parameter and every permitted primitive family. -/
theorem eventually_prime_mean_square {I : Type*} [Fintype I] :
    ∀ᶠ t : ℕ in atTop, ∀ family : I → Entry,
      (∀ i, Valid (family i)) → Function.Injective family →
      (∀ i, (family i).1 ≤ t ^ 10) → ∀ N : ℕ, t ^ 50 ≤ N →
      ∀ primes : Finset ℕ, (∀ p ∈ primes, p.Prime ∧ t ^ 2 < p ∧ p ≤ N) →
      ∀ a : I → ℂ,
        (∑ p ∈ primes, ‖∑ i, a i * value (family i) p‖ ^ 2) ≤
          (2 * (N : ℝ) / Real.log t) * ∑ i, ‖a i‖ ^ 2 := by
  filter_upwards [eventually_good_cutoff] with t ht
  intro family hvalid hinjective hQ N hN primes hprimes a
  exact prime_mean_square_at_good_cutoff ht.1 ht.2 family hvalid hinjective hQ N hN primes hprimes a

theorem eventually_prime_mean_square_dual {I : Type*} [Fintype I] :
    ∀ᶠ t : ℕ in atTop, ∀ family : I → Entry,
      (∀ i, Valid (family i)) → Function.Injective family →
      (∀ i, (family i).1 ≤ t ^ 10) → ∀ N : ℕ, t ^ 50 ≤ N →
      ∀ primes : Finset ℕ, (∀ p ∈ primes, p.Prime ∧ t ^ 2 < p ∧ p ≤ N) →
      ∀ a : primes → ℂ,
        (∑ i, ‖∑ p : primes, a p * value (family i) p‖ ^ 2) ≤
          (2 * (N : ℝ) / Real.log t) * ∑ p : primes, ‖a p‖ ^ 2 := by
  filter_upwards [eventually_good_cutoff] with t ht
  intro family hvalid hinjective hQ N hN primes hprimes a
  exact prime_mean_square_dual_at_good_cutoff ht.1 ht.2 family hvalid hinjective hQ N hN primes hprimes a

end Erdos4.PrimeMeanSquare
