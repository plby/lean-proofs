import ErdosProblems.Erdos587.HooleyEulerProducts
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic

/-!
# Harmonic divisor bounds from the proved Mertens estimate

The bounded-error reciprocal-prime theorem is already proved in the 697
development. Combining it with the exact squarefree Euler products gives
the fixed divisor moments needed for the Delta induction.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_squarefree_divisorPower_log_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X n : ℕ), 2 ≤ X → Squarefree n →
      n.primeFactors ⊆ Nat.primesLE X →
      (∑ d ∈ n.divisors, (d.divisors.card : ℝ) ^ k / d) ≤
        C * Real.log (X : ℝ) ^ (2 ^ k : ℕ) := by
  obtain ⟨C₀, _, hC₀⟩ := Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log
  refine ⟨Real.exp ((2 : ℝ) ^ k * C₀), Real.exp_pos _, ?_⟩
  intro X n hX hn hsub
  have hprime : (∑ p ∈ n.primeFactors, (1 : ℝ) / p) ≤
      Real.log (Real.log (X : ℝ)) + C₀ := by
    have hupper := (abs_le.mp (hC₀ X hX)).2
    have hsum : (∑ p ∈ n.primeFactors, (1 : ℝ) / p) ≤
        Erdos697.PrimeHarmonic.sum X :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    linarith
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  calc
    _ ≤ Real.exp ((2 : ℝ) ^ k * ∑ p ∈ n.primeFactors, (1 : ℝ) / p) :=
      sum_divisorReciprocalPower_le_exp k hn
    _ ≤ Real.exp ((2 : ℝ) ^ k * (Real.log (Real.log (X : ℝ)) + C₀)) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left hprime (by positivity))
    _ = Real.exp ((2 : ℝ) ^ k * C₀) * Real.log (X : ℝ) ^ (2 ^ k : ℕ) := by
      rw [mul_add, Real.exp_add]
      have hcast : (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) := by norm_cast
      rw [hcast, Real.exp_nat_mul, Real.exp_log hlog]
      ring

theorem prime_set_eulerProduct_le_exp (S : Finset ℕ) (r : ℕ) :
    (∏ p ∈ S, (1 + (r : ℝ) / p)) ≤
      Real.exp ((r : ℝ) * ∑ p ∈ S, (1 : ℝ) / p) := by
  calc
    _ ≤ ∏ p ∈ S, Real.exp ((r : ℝ) / p) := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp ((r : ℝ) / p)
    _ = Real.exp (∑ p ∈ S, (r : ℝ) / p) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

/-- The constant is uniform in both cutoffs and in subsets of the prime
window. The exponent is exactly `r`, not an unspecified logarithmic power. -/
theorem exists_primeWindow_eulerProduct_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y : ℕ), 2 ≤ Y → Y ≤ X →
      ∀ S : Finset ℕ, S ⊆ Nat.primesLE X \ Nat.primesLE Y →
      (∏ p ∈ S, (1 + (r : ℝ) / p)) ≤
        C * (Real.log (X : ℝ) / Real.log (Y : ℝ)) ^ r := by
  obtain ⟨C₀, _, hC₀⟩ := Erdos697.PrimeHarmonic.exists_uniform_abs_sum_sub_log_log
  refine ⟨Real.exp ((r : ℝ) * (2 * C₀)), Real.exp_pos _, ?_⟩
  intro X Y hY hYX S hS
  have hprimes : Nat.primesLE Y ⊆ Nat.primesLE X := by
    intro p hp
    obtain ⟨hpY, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpY.trans hYX, hp⟩
  have hsum : (∑ p ∈ S, (1 : ℝ) / p) ≤
      Real.log (Real.log (X : ℝ)) - Real.log (Real.log (Y : ℝ)) + 2 * C₀ := by
    have hsubset := Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun p _ _ => show (0 : ℝ) ≤ 1 / p by positivity)
    rw [Finset.sum_sdiff_eq_sub hprimes] at hsubset
    have hupper := (abs_le.mp (hC₀ X (hY.trans hYX))).2
    have hlower := (abs_le.mp (hC₀ Y hY)).1
    change (∑ p ∈ S, (1 : ℝ) / p) ≤
      Erdos697.PrimeHarmonic.sum X - Erdos697.PrimeHarmonic.sum Y at hsubset
    linarith
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  calc
    _ ≤ Real.exp ((r : ℝ) * ∑ p ∈ S, (1 : ℝ) / p) :=
      prime_set_eulerProduct_le_exp S r
    _ ≤ Real.exp ((r : ℝ) *
        (Real.log (Real.log (X : ℝ)) - Real.log (Real.log (Y : ℝ)) + 2 * C₀)) :=
      Real.exp_monotone (mul_le_mul_of_nonneg_left hsum (by positivity))
    _ = _ := by
      rw [mul_add, Real.exp_add, Real.exp_nat_mul, Real.exp_sub,
        Real.exp_log hlogX, Real.exp_log hlogY]
      ring

noncomputable def deltaTailEulerConstant : ℝ :=
  Classical.choose (exists_primeWindow_eulerProduct_bound 1)

lemma deltaTailEulerConstant_pos : 0 < deltaTailEulerConstant :=
  (Classical.choose_spec (exists_primeWindow_eulerProduct_bound 1)).1

lemma delta_prime_tail_euler_bound {p x : ℕ} (hp : p.Prime) (hpx : p < x) :
    (∏ r ∈ (Finset.Ioo p x).filter Nat.Prime, (1 + (1 : ℝ) / r)) ≤
      deltaTailEulerConstant * (Real.log (x : ℝ) / Real.log (p : ℝ)) := by
  have h := (Classical.choose_spec (exists_primeWindow_eulerProduct_bound 1)).2
    x p hp.two_le hpx.le ((Finset.Ioo p x).filter Nat.Prime)
  change (Finset.Ioo p x).filter Nat.Prime ⊆ Nat.primesLE x \ Nat.primesLE p →
    (∏ r ∈ (Finset.Ioo p x).filter Nat.Prime, (1 + ((1 : ℕ) : ℝ) / r)) ≤
      deltaTailEulerConstant * (Real.log (x : ℝ) / Real.log (p : ℝ)) ^ 1 at h
  simp only [Nat.cast_one, pow_one] at h
  apply h
  intro r hr
  obtain ⟨hrI, hrprime⟩ := Finset.mem_filter.mp hr
  obtain ⟨hpr, hrx⟩ := Finset.mem_Ioo.mp hrI
  apply Finset.mem_sdiff.mpr
  exact ⟨Nat.mem_primesLE.mpr ⟨hrx.le, hrprime⟩,
    fun hrp => (not_le_of_gt hpr) (Nat.mem_primesLE.mp hrp).1⟩

end Erdos587
