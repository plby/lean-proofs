/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.NumberTheory.Chebyshev

/-!
# Factor-four blocks of primes

This file derives a positive lower bound for the number, and hence the
harmonic mass, of the primes in `(n, 4n]`.  The only prime-distribution
inputs are `Chebyshev.pi_ge` and `Chebyshev.eventually_primeCounting_le`.
-/

namespace Erdos896

open Filter Asymptotics
open scoped Nat.Prime Topology

/-- The primes in the factor-four interval `(n, 4n]`. -/
def primeBlock (n : ℕ) : Finset ℕ :=
  (Finset.Ioc n (4 * n)).filter Nat.Prime

@[simp]
lemma mem_primeBlock {n p : ℕ} :
    p ∈ primeBlock n ↔ n < p ∧ p ≤ 4 * n ∧ Nat.Prime p := by
  simp [primeBlock, and_assoc]

/-- The cardinality of a factor-four prime block is the corresponding
difference of prime-counting functions. -/
lemma primeBlock_card (n : ℕ) :
    (primeBlock n).card = Nat.primeCounting (4 * n) - Nat.primeCounting n := by
  rw [primeBlock, ← Nat.primesLE_card_eq_primeCounting,
    ← Nat.primesLE_card_eq_primeCounting]
  rw [Nat.primesLE_eq_filter_Ioc_zero, Nat.primesLE_eq_filter_Ioc_zero]
  have hsubset :
      (Finset.Ioc 0 n).filter Nat.Prime ⊆
        (Finset.Ioc 0 (4 * n)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨hp.1.1, by omega⟩, hp.2⟩
  rw [← Finset.card_sdiff_of_subset hsubset]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hnp, hp4n⟩, hp⟩
    exact ⟨⟨⟨hp.pos, hp4n⟩, hp⟩, fun h ↦ (not_lt_of_ge h.1.2) hnp⟩
  · rintro ⟨⟨⟨hp0, hp4n⟩, hp⟩, hsmall⟩
    refine ⟨⟨?_, hp4n⟩, hp⟩
    by_contra! hpn
    exact hsmall ⟨⟨hp0, hpn⟩, hp⟩

/-- An eventual lower bound for `π(4n)`.  It is a deliberately convenient
weaker consequence of Chebyshev's explicit lower bound. -/
lemma eventually_pi_four_mul_lower :
    ∀ᶠ n : ℕ in atTop,
      (8 / 3 : ℝ) * Real.log 2 * n / Real.log n ≤
        (Nat.primeCounting (4 * n) : ℝ) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have harg :
      Tendsto (fun n : ℕ ↦ (4 : ℝ) * n + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have herrReal :=
    Real.isLittleO_log_id_atTop.bound
      (div_pos hlog2 (by norm_num : (0 : ℝ) < 10))
  have herr : ∀ᶠ n : ℕ in atTop,
      Real.log ((4 : ℝ) * n + 1) ≤ Real.log 2 * n := by
    filter_upwards [harg.eventually herrReal, eventually_ge_atTop 1]
      with n hn hn1
    have hx0 : 0 ≤ (4 : ℝ) * n := by positivity
    have hx : 1 ≤ (4 : ℝ) * n + 1 := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hn
    dsimp only [id_eq] at hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hbiglog : ∀ᶠ n : ℕ in atTop,
      8 * Real.log 4 ≤ Real.log n :=
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [herr, hbiglog, eventually_ge_atTop 2]
    with n herrn hlogn hn2
  have hn0 : n ≠ 0 := by omega
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn2)
  have hlog4npos : 0 < Real.log ((4 * n : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < 4 * n)
  have hlogmul :
      Real.log ((4 * n : ℕ) : ℝ) =
        Real.log 4 + Real.log (n : ℝ) := by
    norm_num [Nat.cast_mul, Real.log_mul, hn0]
  have hden :
      Real.log ((4 * n : ℕ) : ℝ) ≤
        (9 / 8 : ℝ) * Real.log (n : ℝ) := by
    rw [hlogmul]
    nlinarith
  have hnum :
      Real.log (((4 * n : ℕ) : ℝ) + 1) ≤
        Real.log 2 * (n : ℝ) := by
    simpa [Nat.cast_mul] using herrn
  apply le_trans ?_ (Chebyshev.pi_ge (4 * n))
  rw [div_le_div_iff₀ hlognpos hlog4npos]
  calc
    ((8 / 3 : ℝ) * Real.log 2 * (n : ℝ)) *
          Real.log ((4 * n : ℕ) : ℝ)
        ≤ ((8 / 3 : ℝ) * Real.log 2 * (n : ℝ)) *
            ((9 / 8 : ℝ) * Real.log (n : ℝ)) := by
              gcongr
    _ = (3 * Real.log 2 * (n : ℝ)) * Real.log (n : ℝ) := by
      ring
    _ ≤ (((4 * n : ℕ) : ℝ) * Real.log 2 -
          Real.log (((4 * n : ℕ) : ℝ) + 1)) *
            Real.log (n : ℝ) := by
      gcongr
      norm_num [Nat.cast_mul]
      linarith

/-- An eventual upper bound for `π(n)` with coefficient
`(5 / 2) * log 2`. -/
lemma eventually_pi_upper :
    ∀ᶠ n : ℕ in atTop,
      (Nat.primeCounting n : ℝ) ≤
        (5 / 2 : ℝ) * Real.log 2 * n / Real.log n := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
        (Chebyshev.eventually_primeCounting_le (half_pos hlog2))
  filter_upwards [h] with n hn
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hn
  norm_num at hn
  calc
    (Nat.primeCounting n : ℝ) ≤
        (2 * Real.log 2 + Real.log 2 / 2) * n / Real.log n := hn
    _ = (5 / 2 : ℝ) * Real.log 2 * n / Real.log n := by ring

/-- Eventually, the factor-four interval contains at least
`(log 2 / 6) * n / log n` primes. -/
theorem eventually_primeBlock_card_lower :
    ∀ᶠ n : ℕ in atTop,
      (Real.log 2 / 6) * (n : ℝ) / Real.log n ≤
        ((primeBlock n).card : ℝ) := by
  filter_upwards [eventually_pi_four_mul_lower, eventually_pi_upper]
    with n hfour hone
  rw [primeBlock_card,
    Nat.cast_sub (Nat.monotone_primeCounting (by omega))]
  calc
    Real.log 2 / 6 * (n : ℝ) / Real.log n =
        (8 / 3 : ℝ) * Real.log 2 * n / Real.log n -
          (5 / 2 : ℝ) * Real.log 2 * n / Real.log n := by ring
    _ ≤ (Nat.primeCounting (4 * n) : ℝ) - Nat.primeCounting n :=
      sub_le_sub hfour hone

/-- The harmonic mass of the primes in `(n, 4n]` is bounded below by a
positive constant times `1 / log n`, using only Chebyshev's estimates. -/
theorem eventually_primeBlock_harmonic_lower :
    ∀ᶠ n : ℕ in atTop,
      Real.log 2 / (24 * Real.log n) ≤
        ∑ p ∈ primeBlock n, (1 / (p : ℝ)) := by
  filter_upwards [eventually_primeBlock_card_lower, eventually_ge_atTop 2]
    with n hcard hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hlogne : Real.log (n : ℝ) ≠ 0 := hlogpos.ne'
  have hsum :
      ∑ p ∈ primeBlock n, (1 / ((4 * n : ℕ) : ℝ)) ≤
        ∑ p ∈ primeBlock n, (1 / (p : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact one_div_le_one_div_of_le (by exact_mod_cast hp'.2.pos)
      (by exact_mod_cast (Finset.mem_Ioc.mp hp'.1).2)
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  calc
    Real.log 2 / (24 * Real.log n) =
        ((Real.log 2 / 6) * (n : ℝ) / Real.log n) /
          ((4 * n : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      field_simp
      ring
    _ ≤ ((primeBlock n).card : ℝ) / ((4 * n : ℕ) : ℝ) := by
      exact (div_le_div_iff_of_pos_right (by positivity)).mpr hcard
    _ = ((primeBlock n).card : ℝ) *
        (1 / ((4 * n : ℕ) : ℝ)) := by ring
    _ ≤ ∑ p ∈ primeBlock n, (1 / (p : ℝ)) := hsum

end Erdos896
