import UnitFractions.ForMathlib.BasicEstimates

/-!
# Weak Mertens bounds used for Erdős Problem 220

This file packages `weak_mertens_third_upper_all` at natural endpoints and
records the consequence for a product over any collection of primes bounded
by the endpoint.  The separate `h = 1` argument is needed because the source
theorem is stated only for real endpoints at least `2`.
-/

open scoped BigOperators

namespace Erdos220

@[simp] lemma partial_euler_product_one : partial_euler_product 1 = 1 := by
  rw [partial_euler_product]
  have hempty : (Finset.Icc 1 1).filter Nat.Prime = ∅ := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpBounds := Finset.mem_Icc.mp hp'.1
      have hpeq : p = 1 := by omega
      subst p
      exact (Nat.not_prime_one hp'.2).elim
    · simp
  rw [hempty]
  simp

/-- A positive constant bounding the inverse prime product at every natural
endpoint `h ≥ 1`.  The shifted logarithm makes the small endpoint uniform. -/
theorem partial_euler_product_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h →
      partial_euler_product h ≤ C * Real.log ((h : ℝ) + 2) := by
  obtain ⟨c, hc, hupper⟩ := weak_mertens_third_upper_all
  let C : ℝ := max c (Real.log 3)⁻¹
  have hC : 0 < C := hc.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro h hh
  by_cases hh2 : 2 ≤ h
  · have hh2R : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh2
    have hprod : 0 ≤ partial_euler_product h :=
      (by norm_num : (0 : ℝ) ≤ 1).trans partial_euler_trivial_lower_bound
    have hlog : 0 ≤ Real.log (h : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
    have hsource :
        partial_euler_product h ≤ c * Real.log (h : ℝ) := by
      simpa [Real.norm_of_nonneg hprod, Real.norm_of_nonneg hlog] using
        hupper (h : ℝ) hh2R
    have hlog_mono : Real.log (h : ℝ) ≤ Real.log ((h : ℝ) + 2) := by
      apply Real.log_le_log
      · positivity
      · linarith
    calc
      partial_euler_product h ≤ c * Real.log (h : ℝ) := hsource
      _ ≤ C * Real.log (h : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
      _ ≤ C * Real.log ((h : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hlog_mono hC.le
  · have heq : h = 1 := by omega
    subst h
    have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    have hsmall : (Real.log 3)⁻¹ ≤ C := le_max_right _ _
    have hfinal : partial_euler_product 1 ≤ C * Real.log 3 := calc
      partial_euler_product 1 = 1 := by
        exact partial_euler_product_one
      _ = (Real.log 3)⁻¹ * Real.log 3 := by field_simp
      _ ≤ C * Real.log 3 := mul_le_mul_of_nonneg_right hsmall hlog3.le
    convert hfinal using 1 <;> norm_num

/-- The same natural-endpoint bound in the `log (2h)` form used in the
small-prime/large-prime split. -/
theorem partial_euler_product_le_log_two_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 1 ≤ h →
      partial_euler_product h ≤ C * Real.log (2 * (h : ℝ)) := by
  obtain ⟨c, hc, hupper⟩ := weak_mertens_third_upper_all
  let C : ℝ := max c (Real.log 2)⁻¹
  have hC : 0 < C := hc.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro h hh
  by_cases hh2 : 2 ≤ h
  · have hh2R : (2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh2
    have hprod : 0 ≤ partial_euler_product h :=
      (by norm_num : (0 : ℝ) ≤ 1).trans partial_euler_trivial_lower_bound
    have hlog : 0 ≤ Real.log (h : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ h by omega))
    have hsource :
        partial_euler_product h ≤ c * Real.log (h : ℝ) := by
      simpa [Real.norm_of_nonneg hprod, Real.norm_of_nonneg hlog] using
        hupper (h : ℝ) hh2R
    have hlog_mono : Real.log (h : ℝ) ≤ Real.log (2 * (h : ℝ)) := by
      apply Real.log_le_log
      · positivity
      · nlinarith
    calc
      partial_euler_product h ≤ c * Real.log (h : ℝ) := hsource
      _ ≤ C * Real.log (h : ℝ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hlog
      _ ≤ C * Real.log (2 * (h : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_mono hC.le
  · have heq : h = 1 := by omega
    subst h
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hsmall : (Real.log 2)⁻¹ ≤ C := le_max_right _ _
    have hfinal : partial_euler_product 1 ≤ C * Real.log 2 := calc
      partial_euler_product 1 = 1 := by
        exact partial_euler_product_one
      _ = (Real.log 2)⁻¹ * Real.log 2 := by field_simp
      _ ≤ C * Real.log 2 := mul_le_mul_of_nonneg_right hsmall hlog2.le
    simpa using hfinal

/-- Each Euler factor belonging to a prime is at least one. -/
lemma one_le_inverse_prime_factor {p : ℕ} (hp : p.Prime) :
    (1 : ℝ) ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ :=
    sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  exact (one_le_inv₀ hpos).2 (by
    nlinarith [inv_nonneg.2 (show (0 : ℝ) ≤ p by positivity)])

/-- The inverse product over the prime factors of a smooth integer is at
most the complete inverse prime product at the same endpoint. -/
theorem primeFactors_inverse_product_le_partial_euler_product
    {s h : ℕ} (hsmooth : ∀ p ∈ s.primeFactors, p ≤ h) :
    (∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹) ≤
      partial_euler_product h := by
  classical
  rw [partial_euler_product]
  apply Finset.prod_le_prod_of_subset_of_one_le
  · intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpPrime.one_le, hsmooth p hp⟩, hpPrime⟩
  · intro p hp
    exact (one_le_inverse_prime_factor
      (Nat.prime_of_mem_primeFactors hp)).trans' (by norm_num)
  · intro p hp _
    exact one_le_inverse_prime_factor (Finset.mem_filter.mp hp).2

/-- A powered form of the uniform complete-product bound.  It is convenient
when a fixed power of `Pₛ⁻¹` occurs after a moment expansion. -/
theorem partial_euler_product_pow_le_log_two_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ h k : ℕ, 1 ≤ h →
      (partial_euler_product h) ^ k ≤
        (C * Real.log (2 * (h : ℝ))) ^ k := by
  obtain ⟨C, hC, hbound⟩ := partial_euler_product_le_log_two_mul
  refine ⟨C, hC, ?_⟩
  intro h k hh
  exact pow_le_pow_left₀
    ((by norm_num : (0 : ℝ) ≤ 1).trans partial_euler_trivial_lower_bound)
    (hbound h hh) k

/-- Smoothness bounds the reciprocal totient density.  This is the
division-free form useful in moment arguments: it says
`s / φ(s) ≪ log (2h)` after multiplying through by `φ(s)`.

Squarefreeness is not needed for this consequence, because the totient
density depends only on the prime factors. -/
theorem exists_smooth_le_log_mul_totient :
    ∃ C : ℝ, 0 < C ∧ ∀ {s h : ℕ}, 0 < s → 1 ≤ h →
      (∀ p ∈ s.primeFactors, p ≤ h) →
      (s : ℝ) ≤ C * Real.log (2 * (h : ℝ)) * (s.totient : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := partial_euler_product_le_log_two_mul
  refine ⟨C, hC, ?_⟩
  intro s h hs hh hsmooth
  let D : ℝ := ∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹)
  have hDpos : 0 < D := by
    dsimp [D]
    exact Finset.prod_pos fun p hp ↦ by
      have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
      exact sub_pos_of_lt (inv_lt_one_of_one_lt₀ hp1)
  have hinv : D⁻¹ ≤ C * Real.log (2 * (h : ℝ)) := by
    have hsub := primeFactors_inverse_product_le_partial_euler_product hsmooth
    have hcomplete := hbound h hh
    change (∏ p ∈ s.primeFactors, (1 - (p : ℝ)⁻¹))⁻¹ ≤
      C * Real.log (2 * (h : ℝ))
    rw [← Finset.prod_inv_distrib]
    exact hsub.trans hcomplete
  have hphi : (s.totient : ℝ) = (s : ℝ) * D := by
    have hphiQ := congrArg (fun q : ℚ ↦ (q : ℝ))
      (Nat.totient_eq_mul_prod_factors s)
    simpa [D, Rat.cast_prod] using hphiQ
  calc
    (s : ℝ) = D⁻¹ * (s.totient : ℝ) := by
      rw [hphi]
      field_simp [hDpos.ne']
    _ ≤ (C * Real.log (2 * (h : ℝ))) * (s.totient : ℝ) :=
      mul_le_mul_of_nonneg_right hinv (Nat.cast_nonneg _)

end Erdos220
