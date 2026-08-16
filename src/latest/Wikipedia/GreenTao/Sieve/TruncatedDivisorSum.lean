import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-!
# Smooth truncated divisor sums

The Goldston--Yıldırım majorant is the square of a smoothly truncated
Möbius divisor sum.  This file fixes the normalization and proves the exact
prime-value identity used for pointwise domination of the W-tricked prime
weight.  The later linear-forms estimate is deliberately separated from
these elementary identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-- Smooth truncated divisor sum

`Λ_{χ,R}(n) = log R * ∑_{d ∣ n} μ(d) χ(log d / log R)`.

For the final construction, `χ` is a smooth compactly supported function
with `χ 0 = 1`. -/
noncomputable def smoothTruncatedDivisorSum
    (χ : ℝ → ℝ) (R n : ℕ) : ℝ :=
  Real.log R *
    ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        χ (Real.log d / Real.log R)

/-- The individual Möbius-cutoff term in the truncated divisor sum. -/
noncomputable def smoothDivisorSummand
    (χ : ℝ → ℝ) (R d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) *
    χ (Real.log d / Real.log R)

/-- The truncated divisor sum written using its named summand. -/
theorem smoothTruncatedDivisorSum_eq_sum_smoothDivisorSummand
    (χ : ℝ → ℝ) (R n : ℕ) :
    smoothTruncatedDivisorSum χ R n =
      Real.log R *
        ∑ d ∈ n.divisors, smoothDivisorSummand χ R d :=
  rfl

/-- On a prime, only the divisors `1` and `p` occur.  If the cutoff vanishes
at the prime endpoint, the divisor sum is exactly its `d = 1` term. -/
theorem smoothTruncatedDivisorSum_prime
    (χ : ℝ → ℝ) (R : ℕ) {p : ℕ}
    (hp : p.Prime)
    (hcut : χ (Real.log p / Real.log R) = 0) :
    smoothTruncatedDivisorSum χ R p =
      Real.log R * χ 0 := by
  unfold smoothTruncatedDivisorSum
  rw [hp.divisors]
  apply congrArg (fun t : ℝ => Real.log R * t)
  have h1p : 1 ∉ ({p} : Finset ℕ) := by
    simpa using hp.ne_one.symm
  rw [Finset.sum_insert h1p, Finset.sum_singleton, hcut]
  simp

/-- With the standard normalization `χ 0 = 1`, the truncated divisor sum
equals `log R` on primes beyond the cutoff. -/
theorem smoothTruncatedDivisorSum_prime_of_chi_zero
    (χ : ℝ → ℝ) (R : ℕ) {p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hcut : χ (Real.log p / Real.log R) = 0) :
    smoothTruncatedDivisorSum χ R p = Real.log R := by
  rw [smoothTruncatedDivisorSum_prime χ R hp hcut, hχ0, mul_one]

/-- A cutoff supported below one vanishes at `log p / log R` whenever
`R < p`. -/
theorem smoothCutoff_zero_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hR : 1 < R) (hRp : R < p)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0) :
    χ (Real.log p / Real.log R) = 0 := by
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  apply hχ
  rw [le_div_iff₀ hlogR]
  simpa using
    (Real.log_lt_log
      (by exact_mod_cast (Nat.zero_lt_of_lt hR))
      (by exact_mod_cast hRp)).le

/-- A divisor summand past the cutoff `R` vanishes. -/
@[simp]
theorem smoothDivisorSummand_eq_zero_of_lt
    (χ : ℝ → ℝ) {R d : ℕ}
    (hR : 1 < R) (hRd : R < d)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0) :
    smoothDivisorSummand χ R d = 0 := by
  rw [smoothDivisorSummand,
    smoothCutoff_zero_of_lt χ hR hRd hχ, mul_zero]

/-- Exact support restriction: under the standard support hypothesis on
`χ`, only divisors at most `R` contribute to the truncated divisor sum. -/
theorem smoothTruncatedDivisorSum_eq_filtered_divisors
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (n : ℕ) :
    smoothTruncatedDivisorSum χ R n =
      Real.log R *
        ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
          smoothDivisorSummand χ R d := by
  rw [smoothTruncatedDivisorSum_eq_sum_smoothDivisorSummand]
  apply congrArg (fun t : ℝ ↦ Real.log R * t)
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  apply smoothDivisorSummand_eq_zero_of_lt χ hR
  · exact lt_of_not_ge fun hdR ↦
      hnot (Finset.mem_filter.mpr ⟨hd, hdR⟩)
  · exact hχ

/-- Prime-value identity in the form used later: support of `χ` and
`R < p` discharge the endpoint hypothesis automatically. -/
theorem smoothTruncatedDivisorSum_prime_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hR : 1 < R) (hRp : R < p) :
    smoothTruncatedDivisorSum χ R p = Real.log R :=
  smoothTruncatedDivisorSum_prime_of_chi_zero χ R hp hχ0
    (smoothCutoff_zero_of_lt χ hR hRp hχ)

/-- The nonnegative Selberg square used as the unnormalized majorant. -/
noncomputable def smoothSelbergWeight
    (χ : ℝ → ℝ) (R n : ℕ) : ℝ :=
  smoothTruncatedDivisorSum χ R n ^ 2

theorem smoothSelbergWeight_nonneg
    (χ : ℝ → ℝ) (R n : ℕ) :
    0 ≤ smoothSelbergWeight χ R n :=
  sq_nonneg _

/-- Support-filtered square form of the smooth Selberg weight. -/
theorem smoothSelbergWeight_eq_filtered_divisors_sq
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (n : ℕ) :
    smoothSelbergWeight χ R n =
      (Real.log R *
        ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
          smoothDivisorSummand χ R d) ^ 2 := by
  rw [smoothSelbergWeight,
    smoothTruncatedDivisorSum_eq_filtered_divisors χ hR hχ n]

/-- Finite double-sum expansion of the support-filtered Selberg square. -/
theorem smoothSelbergWeight_eq_filtered_double_sum
    (χ : ℝ → ℝ) {R : ℕ}
    (hR : 1 < R)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (n : ℕ) :
    smoothSelbergWeight χ R n =
      Real.log R ^ 2 *
        ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
          ∑ e ∈ n.divisors.filter (fun e ↦ e ≤ R),
            smoothDivisorSummand χ R d *
              smoothDivisorSummand χ R e := by
  rw [smoothSelbergWeight_eq_filtered_divisors_sq χ hR hχ n]
  calc
    (Real.log R *
        ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
          smoothDivisorSummand χ R d) ^ 2 =
      Real.log R ^ 2 *
        ((∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
            smoothDivisorSummand χ R d) *
          ∑ e ∈ n.divisors.filter (fun e ↦ e ≤ R),
            smoothDivisorSummand χ R e) := by
      ring
    _ = Real.log R ^ 2 *
        ∑ d ∈ n.divisors.filter (fun d ↦ d ≤ R),
          ∑ e ∈ n.divisors.filter (fun e ↦ e ≤ R),
            smoothDivisorSummand χ R d *
              smoothDivisorSummand χ R e := by
      rw [Finset.sum_mul_sum]

theorem smoothSelbergWeight_prime
    (χ : ℝ → ℝ) (R : ℕ) {p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hcut : χ (Real.log p / Real.log R) = 0) :
    smoothSelbergWeight χ R p = Real.log R ^ 2 := by
  rw [smoothSelbergWeight,
    smoothTruncatedDivisorSum_prime_of_chi_zero χ R hp hχ0 hcut]

theorem smoothSelbergWeight_prime_of_lt
    (χ : ℝ → ℝ) {R p : ℕ}
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hR : 1 < R) (hRp : R < p) :
    smoothSelbergWeight χ R p = Real.log R ^ 2 := by
  rw [smoothSelbergWeight,
    smoothTruncatedDivisorSum_prime_of_lt χ hp hχ0 hχ hR hRp]

/-- The standard W-tricked normalization of the Selberg square.  The
positive constant `cχ` will later be the `L²` mass of `χ'`. -/
noncomputable def normalizedSelbergMajorant
    (χ : ℝ → ℝ) (cχ : ℝ) (R W n : ℕ) : ℝ :=
  (W.totient : ℝ) / W *
    smoothSelbergWeight χ R n / (cχ * Real.log R)

theorem normalizedSelbergMajorant_nonneg
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R) (W n : ℕ) :
    0 ≤ normalizedSelbergMajorant χ cχ R W n := by
  unfold normalizedSelbergMajorant
  have hlogR : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hR)
  exact div_nonneg
    (mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (smoothSelbergWeight_nonneg χ R n))
    (mul_nonneg hcχ hlogR)

/-- Exact normalized value on a prime beyond the cutoff. -/
theorem normalizedSelbergMajorant_prime_of_lt
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : cχ ≠ 0)
    {R W p : ℕ} (hR : 1 < R) (hW : 0 < W)
    (hp : p.Prime) (hχ0 : χ 0 = 1)
    (hχ : ∀ x : ℝ, 1 ≤ x → χ x = 0)
    (hRp : R < p) :
    normalizedSelbergMajorant χ cχ R W p =
      (W.totient : ℝ) / W * (Real.log R / cχ) := by
  unfold normalizedSelbergMajorant
  rw [smoothSelbergWeight_prime_of_lt χ hp hχ0 hχ hR hRp]
  have hlogR : Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  have hW0 : (W : ℝ) ≠ 0 := by
    exact_mod_cast hW.ne'
  field_simp [hcχ, hlogR, hW0]

end Wikipedia.SzemeredisTheorem
