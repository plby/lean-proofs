import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.SumPrimeReciprocals
import Wikipedia.GreenTao.Sieve.GoodPrimeAffineRank

/-!
# Euler-product control from square-decaying local errors

The good-prime calculation for the Green--Tao linear-forms system produces
local factors of the form `1 + O(p⁻²)`, outside a finite exceptional set.
This file packages the analytic consequence which is independent of the
particular local-factor formula.

The series of reciprocal prime squares is summable.  Consequently a local
factor with error at most `C / p²` has an absolutely summable error, its
Euler product is multipliable, every finite partial product has an explicit
exponential error bound, and products supported sufficiently far out in the
prime tail are arbitrarily close to one.  A masked version records the
standard operation of replacing finitely many exceptional local factors by
one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Reciprocal squares are summable over the subtype of natural primes. -/
theorem summable_prime_inv_sq :
    Summable
      (fun p : Nat.Primes =>
        (1 : ℝ) / (p : ℝ) ^ 2) := by
  have h :
      Summable
        (fun p : Nat.Primes =>
          (p : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine h.congr fun p => ?_
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [one_div]

/-- Uniform square-decay control for a family of real local factors. -/
def HasPrimeSquareError
    (C : ℝ) (localFactor : Nat.Primes → ℝ) : Prop :=
  0 ≤ C ∧
    ∀ p, |localFactor p - 1| ≤ C / (p : ℝ) ^ 2

namespace HasPrimeSquareError

theorem constant_nonneg
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor) :
    0 ≤ C :=
  h.1

theorem error_le
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor)
    (p : Nat.Primes) :
    |localFactor p - 1| ≤ C / (p : ℝ) ^ 2 :=
  h.2 p

/-- The square-decay majorant itself is summable. -/
theorem summable_majorant
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (_h : HasPrimeSquareError C localFactor) :
    Summable
      (fun p : Nat.Primes =>
        C / (p : ℝ) ^ 2) := by
  simpa [div_eq_mul_inv] using
    summable_prime_inv_sq.mul_left C

/-- The absolute local errors form a summable series. -/
theorem summable_abs_error
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor) :
    Summable
      (fun p : Nat.Primes =>
        |localFactor p - 1|) := by
  exact Summable.of_nonneg_of_le
    (fun _ => abs_nonneg _)
    h.error_le
    h.summable_majorant

/-- Norm-valued form used by Mathlib's infinite-product API. -/
theorem summable_norm_error
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor) :
    Summable
      (fun p : Nat.Primes =>
        ‖localFactor p - 1‖) := by
  simpa [Real.norm_eq_abs] using h.summable_abs_error

/-- A square-decaying family of local factors has a convergent unordered
Euler product. -/
theorem multipliable
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor) :
    Multipliable localFactor := by
  have hm :=
    multipliable_one_add_of_summable
      (f := fun p : Nat.Primes => localFactor p - 1)
      h.summable_norm_error
  have heq :
      (fun p : Nat.Primes =>
        1 + (localFactor p - 1)) =
        localFactor := by
    funext p
    ring
  rw [heq] at hm
  exact hm

/-- Explicit finite-product error bound obtained by expanding around one
and applying `1 + x ≤ exp x`. -/
theorem abs_finsetProd_sub_one_le
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor)
    (s : Finset Nat.Primes) :
    |(∏ p ∈ s, localFactor p) - 1| ≤
      Real.exp
          (∑ p ∈ s, C / (p : ℝ) ^ 2) -
        1 := by
  calc
    |(∏ p ∈ s, localFactor p) - 1| ≤
        Real.exp
            (∑ p ∈ s, |localFactor p - 1|) -
          1 := by
      have hbase :=
        s.norm_prod_one_add_sub_one_le
          (fun p : Nat.Primes => localFactor p - 1)
      have heq :
          (fun p : Nat.Primes =>
            1 + (localFactor p - 1)) =
            localFactor := by
        funext p
        ring
      rw [heq] at hbase
      simpa only [Real.norm_eq_abs] using hbase
    _ ≤
        Real.exp
            (∑ p ∈ s, C / (p : ℝ) ^ 2) -
          1 := by
      apply sub_le_sub_right
      apply Real.exp_le_exp.mpr
      exact Finset.sum_le_sum fun p _ => h.error_le p

/-- The preceding finite-product estimate is uniform in the finite set:
the exponent can be replaced by the full convergent prime-square series. -/
theorem abs_finsetProd_sub_one_le_tsum
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor)
    (s : Finset Nat.Primes) :
    |(∏ p ∈ s, localFactor p) - 1| ≤
      Real.exp
          (∑' p : Nat.Primes,
            C / (p : ℝ) ^ 2) -
        1 := by
  refine h.abs_finsetProd_sub_one_le s |>.trans ?_
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  exact h.summable_majorant.sum_le_tsum s fun p _ => by
    exact div_nonneg h.constant_nonneg (sq_nonneg (p : ℝ))

/-- Products over a sufficiently remote finite collection of primes are
arbitrarily close to one.  This is the Cauchy-tail estimate needed when a
finite local calculation is passed to an Euler product. -/
theorem exists_tail_finsetProd_close_to_one
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset Nat.Primes,
      ∀ t : Finset Nat.Primes, Disjoint t s →
        |(∏ p ∈ t, localFactor p) - 1| < ε := by
  obtain ⟨s, hs⟩ :=
    prod_vanishing_of_summable_norm
      (f := fun p : Nat.Primes => localFactor p - 1)
      h.summable_norm_error hε
  refine ⟨s, fun t ht => ?_⟩
  have htail := hs t ht
  have heq :
      (fun p : Nat.Primes =>
        1 + (localFactor p - 1)) =
        localFactor := by
    funext p
    ring
  rw [heq] at htail
  simpa only [Real.norm_eq_abs] using htail

/-- If no local factor vanishes, neither does the resulting Euler product. -/
theorem tprod_ne_zero
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (h : HasPrimeSquareError C localFactor)
    (hnonzero : ∀ p, localFactor p ≠ 0) :
    (∏' p : Nat.Primes, localFactor p) ≠ 0 := by
  have hprod :=
    tprod_one_add_ne_zero_of_summable
      (f := fun p : Nat.Primes => localFactor p - 1)
      (fun p => by
        rw [show 1 + (localFactor p - 1) =
          localFactor p by ring]
        exact hnonzero p)
      h.summable_norm_error
  have heq :
      (fun p : Nat.Primes =>
        1 + (localFactor p - 1)) =
        localFactor := by
    funext p
    ring
  rw [heq] at hprod
  exact hprod

end HasPrimeSquareError

/-! ## Removing finitely many exceptional primes -/

/-- Replace the local factors in a finite exceptional set by one. -/
def maskedPrimeLocalFactor
    (bad : Finset Nat.Primes)
    (localFactor : Nat.Primes → ℝ) :
    Nat.Primes → ℝ :=
  fun p => if p ∈ bad then 1 else localFactor p

@[simp]
theorem maskedPrimeLocalFactor_of_mem
    {bad : Finset Nat.Primes}
    {localFactor : Nat.Primes → ℝ}
    {p : Nat.Primes} (hp : p ∈ bad) :
    maskedPrimeLocalFactor bad localFactor p = 1 := by
  simp [maskedPrimeLocalFactor, hp]

@[simp]
theorem maskedPrimeLocalFactor_of_not_mem
    {bad : Finset Nat.Primes}
    {localFactor : Nat.Primes → ℝ}
    {p : Nat.Primes} (hp : p ∉ bad) :
    maskedPrimeLocalFactor bad localFactor p =
      localFactor p := by
  simp [maskedPrimeLocalFactor, hp]

/-- Square-decay outside a finite exceptional set becomes global
square-decay after masking those exceptional factors. -/
theorem hasPrimeSquareError_masked
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (bad : Finset Nat.Primes)
    (hC : 0 ≤ C)
    (herror :
      ∀ p, p ∉ bad →
        |localFactor p - 1| ≤ C / (p : ℝ) ^ 2) :
    HasPrimeSquareError C
      (maskedPrimeLocalFactor bad localFactor) := by
  refine ⟨hC, fun p => ?_⟩
  by_cases hp : p ∈ bad
  · rw [maskedPrimeLocalFactor_of_mem hp]
    norm_num
    exact div_nonneg hC (sq_nonneg (p : ℝ))
  · simpa [maskedPrimeLocalFactor, hp] using herror p hp

/-- On a finite set disjoint from the exceptional primes, masking does not
alter the finite Euler product. -/
theorem finsetProd_maskedPrimeLocalFactor_eq
    {bad s : Finset Nat.Primes}
    {localFactor : Nat.Primes → ℝ}
    (hdisjoint : Disjoint s bad) :
    (∏ p ∈ s, maskedPrimeLocalFactor bad localFactor p) =
      ∏ p ∈ s, localFactor p := by
  apply Finset.prod_congr rfl
  intro p hp
  exact maskedPrimeLocalFactor_of_not_mem
    (Finset.disjoint_left.mp hdisjoint hp)

/-! ## Masking by a numerical cutoff -/

/-- Replace every prime at most `B` by the neutral local factor.  This form
is convenient when the exceptional set is specified by an explicit natural
bound rather than an enumerated `Finset`. -/
def boundedMaskedPrimeLocalFactor
    (B : ℕ) (localFactor : Nat.Primes → ℝ) :
    Nat.Primes → ℝ :=
  fun p => if (p : ℕ) ≤ B then 1 else localFactor p

@[simp]
theorem boundedMaskedPrimeLocalFactor_of_le
    {B : ℕ} {localFactor : Nat.Primes → ℝ}
    {p : Nat.Primes} (hp : (p : ℕ) ≤ B) :
    boundedMaskedPrimeLocalFactor B localFactor p = 1 := by
  simp [boundedMaskedPrimeLocalFactor, hp]

@[simp]
theorem boundedMaskedPrimeLocalFactor_of_lt
    {B : ℕ} {localFactor : Nat.Primes → ℝ}
    {p : Nat.Primes} (hp : B < (p : ℕ)) :
    boundedMaskedPrimeLocalFactor B localFactor p =
      localFactor p := by
  have hnot : ¬(p : ℕ) ≤ B :=
    Nat.not_le.mpr hp
  simp [boundedMaskedPrimeLocalFactor, hnot]

/-- A square error estimate valid above an explicit cutoff becomes a global
estimate after the bounded mask is applied. -/
theorem hasPrimeSquareError_boundedMasked
    {C : ℝ} {localFactor : Nat.Primes → ℝ}
    (B : ℕ) (hC : 0 ≤ C)
    (herror :
      ∀ p : Nat.Primes, B < (p : ℕ) →
        |localFactor p - 1| ≤ C / (p : ℝ) ^ 2) :
    HasPrimeSquareError C
      (boundedMaskedPrimeLocalFactor B localFactor) := by
  refine ⟨hC, fun p => ?_⟩
  by_cases hp : (p : ℕ) ≤ B
  · rw [boundedMaskedPrimeLocalFactor_of_le hp]
    norm_num
    exact div_nonneg hC (sq_nonneg (p : ℝ))
  · rw [boundedMaskedPrimeLocalFactor_of_lt
      (Nat.lt_of_not_ge hp)]
    exact herror p (Nat.lt_of_not_ge hp)

end Wikipedia.SzemeredisTheorem
