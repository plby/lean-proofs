module

public import CebotarevDensity.NumberFieldEulerProduct

/-!
# Prime-ideal von Mangoldt coefficients

This file packages the elementary finite definitions used by the prime ideal theorem.  For a
number field `K`, the coefficient at `n` is

`\sum_{N 𝔭 ^ m = n, m ≥ 1} log (N 𝔭)`,

where `𝔭` runs through the nonzero prime ideals of `𝓞 K`.  Both indexing sets are explicitly
bounded: a contributing prime ideal has norm at most `n`, and a contributing exponent is in
`[1,n]`.  Thus the definition is a finite sum and needs no convergence convention.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace Chebotarev

section WeightedDefs

variable (K : Type*) [Field K] [NumberField K]

/-- The set of nonzero prime ideals of `𝓞 K` whose absolute norm is at most `n`. -/
def primeIdealsUpToSet (n : ℕ) : Set (Ideal (𝓞 K)) :=
  {𝔭 | 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ n}

/-- There are only finitely many nonzero prime ideals of norm at most `n`. -/
theorem primeIdealsUpToSet_finite (n : ℕ) : (primeIdealsUpToSet K n).Finite :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) n).subset fun _ h𝔭 ↦ h𝔭.2.2

/-- The finite set of nonzero prime ideals of norm at most `n`. -/
noncomputable def primeIdealsUpTo (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (primeIdealsUpToSet_finite K n).toFinset

@[simp] theorem mem_primeIdealsUpTo {n : ℕ} {𝔭 : Ideal (𝓞 K)} :
    𝔭 ∈ primeIdealsUpTo K n ↔
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ Ideal.absNorm 𝔭 ≤ n := by
  simp [primeIdealsUpTo, primeIdealsUpToSet]

/-- A nonzero prime ideal in a number ring has absolute norm at least two. -/
theorem two_le_absNorm_of_mem_primeIdealsUpTo {n : ℕ} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primeIdealsUpTo K n) :
    2 ≤ Ideal.absNorm 𝔭 := by
  have hp := (mem_primeIdealsUpTo (K := K)).mp h𝔭
  have hne0 : Ideal.absNorm 𝔭 ≠ 0 := fun h ↦ hp.2.1 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭 ≠ 1 := fun h ↦ hp.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- The logarithmic weight of a prime ideal in `primeIdealsUpTo` is nonnegative. -/
theorem log_absNorm_nonneg_of_mem_primeIdealsUpTo {n : ℕ} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primeIdealsUpTo K n) :
    0 ≤ Real.log (Ideal.absNorm 𝔭 : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast (one_le_two.trans (two_le_absNorm_of_mem_primeIdealsUpTo K h𝔭))

/-- The number-field von Mangoldt coefficient at `n`:
`\sum_{𝔭,m≥1; (N𝔭)^m=n} log(N𝔭)`.

The explicit bounds do not discard any term: if `(N𝔭)^m = n` and `m ≥ 1`, then `N𝔭 ≤ n`,
while `N𝔭 ≥ 2` implies `m ≤ n`. -/
noncomputable def primeIdealVonMangoldtCoeff (n : ℕ) : ℝ :=
  ∑ 𝔭 ∈ primeIdealsUpTo K n,
    ∑ m ∈ Finset.Icc 1 n,
      if Ideal.absNorm 𝔭 ^ m = n then Real.log (Ideal.absNorm 𝔭 : ℝ) else 0

/-- The defining finite prime-power expansion. -/
theorem primeIdealVonMangoldtCoeff_eq (n : ℕ) :
    primeIdealVonMangoldtCoeff K n =
      ∑ 𝔭 ∈ primeIdealsUpTo K n,
        ∑ m ∈ Finset.Icc 1 n,
          if Ideal.absNorm 𝔭 ^ m = n then Real.log (Ideal.absNorm 𝔭 : ℝ) else 0 :=
  rfl

/-- Every summand occurring in the defining double sum is nonnegative. -/
theorem primeIdealVonMangoldtSummand_nonneg {n m : ℕ} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primeIdealsUpTo K n) :
    0 ≤ (if Ideal.absNorm 𝔭 ^ m = n then Real.log (Ideal.absNorm 𝔭 : ℝ) else 0) := by
  split_ifs
  · exact log_absNorm_nonneg_of_mem_primeIdealsUpTo K h𝔭
  · exact le_rfl

/-- The number-field von Mangoldt coefficient is nonnegative. -/
theorem primeIdealVonMangoldtCoeff_nonneg (n : ℕ) :
    0 ≤ primeIdealVonMangoldtCoeff K n := by
  rw [primeIdealVonMangoldtCoeff_eq]
  exact Finset.sum_nonneg fun 𝔭 h𝔭 ↦
    Finset.sum_nonneg fun m _ ↦ primeIdealVonMangoldtSummand_nonneg K h𝔭

@[simp] theorem primeIdealVonMangoldtCoeff_zero :
    primeIdealVonMangoldtCoeff K 0 = 0 := by
  simp [primeIdealVonMangoldtCoeff]

@[simp] theorem primeIdealsUpTo_one : primeIdealsUpTo K 1 = ∅ := by
  ext 𝔭
  constructor
  · intro h𝔭
    have := two_le_absNorm_of_mem_primeIdealsUpTo K h𝔭
    have := ((mem_primeIdealsUpTo (K := K)).mp h𝔭).2.2
    omega
  · simp

@[simp] theorem primeIdealVonMangoldtCoeff_one :
    primeIdealVonMangoldtCoeff K 1 = 0 := by
  simp [primeIdealVonMangoldtCoeff]

/-- A nonzero coefficient can only occur at an integer at least two. -/
theorem two_le_of_primeIdealVonMangoldtCoeff_ne_zero {n : ℕ}
    (hn : primeIdealVonMangoldtCoeff K n ≠ 0) :
    2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp at hn
  · exact hge

/-- If an indexed prime-power term contributes at `n`, then its prime norm lies in `[2,n]`. -/
theorem absNorm_mem_interval_of_primePower_eq {n m : ℕ} {𝔭 : Ideal (𝓞 K)}
    (h𝔭 : 𝔭 ∈ primeIdealsUpTo K n) (_hm : m ∈ Finset.Icc 1 n)
    (_hpow : Ideal.absNorm 𝔭 ^ m = n) :
    2 ≤ Ideal.absNorm 𝔭 ∧ Ideal.absNorm 𝔭 ≤ n := by
  exact ⟨two_le_absNorm_of_mem_primeIdealsUpTo K h𝔭,
    ((mem_primeIdealsUpTo (K := K)).mp h𝔭).2.2⟩

/-- The finite cumulative prime-ideal von Mangoldt sum through `x`.  The `0`-coefficient is zero,
so this is exactly the sum over `1 ≤ n ≤ x`. -/
noncomputable def primeIdealChebyshev (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1), primeIdealVonMangoldtCoeff K n

theorem primeIdealChebyshev_nonneg (x : ℕ) : 0 ≤ primeIdealChebyshev K x := by
  rw [primeIdealChebyshev]
  exact Finset.sum_nonneg fun n _ ↦ primeIdealVonMangoldtCoeff_nonneg K n

@[simp] theorem primeIdealChebyshev_zero : primeIdealChebyshev K 0 = 0 := by
  simp [primeIdealChebyshev]

/-- Adding the next endpoint adds precisely its von Mangoldt coefficient. -/
theorem primeIdealChebyshev_succ (x : ℕ) :
    primeIdealChebyshev K (x + 1) =
      primeIdealChebyshev K x + primeIdealVonMangoldtCoeff K (x + 1) := by
  simp [primeIdealChebyshev, Finset.sum_range_succ]

/-- The cumulative prime-ideal von Mangoldt sum is monotone. -/
theorem primeIdealChebyshev_mono : Monotone (primeIdealChebyshev K) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      rw [primeIdealChebyshev_succ]
      exact le_add_of_nonneg_right (primeIdealVonMangoldtCoeff_nonneg K (b + 1)) |>.trans' ih

end WeightedDefs

end Chebotarev
