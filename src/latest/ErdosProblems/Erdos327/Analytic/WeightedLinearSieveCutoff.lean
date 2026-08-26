import ErdosProblems.Erdos327.Analytic.EulerProductBounds
import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveFinite
import Mathlib.Data.Nat.Choose.Sum

/-!
# Explicit cutoff bounds for the finite weighted sieve

This file removes the remaining subset-dependent quantities from the
finite Bonferroni/CRT bound.  If every prime in `P` is at most `z`,
then a `k`-element subset has modulus at most `z^k`; its contribution
can consequently be counted using `Nat.choose P.card k`.
-/

namespace Erdos327.Analytic

open scoped BigOperators

open Finset

/-- A subset modulus is at most `z^|T|` when all ambient primes are at
most `z`. -/
theorem subsetModulus_le_pow
    {P : Finset ℕ} {z : ℕ}
    (hpz : ∀ p ∈ P, p ≤ z) (T : Finset P) :
    subsetModulus T ≤ z ^ T.card := by
  unfold subsetModulus
  calc
    (∏ p : T, (((p : T) : P) : ℕ)) ≤
        ∏ _p : T, z := by
      exact Finset.prod_le_prod' fun p _ ↦
        hpz p.val.val p.val.property
    _ = z ^ T.card := by simp

/-- Eliminate `powersetCard` and `subsetModulus` from the boundary
sum, retaining the exact binomial count in each degree. -/
theorem subsetBoundarySum_le_choose
    {P : Finset ℕ} {z X m : ℕ}
    (hpz : ∀ p ∈ P, p ≤ z) :
    (∑ k ∈ range m,
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T)) ≤
      ∑ k ∈ range m,
        (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ k * (9 * (X : ℝ) + (z : ℝ) ^ k)) := by
  apply sum_le_sum
  intro k _
  calc
    (∑ T ∈ (univ : Finset P).powersetCard k,
        (3 : ℝ) ^ T.card *
          (9 * (X : ℝ) + subsetModulus T)) ≤
      ∑ _T ∈ (univ : Finset P).powersetCard k,
        (3 : ℝ) ^ k *
          (9 * (X : ℝ) + (z : ℝ) ^ k) := by
      apply sum_le_sum
      intro T hT
      have hcard : T.card = k := (mem_powersetCard.mp hT).2
      have hmodNat := subsetModulus_le_pow hpz T
      have hmod :
          (subsetModulus T : ℝ) ≤ (z : ℝ) ^ k := by
        rw [← hcard]
        exact_mod_cast hmodNat
      rw [hcard]
      gcongr
    _ = (Nat.choose P.card k : ℝ) *
        ((3 : ℝ) ^ k * (9 * (X : ℝ) + (z : ℝ) ^ k)) := by
      rw [sum_const]
      simp [card_powersetCard]

/-- Any initial segment of a binomial row has mass at most `2^n`. -/
theorem sum_choose_range_le_two_pow (n m : ℕ) :
    (∑ k ∈ range m, Nat.choose n k) ≤ 2 ^ n := by
  by_cases hm : m ≤ n + 1
  · calc
      (∑ k ∈ range m, Nat.choose n k) ≤
          ∑ k ∈ range (n + 1), Nat.choose n k := by
        exact sum_le_sum_of_subset_of_nonneg
          (range_mono hm) (fun _ _ _ ↦ Nat.zero_le _)
      _ = 2 ^ n := Nat.sum_range_choose n
  · have hnm : n + 1 ≤ m := by omega
    calc
      (∑ k ∈ range m, Nat.choose n k) =
          ∑ k ∈ range (n + 1), Nat.choose n k := by
        symm
        apply sum_subset (range_mono hnm)
        intro k hkm hk
        exact Nat.choose_eq_zero_of_lt (by
          rw [mem_range] at hkm
          rw [mem_range] at hk
          omega)
      _ = 2 ^ n := Nat.sum_range_choose n
      _ ≤ 2 ^ n := le_rfl

/-- Coarse closed-form boundary bound with no remaining finite subset
or degree sums. -/
theorem subsetBoundarySum_le_closed
    {P : Finset ℕ} {z X R : ℕ}
    (hz : 1 ≤ z) (hpz : ∀ p ∈ P, p ≤ z) :
    (∑ k ∈ range (2 * R + 1),
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T)) ≤
      (2 : ℝ) ^ P.card * (3 : ℝ) ^ (2 * R) *
        (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  have hchoose := subsetBoundarySum_le_choose
    (P := P) (z := z) (X := X) (m := 2 * R + 1) hpz
  have hterm (k : ℕ) (hk : k ∈ range (2 * R + 1)) :
      (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ k * (9 * (X : ℝ) + (z : ℝ) ^ k)) ≤
        (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ (2 * R) *
            (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))) := by
    have hkR : k ≤ 2 * R := by
      rw [mem_range] at hk
      omega
    have h3pow :
        (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (2 * R) :=
      pow_le_pow_right₀ (by norm_num) hkR
    have hzpow :
        (z : ℝ) ^ k ≤ (z : ℝ) ^ (2 * R) :=
      pow_le_pow_right₀ (by exact_mod_cast hz) hkR
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h3pow (add_le_add le_rfl hzpow)
        (by positivity) (by positivity))
      (by positivity)
  calc
    (∑ k ∈ range (2 * R + 1),
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T)) ≤
      ∑ k ∈ range (2 * R + 1),
        (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ k * (9 * (X : ℝ) + (z : ℝ) ^ k)) :=
      hchoose
    _ ≤ ∑ k ∈ range (2 * R + 1),
        (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ (2 * R) *
            (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))) :=
      sum_le_sum fun k hk ↦ hterm k hk
    _ = (∑ k ∈ range (2 * R + 1),
          (Nat.choose P.card k : ℝ)) *
        ((3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))) := by
      rw [sum_mul]
    _ ≤ (2 : ℝ) ^ P.card *
        ((3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))) := by
      gcongr
      exact_mod_cast sum_choose_range_le_two_pow P.card (2 * R + 1)
    _ = _ := by ring

/-- If `z^(2R) ≤ X`, the complete subset boundary is at most
`10 X · 2^|P| · 3^(2R)`. -/
theorem subsetBoundarySum_le_closed_of_pow_le
    {P : Finset ℕ} {z X R : ℕ}
    (hz : 1 ≤ z) (hpz : ∀ p ∈ P, p ≤ z)
    (hzX : z ^ (2 * R) ≤ X) :
    (∑ k ∈ range (2 * R + 1),
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T)) ≤
      10 * (X : ℝ) * (2 : ℝ) ^ P.card *
        (3 : ℝ) ^ (2 * R) := by
  calc
    _ ≤ (2 : ℝ) ^ P.card * (3 : ℝ) ^ (2 * R) *
        (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) :=
      subsetBoundarySum_le_closed hz hpz
    _ ≤ (2 : ℝ) ^ P.card * (3 : ℝ) ^ (2 * R) *
        (10 * (X : ℝ)) := by
      gcongr
      have hzXReal :
          (z : ℝ) ^ (2 * R) ≤ (X : ℝ) := by
        exact_mod_cast hzX
      linarith
    _ = _ := by ring

/-- If the available local estimate is `μₚ ≤ 3/p`, then the total
local loss is controlled by the reciprocal-prime mass up to the
cutoff. -/
theorem sum_localLossMean_le_three_mul_primeInvSum
    {P : Finset ℕ} {z : ℕ}
    [∀ p : P, NeZero (p : ℕ)]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hPz : P ⊆ Nat.primesLE z)
    (hmean : ∀ p : P,
      localLossMean ell p ≤ 3 / (p : ℝ)) :
    (∑ p : P, localLossMean ell p) ≤
      3 * primeInvSum z := by
  calc
    (∑ p : P, localLossMean ell p) ≤
        ∑ p : P, 3 / (p : ℝ) :=
      sum_le_sum fun p _ ↦ hmean p
    _ = ∑ p ∈ P, 3 / (p : ℝ) := by
      simpa using
        (sum_coe_sort P (fun p : ℕ ↦ 3 / (p : ℝ)))
    _ = 3 * ∑ p ∈ P, 1 / (p : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    _ ≤ 3 * ∑ p ∈ Nat.primesLE z, 1 / (p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum_of_subset_of_nonneg hPz
        (fun _ _ _ ↦ by positivity)
    _ = 3 * primeInvSum z := by
      rfl

/-- The factorial tail inherits the explicit reciprocal-prime bound.
This is stated separately so downstream applications can use it
without reopening the finite sieve argument. -/
theorem localLossFactorialTail_le_primeInvSum
    {P : Finset ℕ} {z R : ℕ}
    [∀ p : P, NeZero (p : ℕ)]
    (ell : ∀ p : P, ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hmean0 : ∀ p : P, 0 ≤ localLossMean ell p)
    (hPz : P ⊆ Nat.primesLE z)
    (hmean : ∀ p : P,
      localLossMean ell p ≤ 3 / (p : ℝ)) :
    (∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
          ((2 * R + 1).factorial : ℝ) ≤
      (3 * primeInvSum z) ^ (2 * R + 1) /
          ((2 * R + 1).factorial : ℝ) := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀
  · exact sum_nonneg fun p _ ↦ hmean0 p
  · exact sum_localLossMean_le_three_mul_primeInvSum ell hPz hmean

/-- Fully explicit finite weighted-sieve bound: both the factorial
tail and the subset boundary are expressed only through the cutoff
parameters. -/
theorem finiteWeightBoxSum_le_primeInvSum_add_closed_boundary
    {P : Finset ℕ} {z : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (w ell : ∀ p : P,
      ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hcomplement : ∀ (p : P) u, w p u + ell p u = 1)
    (hell0 : ∀ (p : P) u, 0 ≤ ell p u)
    (hell1 : ∀ (p : P) u, ell p u ≤ 1)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ))
    (hPz : P ⊆ Nat.primesLE z)
    (hmean : ∀ p : P,
      localLossMean ell p ≤ 3 / (p : ℝ))
    (hz : 1 ≤ z) (X R : ℕ) :
    finiteWeightBoxSum w X ≤
      8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        (2 : ℝ) ^ P.card * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  have hpz : ∀ p ∈ P, p ≤ z := fun p hp ↦
    (Nat.mem_primesLE.mp (hPz hp)).1
  have hmean0 : ∀ p : P, 0 ≤ localLossMean ell p := fun p ↦
    (localLossMean_nonneg_le_one
      hprime ell hell0 hell1 p).1
  have htail :=
    localLossFactorialTail_le_primeInvSum
      ell hmean0 hPz hmean (R := R)
  have htailScaled :
      8 * (X : ℝ) ^ 2 *
          ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) ≤
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  have hboundary :=
    subsetBoundarySum_le_closed
      (P := P) (X := X) (R := R) hz hpz
  calc
    finiteWeightBoxSum w X ≤
        8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
          8 * (X : ℝ) ^ 2 *
            ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
              ((2 * R + 1).factorial : ℝ)) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) :=
      finiteWeightBoxSum_le_main_add_tail_add_boundary
        hprime w ell hcomplement hell0 hell1 hsupport X R
    _ ≤ _ :=
      add_le_add (add_le_add le_rfl htailScaled) hboundary

/-- Under `z^(2R) ≤ X`, the boundary contribution simplifies to
`10 X · 2^|P| · 3^(2R)`. -/
theorem finiteWeightBoxSum_le_primeInvSum_add_closed_boundary_of_pow_le
    {P : Finset ℕ} {z : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (w ell : ∀ p : P,
      ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hcomplement : ∀ (p : P) u, w p u + ell p u = 1)
    (hell0 : ∀ (p : P) u, 0 ≤ ell p u)
    (hell1 : ∀ (p : P) u, ell p u ≤ 1)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ))
    (hPz : P ⊆ Nat.primesLE z)
    (hmean : ∀ p : P,
      localLossMean ell p ≤ 3 / (p : ℝ))
    (hz : 1 ≤ z) (X R : ℕ)
    (hzX : z ^ (2 * R) ≤ X) :
    finiteWeightBoxSum w X ≤
      8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        10 * (X : ℝ) * (2 : ℝ) ^ P.card *
          (3 : ℝ) ^ (2 * R) := by
  have hpz : ∀ p ∈ P, p ≤ z := fun p hp ↦
    (Nat.mem_primesLE.mp (hPz hp)).1
  have hmean0 : ∀ p : P, 0 ≤ localLossMean ell p := fun p ↦
    (localLossMean_nonneg_le_one
      hprime ell hell0 hell1 p).1
  have htail :=
    localLossFactorialTail_le_primeInvSum
      ell hmean0 hPz hmean (R := R)
  have htailScaled :
      8 * (X : ℝ) ^ 2 *
          ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) ≤
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  have hboundary :=
    subsetBoundarySum_le_closed_of_pow_le
      (P := P) hz hpz hzX
  calc
    finiteWeightBoxSum w X ≤
        8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
          8 * (X : ℝ) ^ 2 *
            ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
              ((2 * R + 1).factorial : ℝ)) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) :=
      finiteWeightBoxSum_le_main_add_tail_add_boundary
        hprime w ell hcomplement hell0 hell1 hsupport X R
    _ ≤ _ :=
      add_le_add (add_le_add le_rfl htailScaled) hboundary

end Erdos327.Analytic
