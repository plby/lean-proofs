import ErdosProblems.Erdos327.Analytic.FactorCounts
import ErdosProblems.Erdos327.Analytic.PrimeRangeWeight
import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveFinite

/-!
# Integer-to-residue bridge for the weighted three-linear-form sieve

The finite CRT sieve is phrased as a product of local weights on residue
pairs.  This file identifies those weights with squarefree divisibility
weights of the integer linear forms.  It also records the localized
`Ω`-to-`ω` comparison used to pass from the paper's prime-factor weights
to those squarefree products.
-/

namespace Erdos327.Analytic

open Finset
open scoped BigOperators

/-- The finite set of primes in the closed interval `[L, X]`. -/
def primesBetween (L X : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter fun p ↦ L ≤ p

@[simp] theorem mem_primesBetween {L X p : ℕ} :
    p ∈ primesBetween L X ↔ L ≤ p ∧ p ≤ X ∧ p.Prime := by
  simp only [primesBetween, mem_filter, Nat.mem_primesLE]
  aesop

/-- Distinct prime factors of `n` in the closed interval `[L, X]`. -/
def distinctPrimeFactorCountBetween (L X n : ℕ) : ℕ :=
  (n.primeFactors.filter fun p ↦ L ≤ p ∧ p ≤ X).card

/-- Localized distinct prime factors are a sub-multiset of the localized
prime-factor list, so their number is at most the multiplicity count. -/
theorem distinctPrimeFactorCountBetween_le_primeFactorCountBetween
    (L X n : ℕ) :
    distinctPrimeFactorCountBetween L X n ≤
      primeFactorCountBetween L X n := by
  unfold distinctPrimeFactorCountBetween primeFactorCountBetween
  have heq :
      n.primeFactors.filter (fun p ↦ L ≤ p ∧ p ≤ X) =
        (n.primeFactorsList.filter
          (fun p ↦ decide (L ≤ p ∧ p ≤ X))).toFinset := by
    ext p
    simp only [Nat.primeFactors, mem_filter, List.mem_toFinset,
      List.mem_filter, decide_eq_true_eq]
  rw [heq]
  exact (n.primeFactorsList.filter
    (fun p ↦ decide (L ≤ p ∧ p ≤ X))).toFinset_card_le

/-- For a base in `[0,1]`, forgetting repeated prime factors in a fixed
prime interval enlarges the exponential weight. -/
theorem pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (L X n : ℕ) :
    q ^ primeFactorCountBetween L X n ≤
      q ^ distinctPrimeFactorCountBetween L X n :=
  pow_le_pow_of_le_one hq0 hq1
    (distinctPrimeFactorCountBetween_le_primeFactorCountBetween L X n)

/-- The localized distinct-factor count is equivalently the number of
primes in the cutoff set which divide `n`. -/
theorem distinctPrimeFactorCountBetween_eq_card_filter_dvd
    {L X n : ℕ} (hn : n ≠ 0) :
    distinctPrimeFactorCountBetween L X n =
      ((primesBetween L X).filter fun p ↦ p ∣ n).card := by
  unfold distinctPrimeFactorCountBetween
  congr 1
  ext p
  simp only [mem_filter, mem_primesBetween]
  simp only [Nat.mem_primeFactors]
  aesop

/-- A product of a constant local factor over the divisors in `P` is
the corresponding power of the number of such divisors. -/
theorem prod_subtype_ite_dvd_eq_pow
    (P : Finset ℕ) (q : ℝ) (n : ℕ) :
    (∏ p ∈ P, if p ∣ n then q else 1) =
      q ^ (P.filter fun p ↦ p ∣ n).card := by
  rw [← Finset.prod_filter]
  simp

/-- Squarefree centered divisibility weight of the integer forms
`u`, `v`, and `u+v`. -/
noncomputable def centeredIntegerWeight
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ) (u v : ℕ) : ℝ :=
  ∏ p ∈ P,
    (if p ∣ u then qU p else 1) *
      (if p ∣ v then qV p else 1) *
      (if p ∣ u + v then qSum p else 1)

/-- Squarefree cross divisibility weight of the integer forms
`u`, `w`, and `2u+w`. -/
noncomputable def crossIntegerWeight
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ) (u w : ℕ) : ℝ :=
  ∏ p ∈ P,
    (if p ∣ u then qU p else 1) *
      (if p ∣ w then qW p else 1) *
      (if p ∣ 2 * u + w then qLinear p else 1)

/-- Reducing an integer pair modulo the squarefree product and then
modulo one of its prime factors gives the direct reduction modulo that
prime. -/
theorem castHom_natCast_primeModulus
    (P : Finset ℕ) (p : P) (n : ℕ) :
    ZMod.castHom (prime_dvd_primeModulus P p) (ZMod p)
        (n : ZMod (primeModulus P)) =
      (n : ZMod p) := by
  simp

/-- The centered finite residue weight is exactly the centered
squarefree integer divisibility weight. -/
theorem centeredFiniteWeight_natCast
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ) (u v : ℕ) :
    centeredFiniteWeight P qU qV qSum
        ((u : ZMod (primeModulus P)), (v : ZMod (primeModulus P))) =
      centeredIntegerWeight P qU qV qSum u v := by
  classical
  calc
    centeredFiniteWeight P qU qV qSum
        ((u : ZMod (primeModulus P)), (v : ZMod (primeModulus P))) =
      ∏ p : P,
        (if (p : ℕ) ∣ u then qU p else 1) *
          (if (p : ℕ) ∣ v then qV p else 1) *
          (if (p : ℕ) ∣ u + v then qSum p else 1) := by
            unfold centeredFiniteWeight centeredLocalAt
            apply Fintype.prod_congr
            intro p
            simp only [castHom_natCast_primeModulus]
            unfold centeredLocalWeight
            simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    _ = centeredIntegerWeight P qU qV qSum u v := by
      unfold centeredIntegerWeight
      simpa using
        (Finset.prod_coe_sort P
          (fun p : ℕ ↦
            (if p ∣ u then qU p else 1) *
              (if p ∣ v then qV p else 1) *
              (if p ∣ u + v then qSum p else 1)))

/-- With constant local parameters, the centered squarefree weight is
the product of three localized distinct-factor moments. -/
theorem centeredIntegerWeight_const
    (P : Finset ℕ) (qU qV qSum : ℝ) (u v : ℕ) :
    centeredIntegerWeight P (fun _ ↦ qU) (fun _ ↦ qV)
        (fun _ ↦ qSum) u v =
      qU ^ (P.filter fun p ↦ p ∣ u).card *
        qV ^ (P.filter fun p ↦ p ∣ v).card *
        qSum ^ (P.filter fun p ↦ p ∣ u + v).card := by
  unfold centeredIntegerWeight
  simp_rw [Finset.prod_mul_distrib]
  rw [prod_subtype_ite_dvd_eq_pow, prod_subtype_ite_dvd_eq_pow,
    prod_subtype_ite_dvd_eq_pow]

/-- Exact cutoff-count form of the constant centered squarefree weight. -/
theorem centeredIntegerWeight_primesBetween
    {L X u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0)
    (qU qV qSum : ℝ) :
    centeredIntegerWeight (primesBetween L X)
        (fun _ ↦ qU) (fun _ ↦ qV) (fun _ ↦ qSum) u v =
      qU ^ distinctPrimeFactorCountBetween L X u *
        qV ^ distinctPrimeFactorCountBetween L X v *
        qSum ^ distinctPrimeFactorCountBetween L X (u + v) := by
  rw [centeredIntegerWeight_const,
    ← distinctPrimeFactorCountBetween_eq_card_filter_dvd hu,
    ← distinctPrimeFactorCountBetween_eq_card_filter_dvd hv,
    ← distinctPrimeFactorCountBetween_eq_card_filter_dvd huv]

/-- The centered multiplicity weight is pointwise bounded by the
squarefree finite-sieve weight. -/
theorem centeredMultiplicityWeight_le_integerWeight
    {L X u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u + v ≠ 0)
    {qU qV qSum : ℝ}
    (hqU0 : 0 ≤ qU) (hqU1 : qU ≤ 1)
    (hqV0 : 0 ≤ qV) (hqV1 : qV ≤ 1)
    (hqSum0 : 0 ≤ qSum) (hqSum1 : qSum ≤ 1) :
    qU ^ primeFactorCountBetween L X u *
        qV ^ primeFactorCountBetween L X v *
        qSum ^ primeFactorCountBetween L X (u + v) ≤
      centeredIntegerWeight (primesBetween L X)
        (fun _ ↦ qU) (fun _ ↦ qV) (fun _ ↦ qSum) u v := by
  rw [centeredIntegerWeight_primesBetween hu hv huv]
  have hU :=
    pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
      hqU0 hqU1 L X u
  have hV :=
    pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
      hqV0 hqV1 L X v
  have hSum :=
    pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
      hqSum0 hqSum1 L X (u + v)
  exact mul_le_mul
    (mul_le_mul hU hV (pow_nonneg hqV0 _) (pow_nonneg hqU0 _))
    hSum (pow_nonneg hqSum0 _)
    (mul_nonneg (pow_nonneg hqU0 _) (pow_nonneg hqV0 _))

/-- The finite-sieve box sum is exactly the sum of the corresponding
centered integer squarefree weights. -/
theorem finiteWeightBoxSum_centered_eq_integerWeight
    (P : Finset ℕ) (qU qV qSum : ℕ → ℝ) (X : ℕ) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := P) qU qV qSum) X =
      ∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
        centeredIntegerWeight P qU qV qSum x.1 x.2 := by
  classical
  unfold finiteWeightBoxSum localAtNat centeredRetainedFamily
  apply Finset.sum_congr rfl
  intro x _
  unfold centeredIntegerWeight
  calc
    (∏ p : P,
        centeredLocalWeight (qU p) (qV p) (qSum p)
          ((x.1 : ZMod (p : ℕ)), (x.2 : ZMod (p : ℕ)))) =
      ∏ p : P,
        (if (p : ℕ) ∣ x.1 then qU p else 1) *
          (if (p : ℕ) ∣ x.2 then qV p else 1) *
          (if (p : ℕ) ∣ x.1 + x.2 then qSum p else 1) := by
            apply Fintype.prod_congr
            intro p
            unfold centeredLocalWeight
            simp only [← Nat.cast_add, ZMod.natCast_eq_zero_iff]
    _ = _ := by
      simpa using
        (Finset.prod_coe_sort P
          (fun p : ℕ ↦
            (if p ∣ x.1 then qU p else 1) *
              (if p ∣ x.2 then qV p else 1) *
              (if p ∣ x.1 + x.2 then qSum p else 1)))

/-- Summed version of the pointwise centered `Ω`-to-squarefree
majorization on the standard sieve box. -/
theorem sum_centeredMultiplicityWeight_le_finiteWeightBoxSum
    {L X : ℕ} {qU qV qSum : ℝ}
    (hqU0 : 0 ≤ qU) (hqU1 : qU ≤ 1)
    (hqV0 : 0 ≤ qV) (hqV1 : qV ≤ 1)
    (hqSum0 : 0 ≤ qSum) (hqSum1 : qSum ≤ 1) :
    (∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
        qU ^ primeFactorCountBetween L (8 * X) x.1 *
          qV ^ primeFactorCountBetween L (8 * X) x.2 *
          qSum ^ primeFactorCountBetween L (8 * X) (x.1 + x.2)) ≤
      finiteWeightBoxSum
        (centeredRetainedFamily (P := primesBetween L (8 * X))
          (fun _ ↦ qU) (fun _ ↦ qV) (fun _ ↦ qSum)) X := by
  rw [finiteWeightBoxSum_centered_eq_integerWeight]
  apply sum_le_sum
  intro x hx
  have hxmem := mem_product.mp hx
  have hu : x.1 ≠ 0 := by
    have hlo := (mem_Ico.mp hxmem.1).1
    have hhi := (mem_Ico.mp hxmem.1).2
    omega
  have hv : x.2 ≠ 0 := by
    have := (mem_Icc.mp hxmem.2).1
    omega
  have huv : x.1 + x.2 ≠ 0 := by
    intro hzero
    apply hv
    omega
  exact centeredMultiplicityWeight_le_integerWeight hu hv huv
    hqU0 hqU1 hqV0 hqV1 hqSum0 hqSum1

/-- The cross finite residue weight is exactly the cross squarefree
integer divisibility weight. -/
theorem crossFiniteWeight_natCast
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ) (u w : ℕ) :
    crossFiniteWeight P qU qW qLinear
        ((u : ZMod (primeModulus P)), (w : ZMod (primeModulus P))) =
      crossIntegerWeight P qU qW qLinear u w := by
  classical
  calc
    crossFiniteWeight P qU qW qLinear
        ((u : ZMod (primeModulus P)), (w : ZMod (primeModulus P))) =
      ∏ p : P,
        (if (p : ℕ) ∣ u then qU p else 1) *
          (if (p : ℕ) ∣ w then qW p else 1) *
          (if (p : ℕ) ∣ 2 * u + w then qLinear p else 1) := by
            unfold crossFiniteWeight crossLocalAt
            apply Fintype.prod_congr
            intro p
            simp only [castHom_natCast_primeModulus]
            unfold crossLocalWeight
            have hcast :
                (2 : ZMod (p : ℕ)) * (u : ZMod (p : ℕ)) +
                    (w : ZMod (p : ℕ)) =
                  ((2 * u + w : ℕ) : ZMod (p : ℕ)) := by
              push_cast
              rfl
            rw [hcast]
            simp only [ZMod.natCast_eq_zero_iff]
    _ = crossIntegerWeight P qU qW qLinear u w := by
      unfold crossIntegerWeight
      simpa using
        (Finset.prod_coe_sort P
          (fun p : ℕ ↦
            (if p ∣ u then qU p else 1) *
              (if p ∣ w then qW p else 1) *
              (if p ∣ 2 * u + w then qLinear p else 1)))

/-- Constant-parameter form of the cross squarefree weight. -/
theorem crossIntegerWeight_const
    (P : Finset ℕ) (qU qW qLinear : ℝ) (u w : ℕ) :
    crossIntegerWeight P (fun _ ↦ qU) (fun _ ↦ qW)
        (fun _ ↦ qLinear) u w =
      qU ^ (P.filter fun p ↦ p ∣ u).card *
        qW ^ (P.filter fun p ↦ p ∣ w).card *
        qLinear ^ (P.filter fun p ↦ p ∣ 2 * u + w).card := by
  unfold crossIntegerWeight
  simp_rw [Finset.prod_mul_distrib]
  rw [prod_subtype_ite_dvd_eq_pow, prod_subtype_ite_dvd_eq_pow,
    prod_subtype_ite_dvd_eq_pow]

/-- Exact cutoff-count form of the constant cross squarefree weight. -/
theorem crossIntegerWeight_primesBetween
    {L X u w : ℕ} (hu : u ≠ 0) (hw : w ≠ 0)
    (hlin : 2 * u + w ≠ 0) (qU qW qLinear : ℝ) :
    crossIntegerWeight (primesBetween L X)
        (fun _ ↦ qU) (fun _ ↦ qW) (fun _ ↦ qLinear) u w =
      qU ^ distinctPrimeFactorCountBetween L X u *
        qW ^ distinctPrimeFactorCountBetween L X w *
        qLinear ^ distinctPrimeFactorCountBetween L X (2 * u + w) := by
  rw [crossIntegerWeight_const,
    ← distinctPrimeFactorCountBetween_eq_card_filter_dvd hu,
    ← distinctPrimeFactorCountBetween_eq_card_filter_dvd hw,
    ← distinctPrimeFactorCountBetween_eq_card_filter_dvd hlin]

/-- The cross multiplicity weight is pointwise bounded by the
squarefree finite-sieve weight. -/
theorem crossMultiplicityWeight_le_integerWeight
    {L X u w : ℕ} (hu : u ≠ 0) (hw : w ≠ 0)
    (hlin : 2 * u + w ≠ 0)
    {qU qW qLinear : ℝ}
    (hqU0 : 0 ≤ qU) (hqU1 : qU ≤ 1)
    (hqW0 : 0 ≤ qW) (hqW1 : qW ≤ 1)
    (hqLinear0 : 0 ≤ qLinear) (hqLinear1 : qLinear ≤ 1) :
    qU ^ primeFactorCountBetween L X u *
        qW ^ primeFactorCountBetween L X w *
        qLinear ^ primeFactorCountBetween L X (2 * u + w) ≤
      crossIntegerWeight (primesBetween L X)
        (fun _ ↦ qU) (fun _ ↦ qW) (fun _ ↦ qLinear) u w := by
  rw [crossIntegerWeight_primesBetween hu hw hlin]
  have hU :=
    pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
      hqU0 hqU1 L X u
  have hW :=
    pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
      hqW0 hqW1 L X w
  have hLinear :=
    pow_primeFactorCountBetween_le_pow_distinctPrimeFactorCountBetween
      hqLinear0 hqLinear1 L X (2 * u + w)
  exact mul_le_mul
    (mul_le_mul hU hW (pow_nonneg hqW0 _) (pow_nonneg hqU0 _))
    hLinear (pow_nonneg hqLinear0 _)
    (mul_nonneg (pow_nonneg hqU0 _) (pow_nonneg hqW0 _))

/-- The finite-sieve box sum is exactly the sum of cross integer
squarefree weights. -/
theorem finiteWeightBoxSum_cross_eq_integerWeight
    (P : Finset ℕ) (qU qW qLinear : ℕ → ℝ) (X : ℕ) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := P) qU qW qLinear) X =
      ∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
        crossIntegerWeight P qU qW qLinear x.1 x.2 := by
  classical
  unfold finiteWeightBoxSum localAtNat crossRetainedFamily
  apply Finset.sum_congr rfl
  intro x _
  unfold crossIntegerWeight
  calc
    (∏ p : P,
        crossLocalWeight (qU p) (qW p) (qLinear p)
          ((x.1 : ZMod (p : ℕ)), (x.2 : ZMod (p : ℕ)))) =
      ∏ p : P,
        (if (p : ℕ) ∣ x.1 then qU p else 1) *
          (if (p : ℕ) ∣ x.2 then qW p else 1) *
          (if (p : ℕ) ∣ 2 * x.1 + x.2 then qLinear p else 1) := by
            apply Fintype.prod_congr
            intro p
            unfold crossLocalWeight
            have hcast :
                (2 : ZMod (p : ℕ)) * (x.1 : ZMod (p : ℕ)) +
                    (x.2 : ZMod (p : ℕ)) =
                  ((2 * x.1 + x.2 : ℕ) : ZMod (p : ℕ)) := by
              push_cast
              rfl
            rw [hcast]
            simp only [ZMod.natCast_eq_zero_iff]
    _ = _ := by
      simpa using
        (Finset.prod_coe_sort P
          (fun p : ℕ ↦
            (if p ∣ x.1 then qU p else 1) *
              (if p ∣ x.2 then qW p else 1) *
              (if p ∣ 2 * x.1 + x.2 then qLinear p else 1)))

/-- Summed version of the cross `Ω`-to-squarefree majorization on the
standard sieve box. -/
theorem sum_crossMultiplicityWeight_le_finiteWeightBoxSum
    {L X : ℕ} {qU qW qLinear : ℝ}
    (hqU0 : 0 ≤ qU) (hqU1 : qU ≤ 1)
    (hqW0 : 0 ≤ qW) (hqW1 : qW ≤ 1)
    (hqLinear0 : 0 ≤ qLinear) (hqLinear1 : qLinear ≤ 1) :
    (∑ x ∈ Ico X (2 * X) ×ˢ Icc 1 (8 * X),
        qU ^ primeFactorCountBetween L (8 * X) x.1 *
          qW ^ primeFactorCountBetween L (8 * X) x.2 *
          qLinear ^ primeFactorCountBetween L (8 * X)
            (2 * x.1 + x.2)) ≤
      finiteWeightBoxSum
        (crossRetainedFamily (P := primesBetween L (8 * X))
          (fun _ ↦ qU) (fun _ ↦ qW) (fun _ ↦ qLinear)) X := by
  rw [finiteWeightBoxSum_cross_eq_integerWeight]
  apply sum_le_sum
  intro x hx
  have hxmem := mem_product.mp hx
  have hu : x.1 ≠ 0 := by
    have hlo := (mem_Ico.mp hxmem.1).1
    have hhi := (mem_Ico.mp hxmem.1).2
    omega
  have hw : x.2 ≠ 0 := by
    have := (mem_Icc.mp hxmem.2).1
    omega
  have hlin : 2 * x.1 + x.2 ≠ 0 := by
    intro hzero
    apply hw
    omega
  exact crossMultiplicityWeight_le_integerWeight hu hw hlin
    hqU0 hqU1 hqW0 hqW1 hqLinear0 hqLinear1

end Erdos327.Analytic
