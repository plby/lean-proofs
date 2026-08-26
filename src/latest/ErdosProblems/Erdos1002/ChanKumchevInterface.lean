import ErdosProblems.Erdos1002.RamanujanVectorDyadic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact interface for the Chan--Kumchev second-moment input

This file isolates the only long-range arithmetic estimate not supplied by
the elementary Ramanujan modules and proves every subsequent finite
deduction needed by the near-resonant multiplier argument.

The source-faithful external mathematical content is represented by the
proposition `ChanKumchevInitialSecondMomentEstimate D K T`:

`∑_{1≤n≤2K}|∑_{q≤X} c_q(-n)|² ≤ D K X²` for every `1 ≤ X ≤ T`.

This proposition is a definition, not an axiom, and this file does not claim
a proof of it.  Its immediate restriction to `K < n ≤ 2K` is the minimal
interface `RamanujanPrefixSecondMomentEstimate`.  Chan and Kumchev's
Theorem 1.2(ii), together with an elementary argument in the complementary
range, supplies precisely such an absolute `D` when `T` is at most
`K/(log K)^B` with a sufficiently large fixed `B`.  The elementary range
`T² ≤ K` is proved below with `D = 6`; a source-faithful *uniform* estimate
in the genuinely long range would require the analytic Chan--Kumchev
theorem.

Assuming a proof of the displayed proposition as an ordinary theorem
argument, everything below is fully formal and finite: conversion from a
second moment to an `ℓ²` bound, subtraction of prefix vectors, exact Abel
summation with both endpoints, reciprocal-square variation, the finite-tail
estimate, and finally the near-resonant multiplier bound.  No declaration in
this file introduces an unproved global constant, an incomplete proof marker,
or an infinite-tail limiting convention.

This is an interface module, not an assumption in the public theorem.
The final dependency chain instead uses the fully formal divisor-square
estimate and the subquadratic fixed-away argument in
`FixedAwayUnshiftedSubquadratic`; consequently `Erdos1002.erdos1002` has no
Chan--Kumchev hypothesis.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-! ## The minimal second-moment interface -/

/-- The unweighted Ramanujan vector on the manuscript frequency shell. -/
def rawRamanujanVectorTerm (K q : ℕ) : NearDyadicEuclidean K :=
  WithLp.toLp 2 (fun n ↦ ramanujanSum q (-((n : ℕ) : ℤ)))

/-- The finite prefix `∑_{1≤q≤X} c_q(-n)` as an `ℓ²` vector. -/
def ramanujanPrefixVector (K X : ℕ) : NearDyadicEuclidean K :=
  euclideanIntervalPartialSum (rawRamanujanVectorTerm K) 1 X

/-- Norm form of the required uniform prefix estimate. -/
def RamanujanPrefixL2Estimate (C : ℝ) (K T : ℕ) : Prop :=
  0 ≤ C ∧ ∀ X ∈ Finset.Icc 1 T,
    ‖ramanujanPrefixVector K X‖ ≤
      C * Real.sqrt (K : ℝ) * (X : ℝ)

/-- Minimal second-moment proposition extracted from the Chan--Kumchev
theorem.  This is merely a proposition-valued definition. -/
def RamanujanPrefixSecondMomentEstimate (D : ℝ) (K T : ℕ) : Prop :=
  0 ≤ D ∧ ∀ X ∈ Finset.Icc 1 T,
    ‖ramanujanPrefixVector K X‖ ^ 2 ≤
      D * (K : ℝ) * (X : ℝ) ^ 2

/-- The full positive-frequency index set `1 ≤ n ≤ 2K` occurring literally
in the Chan--Kumchev moment sum. -/
abbrev initialRamanujanIndex (K : ℕ) :=
  {n : ℕ // n ∈ Finset.Icc 1 (2 * K)}

/-- Euclidean space on the full initial frequency interval. -/
abbrev InitialRamanujanEuclidean (K : ℕ) :=
  EuclideanSpace ℂ (initialRamanujanIndex K)

/-- One unweighted Ramanujan vector on the full initial interval. -/
def initialRawRamanujanVectorTerm (K q : ℕ) : InitialRamanujanEuclidean K :=
  WithLp.toLp 2 (fun n ↦ ramanujanSum q (-((n : ℕ) : ℤ)))

/-- The literal prefix vector whose norm square is the second moment
`∑_{1≤n≤2K}|∑_{q≤X}c_q(n)|²`. -/
def initialRamanujanPrefixVector (K X : ℕ) : InitialRamanujanEuclidean K :=
  euclideanIntervalPartialSum (initialRawRamanujanVectorTerm K) 1 X

/-- Source-faithful second-moment interface on `1 ≤ n ≤ 2K`.  Proving this
uniformly with an absolute `D` in the long range is the precise remaining
Chan--Kumchev input. -/
def ChanKumchevInitialSecondMomentEstimate (D : ℝ) (K T : ℕ) : Prop :=
  0 ≤ D ∧ ∀ X ∈ Finset.Icc 1 T,
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
      D * (K : ℝ) * (X : ℝ) ^ 2

/-! ## Elementary proof of the initial second moment when `X² ≤ K` -/

/-- The real Ramanujan prefix coefficient at one positive frequency. -/
def initialRawRamanujanBlockCoefficient (X n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 X, (ramanujanSum q (n : ℤ)).re

/-- The unweighted correlation of two Ramanujan sums on `1 ≤ n ≤ 2K`. -/
def initialRamanujanPairCorrelation (K q q' : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (2 * K),
    ramanujanSum q (n : ℤ) * ramanujanSum q' (n : ℤ)

/-- Pointwise expansion of the square of the real prefix coefficient. -/
theorem initialRawRamanujanBlockCoefficient_sq (X n : ℕ) :
    initialRawRamanujanBlockCoefficient X n ^ 2 =
      ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
        (ramanujanSum q (n : ℤ) * ramanujanSum q' (n : ℤ)).re := by
  rw [initialRawRamanujanBlockCoefficient, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q' _hq'
  simp only [Complex.mul_re, ramanujanSum_im, mul_zero, sub_zero]

/-- The vector coefficient agrees with the real scalar block coefficient;
the sign in `c_q(-n)` disappears by evenness of the Ramanujan sum. -/
theorem initialRamanujanPrefixVector_apply_eq_realBlock
    (K X : ℕ) (n : initialRamanujanIndex K) :
    initialRamanujanPrefixVector K X n =
      (initialRawRamanujanBlockCoefficient X (n : ℕ) : ℂ) := by
  simp only [initialRamanujanPrefixVector, euclideanIntervalPartialSum,
    initialRawRamanujanVectorTerm, WithLp.ofLp_sum, Finset.sum_apply,
    initialRawRamanujanBlockCoefficient]
  push_cast
  apply Finset.sum_congr rfl
  intro q _hq
  rw [ramanujanSum_even]
  exact (ofReal_re_ramanujanSum q ((n : ℕ) : ℤ)).symm

/-- The norm square of the initial prefix vector is the scalar second
moment over `1 ≤ n ≤ 2K`. -/
theorem norm_sq_initialRamanujanPrefixVector_eq_coefficients
    (K X : ℕ) :
    ‖initialRamanujanPrefixVector K X‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 (2 * K),
        initialRawRamanujanBlockCoefficient X n ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_coe_sort (Finset.Icc 1 (2 * K))]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [initialRamanujanPrefixVector_apply_eq_realBlock]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Exact pair-correlation expansion of the initial second moment. -/
theorem norm_sq_initialRamanujanPrefixVector_eq_pairSum
    (K X : ℕ) :
    ‖initialRamanujanPrefixVector K X‖ ^ 2 =
      ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
        (initialRamanujanPairCorrelation K q q').re := by
  rw [norm_sq_initialRamanujanPrefixVector_eq_coefficients]
  calc
    (∑ n ∈ Finset.Icc 1 (2 * K),
        initialRawRamanujanBlockCoefficient X n ^ 2) =
        ∑ n ∈ Finset.Icc 1 (2 * K),
          ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
            (ramanujanSum q (n : ℤ) * ramanujanSum q' (n : ℤ)).re := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact initialRawRamanujanBlockCoefficient_sq X n
    _ = ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
        ∑ n ∈ Finset.Icc 1 (2 * K),
          (ramanujanSum q (n : ℤ) * ramanujanSum q' (n : ℤ)).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_comm]
    _ = ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
        (initialRamanujanPairCorrelation K q q').re := by
      apply Finset.sum_congr rfl
      intro q _hq
      apply Finset.sum_congr rfl
      intro q' _hq'
      simp only [initialRamanujanPairCorrelation, Complex.re_sum]

/-- Incomplete orthogonality bounds an off-diagonal correlation. -/
theorem norm_initialRamanujanPairCorrelation_le
    (K : ℕ) {q q' : ℕ}
    (hq : q ≠ 0) (hq' : q' ≠ 0) (hqq' : q ≠ q') :
    ‖initialRamanujanPairCorrelation K q q'‖ ≤
      2 * ((ArithmeticFunction.sigma 1 q : ℝ) *
        (ArithmeticFunction.sigma 1 q' : ℝ)) := by
  exact ramanujan_incomplete_orthogonality_nat_Icc
    1 (2 * K) hq hq' hqq'

/-- Complete-period orthogonality bounds one diagonal correlation by a
linear interval-length factor. -/
theorem initialRamanujanPairCorrelation_self_re_le_linear
    (K q : ℕ) (hq : q ≠ 0) :
    (initialRamanujanPairCorrelation K q q).re ≤
      (((2 * K + 1 + q) * Nat.totient q : ℕ) : ℝ) := by
  have hsubset : Finset.Icc 1 (2 * K) ⊆ Finset.range (2 * K + 1) := by
    intro n hn
    rw [Finset.mem_range]
    exact Nat.lt_add_one_iff.mpr (Finset.mem_Icc.mp hn).2
  have hperiodCount : ((2 * K + 1) / q + 1) * q ≤ 2 * K + 1 + q := by
    rw [add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self (2 * K + 1) q) q
  calc
    (initialRamanujanPairCorrelation K q q).re =
        ∑ n ∈ Finset.Icc 1 (2 * K), ramanujanNormSq q n := by
      simp only [initialRamanujanPairCorrelation, Complex.re_sum,
        Complex.mul_re, ramanujanSum_im, mul_zero, sub_zero,
        ramanujanNormSq, Complex.normSq_apply, add_zero]
    _ ≤ ∑ n ∈ Finset.range (2 * K + 1), ramanujanNormSq q n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n _hn _hnot
      exact Complex.normSq_nonneg _
    _ ≤ (((2 * K + 1) / q + 1 : ℕ) : ℝ) *
          (q * Nat.totient q : ℕ) :=
      sum_ramanujanNormSq_range_le q (2 * K + 1) hq
    _ = ((((2 * K + 1) / q + 1) * q * Nat.totient q : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (((2 * K + 1 + q) * Nat.totient q : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right (Nat.totient q) hperiodCount

/-- The total diagonal contribution is at most `4 K X²` when `X² ≤ K`. -/
theorem sum_initialRamanujan_diagonal_le
    (K X : ℕ) (hX : 0 < X) (hXK : X ^ 2 ≤ K) :
    (∑ q ∈ Finset.Icc 1 X,
      (initialRamanujanPairCorrelation K q q).re) ≤
      4 * (K : ℝ) * (X : ℝ) ^ 2 := by
  have hXleXsq : X ≤ X ^ 2 := by nlinarith
  have hXleK : X ≤ K := hXleXsq.trans hXK
  have hOneK : 1 ≤ K := hX.trans_le hXleK
  have hmainNat : 2 * K + 1 + X ≤ 4 * K := by omega
  have hcard : (Finset.Icc 1 X).card = X := by
    rw [Nat.card_Icc]
    omega
  have hpoint (q : ℕ) (hq : q ∈ Finset.Icc 1 X) :
      (initialRamanujanPairCorrelation K q q).re ≤
        (((2 * K + 1 + X) * X : ℕ) : ℝ) := by
    have hqBounds := Finset.mem_Icc.mp hq
    calc
      (initialRamanujanPairCorrelation K q q).re ≤
          (((2 * K + 1 + q) * Nat.totient q : ℕ) : ℝ) :=
        initialRamanujanPairCorrelation_self_re_le_linear K q (by omega)
      _ ≤ (((2 * K + 1 + X) * X : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul
          (Nat.add_le_add_left hqBounds.2 (2 * K + 1))
          ((Nat.totient_le q).trans hqBounds.2)
  calc
    (∑ q ∈ Finset.Icc 1 X,
        (initialRamanujanPairCorrelation K q q).re) ≤
        ∑ _q ∈ Finset.Icc 1 X,
          (((2 * K + 1 + X) * X : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hpoint q hq
    _ = (X : ℝ) * (((2 * K + 1 + X) * X : ℕ) : ℝ) := by
      rw [sum_const, nsmul_eq_mul, hcard]
    _ ≤ (X : ℝ) * ((4 * K * X : ℕ) : ℝ) := by
      gcongr
    _ = 4 * (K : ℝ) * (X : ℝ) ^ 2 := by
      push_cast
      ring

/-- The absolute off-diagonal contribution is at most `2 K X²` when
`X² ≤ K`. -/
theorem sum_abs_initialRamanujan_offDiagonal_le
    (K X : ℕ) (hXK : X ^ 2 ≤ K) :
    (∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
      if q ≠ q' then |(initialRamanujanPairCorrelation K q q').re|
      else 0) ≤
      2 * (K : ℝ) * (X : ℝ) ^ 2 := by
  let mass : ℕ → ℝ := fun q ↦ (ArithmeticFunction.sigma 1 q : ℝ)
  have hmass (q : ℕ) : 0 ≤ mass q := by dsimp [mass]; positivity
  have hpoint {q q' : ℕ}
      (hq : q ∈ Finset.Icc 1 X) (hq' : q' ∈ Finset.Icc 1 X)
      (hne : q ≠ q') :
      |(initialRamanujanPairCorrelation K q q').re| ≤
        2 * mass q * mass q' := by
    have hqPos : 0 < q := (Finset.mem_Icc.mp hq).1
    have hq'Pos : 0 < q' := (Finset.mem_Icc.mp hq').1
    calc
      |(initialRamanujanPairCorrelation K q q').re| ≤
          ‖initialRamanujanPairCorrelation K q q'‖ :=
        Complex.abs_re_le_norm _
      _ ≤ 2 * ((ArithmeticFunction.sigma 1 q : ℝ) *
          (ArithmeticFunction.sigma 1 q' : ℝ)) :=
        norm_initialRamanujanPairCorrelation_le
          K hqPos.ne' hq'Pos.ne' hne
      _ = 2 * mass q * mass q' := by dsimp [mass]; ring
  have hmassSum : (∑ q ∈ Finset.Icc 1 X, mass q) ≤ (X : ℝ) ^ 2 := by
    simpa only [mass] using! sum_sigma_one_Icc_le_square X
  have hXKReal : (X : ℝ) ^ 2 ≤ (K : ℝ) := by exact_mod_cast hXK
  calc
    (∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
        if q ≠ q' then |(initialRamanujanPairCorrelation K q q').re|
        else 0) ≤
        ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
          2 * mass q * mass q' := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro q' hq'
      by_cases hne : q ≠ q'
      · rw [if_pos hne]
        exact hpoint hq hq' hne
      · rw [if_neg hne]
        positivity
    _ = 2 * (∑ q ∈ Finset.Icc 1 X, mass q) ^ 2 := by
      calc
        (∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
            2 * mass q * mass q') =
            ∑ q ∈ Finset.Icc 1 X,
              (2 * mass q) * (∑ q' ∈ Finset.Icc 1 X, mass q') := by
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
        _ = (∑ q ∈ Finset.Icc 1 X, 2 * mass q) *
            (∑ q' ∈ Finset.Icc 1 X, mass q') := by
          rw [Finset.sum_mul]
        _ = (2 * (∑ q ∈ Finset.Icc 1 X, mass q)) *
            (∑ q' ∈ Finset.Icc 1 X, mass q') := by
          have hf : (∑ q ∈ Finset.Icc 1 X, 2 * mass q) =
              2 * (∑ q ∈ Finset.Icc 1 X, mass q) :=
            (Finset.mul_sum (Finset.Icc 1 X) mass 2).symm
          rw [hf]
        _ = 2 * (∑ q ∈ Finset.Icc 1 X, mass q) ^ 2 := by ring
    _ ≤ 2 * ((X : ℝ) ^ 2) ^ 2 := by gcongr
    _ ≤ 2 * (K : ℝ) * (X : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((X : ℝ) ^ 2)]

/-- Elementary initial second-moment bound with explicit constant `6` in
the complete-period range `X² ≤ K`. -/
theorem norm_sq_initialRamanujanPrefixVector_le_lowRange
    (K X : ℕ) (hX : 0 < X) (hXK : X ^ 2 ≤ K) :
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
      6 * (K : ℝ) * (X : ℝ) ^ 2 := by
  let D : ℕ → ℕ → ℝ := fun q q' ↦
    if q = q' then (initialRamanujanPairCorrelation K q q).re else 0
  let O : ℕ → ℕ → ℝ := fun q q' ↦
    if q ≠ q' then |(initialRamanujanPairCorrelation K q q').re| else 0
  have hpoint (q q' : ℕ) :
      (initialRamanujanPairCorrelation K q q').re ≤ D q q' + O q q' := by
    by_cases heq : q = q'
    · subst q'
      simp [D, O]
    · have hre : (initialRamanujanPairCorrelation K q q').re ≤
          |(initialRamanujanPairCorrelation K q q').re| := le_abs_self _
      simpa [D, O, heq] using! hre
  have hdiag :
      (∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X, D q q') =
        ∑ q ∈ Finset.Icc 1 X,
          (initialRamanujanPairCorrelation K q q).re := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_eq_single q]
    · simp [D]
    · intro q' hq' hne
      simp [D, Ne.symm hne]
    · exact fun hnot ↦ (hnot hq).elim
  calc
    ‖initialRamanujanPrefixVector K X‖ ^ 2 =
        ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
          (initialRamanujanPairCorrelation K q q').re :=
      norm_sq_initialRamanujanPrefixVector_eq_pairSum K X
    _ ≤ ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
          (D q q' + O q q') := by
      apply Finset.sum_le_sum
      intro q _hq
      apply Finset.sum_le_sum
      intro q' _hq'
      exact hpoint q q'
    _ = (∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X, D q q') +
          ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X, O q q' := by
      simp_rw [Finset.sum_add_distrib]
    _ = (∑ q ∈ Finset.Icc 1 X,
          (initialRamanujanPairCorrelation K q q).re) +
          ∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X, O q q' := by
      rw [hdiag]
    _ ≤ 4 * (K : ℝ) * (X : ℝ) ^ 2 +
          2 * (K : ℝ) * (X : ℝ) ^ 2 := by
      apply add_le_add (sum_initialRamanujan_diagonal_le K X hX hXK)
      simpa only [O] using! sum_abs_initialRamanujan_offDiagonal_le K X hXK
    _ = 6 * (K : ℝ) * (X : ℝ) ^ 2 := by ring

/-- Uniform source-faithful second-moment estimate in the entire elementary
range `T² ≤ K`. -/
theorem chanKumchevInitialSecondMomentEstimate_elementaryRange
    (K T : ℕ) (hTK : T ^ 2 ≤ K) :
    ChanKumchevInitialSecondMomentEstimate 6 K T := by
  refine ⟨by norm_num, ?_⟩
  intro X hX
  have hXbounds := Finset.mem_Icc.mp hX
  have hXPos : 0 < X := hXbounds.1
  have hXsqT : X ^ 2 ≤ T ^ 2 := Nat.pow_le_pow_left hXbounds.2 2
  exact norm_sq_initialRamanujanPrefixVector_le_lowRange K X hXPos
    (hXsqT.trans hTK)

/-- The exact residual analytic input after the elementary range has been
removed: the initial second moment only for prefixes with `K < X²`.  This
is a proposition-valued interface, not an axiom. -/
def ChanKumchevInitialLongRangeEstimate (D : ℝ) (K T : ℕ) : Prop :=
  0 ≤ D ∧ ∀ X ∈ Finset.Icc 1 T, K < X ^ 2 →
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
      D * (K : ℝ) * (X : ℝ) ^ 2

/-- Combining a long-range Chan--Kumchev estimate with the proved
elementary range yields the full source-faithful estimate.  The harmless
constant `6` is added only to avoid a maximum in the interface. -/
theorem ChanKumchevInitialLongRangeEstimate.withElementaryRange
    {D : ℝ} {K T : ℕ}
    (hLong : ChanKumchevInitialLongRangeEstimate D K T) :
    ChanKumchevInitialSecondMomentEstimate (D + 6) K T := by
  refine ⟨by nlinarith [hLong.1], ?_⟩
  intro X hX
  have hXPos : 0 < X := (Finset.mem_Icc.mp hX).1
  have hScale : 0 ≤ (K : ℝ) * (X : ℝ) ^ 2 := by positivity
  by_cases hLow : X ^ 2 ≤ K
  · calc
      ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
          6 * (K : ℝ) * (X : ℝ) ^ 2 :=
        norm_sq_initialRamanujanPrefixVector_le_lowRange K X hXPos hLow
      _ ≤ (D + 6) * (K : ℝ) * (X : ℝ) ^ 2 := by
        nlinarith [hLong.1]
  · have hHigh : K < X ^ 2 := by omega
    calc
      ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
          D * (K : ℝ) * (X : ℝ) ^ 2 := hLong.2 X hX hHigh
      _ ≤ (D + 6) * (K : ℝ) * (X : ℝ) ^ 2 := by
        nlinarith

/-- Restricting the full initial frequency interval to `K < n ≤ 2K` can
only decrease the norm square. -/
theorem norm_sq_ramanujanPrefixVector_le_initial
    (K X : ℕ) :
    ‖ramanujanPrefixVector K X‖ ^ 2 ≤
      ‖initialRamanujanPrefixVector K X‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [ramanujanPrefixVector, initialRamanujanPrefixVector,
    euclideanIntervalPartialSum, WithLp.ofLp_sum,
    rawRamanujanVectorTerm, initialRawRamanujanVectorTerm,
    Finset.sum_apply]
  let f : ℕ → ℝ := fun n ↦
    ‖∑ q ∈ Finset.Icc 1 X, ramanujanSum q (-(n : ℤ))‖ ^ 2
  change (∑ n : nearDyadicIndex K, f (n : ℕ)) ≤
    ∑ n : initialRamanujanIndex K, f (n : ℕ)
  rw [Finset.sum_coe_sort (Finset.Ioc K (2 * K))]
  rw [Finset.sum_coe_sort (Finset.Icc 1 (2 * K))]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hbounds := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hbounds.2⟩
  · intro n hn _hnot
    positivity

/-- The source-faithful initial-interval estimate implies the minimal dyadic
interface used by the multiplier proof. -/
theorem ChanKumchevInitialSecondMomentEstimate.toDyadic
    {D : ℝ} {K T : ℕ}
    (hCK : ChanKumchevInitialSecondMomentEstimate D K T) :
    RamanujanPrefixSecondMomentEstimate D K T := by
  refine ⟨hCK.1, ?_⟩
  intro X hX
  exact (norm_sq_ramanujanPrefixVector_le_initial K X).trans (hCK.2 X hX)

/-- A second-moment estimate implies its square-root norm form. -/
theorem RamanujanPrefixSecondMomentEstimate.toL2
    {D : ℝ} {K T : ℕ}
    (hCK : RamanujanPrefixSecondMomentEstimate D K T) :
    RamanujanPrefixL2Estimate (Real.sqrt D) K T := by
  refine ⟨Real.sqrt_nonneg D, ?_⟩
  intro X hX
  have hrhsNonneg :
      0 ≤ Real.sqrt D * Real.sqrt (K : ℝ) * (X : ℝ) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) hrhsNonneg).mp
  calc
    ‖ramanujanPrefixVector K X‖ ^ 2 ≤
        D * (K : ℝ) * (X : ℝ) ^ 2 := hCK.2 X hX
    _ = (Real.sqrt D * Real.sqrt (K : ℝ) * (X : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hCK.1,
        Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (K : ℝ))]

/-! ## Prefix subtraction and reciprocal-square Abel summation -/

/-- An interval sum is exactly the difference of its two global prefixes. -/
theorem euclideanIntervalPartialSum_raw_eq_prefix_sub
    (K Q R : ℕ) (hQ : 0 < Q) (hQR : Q < R) :
    euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R =
      ramanujanPrefixVector K R - ramanujanPrefixVector K Q := by
  have hdisjoint : Disjoint (Finset.Icc 1 Q) (Finset.Icc (Q + 1) R) := by
    rw [Finset.disjoint_left]
    intro q hqLeft hqRight
    have hl := Finset.mem_Icc.mp hqLeft
    have hr := Finset.mem_Icc.mp hqRight
    omega
  have hunion : Finset.Icc 1 Q ∪ Finset.Icc (Q + 1) R =
      Finset.Icc 1 R := by
    ext q
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hsum : ramanujanPrefixVector K R =
      ramanujanPrefixVector K Q +
        euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R := by
    change (∑ q ∈ Finset.Icc 1 R, rawRamanujanVectorTerm K q) =
      (∑ q ∈ Finset.Icc 1 Q, rawRamanujanVectorTerm K q) +
        ∑ q ∈ Finset.Icc (Q + 1) R, rawRamanujanVectorTerm K q
    rw [← Finset.sum_union hdisjoint, hunion]
  rw [hsum]
  abel

/-- Uniform interval bound obtained from the two prefix endpoints. -/
theorem norm_euclideanIntervalPartialSum_raw_le_of_prefixEstimate
    (C : ℝ) (K T Q R : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hQ : 0 < Q) (hQR : Q < R) (hRT : R ≤ T) :
    ‖euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R‖ ≤
      2 * C * Real.sqrt (K : ℝ) * (R : ℝ) := by
  have hQT : Q ≤ T := hQR.le.trans hRT
  have hQmem : Q ∈ Finset.Icc 1 T :=
    Finset.mem_Icc.mpr ⟨hQ, hQT⟩
  have hRmem : R ∈ Finset.Icc 1 T :=
    Finset.mem_Icc.mpr ⟨hQ.trans hQR, hRT⟩
  rw [euclideanIntervalPartialSum_raw_eq_prefix_sub K Q R hQ hQR]
  calc
    ‖ramanujanPrefixVector K R - ramanujanPrefixVector K Q‖ ≤
        ‖ramanujanPrefixVector K R‖ + ‖ramanujanPrefixVector K Q‖ :=
      norm_sub_le _ _
    _ ≤ C * Real.sqrt (K : ℝ) * (R : ℝ) +
        C * Real.sqrt (K : ℝ) * (Q : ℝ) := by
      exact add_le_add (hCK.2 R hRmem) (hCK.2 Q hQmem)
    _ ≤ 2 * C * Real.sqrt (K : ℝ) * (R : ℝ) := by
      have hfactor : 0 ≤ C * Real.sqrt (K : ℝ) :=
        mul_nonneg hCK.1 (Real.sqrt_nonneg _)
      have hQRReal : (Q : ℝ) ≤ (R : ℝ) := by exact_mod_cast hQR.le
      nlinarith

/-- The constant coordinate multiplier `q⁻²`. -/
def reciprocalSquareMultiplier (K q : ℕ) : nearDyadicIndex K → ℂ :=
  fun _ ↦ ((1 / (q : ℝ) ^ 2 : ℝ) : ℂ)

/-- Multiplying the raw vector by `q⁻²` recovers the weighted vector from
`NearResonantVectorAbel`. -/
@[simp] theorem euclideanCoordinateMul_raw_reciprocalSquareMultiplier
    (K q : ℕ) :
    euclideanCoordinateMul (rawRamanujanVectorTerm K q)
      (reciprocalSquareMultiplier K q) = nearRamanujanVectorTerm K q := by
  ext n
  simp only [euclideanCoordinateMul, rawRamanujanVectorTerm,
    reciprocalSquareMultiplier, nearRamanujanVectorTerm,
    WithLp.ofLp_toLp]
  push_cast
  ring

/-- Supremum-norm bound for the terminal reciprocal-square multiplier. -/
theorem norm_reciprocalSquareMultiplier_le
    (K q : ℕ) (hq : 0 < q) :
    ‖reciprocalSquareMultiplier K q‖ ≤ 1 / (q : ℝ) ^ 2 := by
  have hnonneg : 0 ≤ 1 / (q : ℝ) ^ 2 := by positivity
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro n
  simp only [reciprocalSquareMultiplier, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact le_rfl

/-- Exact-sign bound for one discrete reciprocal-square variation. -/
theorem norm_reciprocalSquareMultiplier_sub_succ_le
    (K q : ℕ) (hq : 0 < q) :
    ‖reciprocalSquareMultiplier K q - reciprocalSquareMultiplier K (q + 1)‖ ≤
      1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hden : (q : ℝ) ^ 2 ≤ ((q + 1 : ℕ) : ℝ) ^ 2 := by
    norm_num
    nlinarith
  have hle : 1 / ((q + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (q : ℝ) ^ 2 := by
    exact one_div_le_one_div_of_le (sq_pos_of_pos hqR) hden
  have hnonneg :
      0 ≤ 1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2 :=
    sub_nonneg.mpr hle
  apply (pi_norm_le_iff_of_nonneg hnonneg).mpr
  intro n
  simp only [reciprocalSquareMultiplier, Pi.sub_apply, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact le_rfl

/-- Exact finite vector Abel identity, including the upper endpoint and every
variation term. -/
theorem sum_nearRamanujanVectorTerm_eq_raw_abel
    (K A R : ℕ) (hAR : A ≤ R) :
    (∑ q ∈ Finset.Icc A R, nearRamanujanVectorTerm K q) =
      euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) A R)
          (reciprocalSquareMultiplier K R) +
        ∑ q ∈ Finset.Ico A R,
          euclideanCoordinateMul
            (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) A q)
            (reciprocalSquareMultiplier K q -
              reciprocalSquareMultiplier K (q + 1)) := by
  simpa only [euclideanCoordinateMul_raw_reciprocalSquareMultiplier] using!
    euclideanVectorDiscreteAbel_identity
      (rawRamanujanVectorTerm K) (reciprocalSquareMultiplier K) hAR

/-- The weighted reciprocal-square variation is dominated by a telescoping
reciprocal difference. -/
theorem reciprocalSquare_weightedVariation_le_telescope
    (q : ℕ) (hq : 0 < q) :
    (q : ℝ) *
        (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2) ≤
      2 * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  field_simp
  push_cast
  nlinarith

/-- Summed variation bound with the lower endpoint explicit. -/
theorem sum_reciprocalSquare_weightedVariation_le
    (A R : ℕ) (hA : 0 < A) (hAR : A ≤ R) :
    (∑ q ∈ Finset.Ico A R,
      (q : ℝ) *
        (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2)) ≤
      2 / (A : ℝ) := by
  have htel :
      (∑ q ∈ Finset.Ico A R,
        (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ))) =
        1 / (A : ℝ) - 1 / (R : ℝ) := by
    have h := Finset.sum_Ico_sub
      (fun q : ℕ ↦ -(1 / (q : ℝ))) hAR
    simpa only [neg_sub_neg, neg_div, neg_neg] using! h
  calc
    (∑ q ∈ Finset.Ico A R,
        (q : ℝ) *
          (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2)) ≤
        ∑ q ∈ Finset.Ico A R,
          2 * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact reciprocalSquare_weightedVariation_le_telescope q
        (hA.trans_le (Finset.mem_Ico.mp hq).1)
    _ = 2 * (1 / (A : ℝ) - 1 / (R : ℝ)) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ 2 / (A : ℝ) := by
      have hRnonneg : 0 ≤ 1 / (R : ℝ) := by positivity
      calc
        2 * (1 / (A : ℝ) - 1 / (R : ℝ)) =
            2 / (A : ℝ) - 2 * (1 / (R : ℝ)) := by ring
        _ ≤ 2 / (A : ℝ) := sub_le_self _ (mul_nonneg (by norm_num) hRnonneg)

/-! ## Consequences for the finite tail and near-resonant multiplier -/

/-- The finite reciprocal-square Ramanujan tail follows from the prefix
estimate with explicit constant `6`; no infinite limit is taken. -/
theorem norm_sum_nearRamanujanVectorTerm_tail_le_of_prefixEstimate
    (C : ℝ) (K T Q R : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (hQ : 0 < Q) (hQR : Q < R) (hRT : R ≤ T) :
    ‖∑ q ∈ Finset.Icc (Q + 1) R, nearRamanujanVectorTerm K q‖ ≤
      6 * C * Real.sqrt (K : ℝ) / (Q : ℝ) := by
  have hStartEnd : Q + 1 ≤ R := by omega
  have hRpos : 0 < R := hQ.trans hQR
  have hterminalRaw :=
    norm_euclideanIntervalPartialSum_raw_le_of_prefixEstimate
      C K T Q R hCK hQ hQR hRT
  have hterminalWeight := norm_reciprocalSquareMultiplier_le K R hRpos
  have hfactor : 0 ≤ 2 * C * Real.sqrt (K : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) hCK.1) (Real.sqrt_nonneg _)
  have hterminal :
      ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R)
          (reciprocalSquareMultiplier K R)‖ ≤
        2 * C * Real.sqrt (K : ℝ) / (Q : ℝ) := by
    have hRReal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRpos
    have hQRReal : (Q : ℝ) ≤ (R : ℝ) := by exact_mod_cast hQR.le
    have hinv : 1 / (R : ℝ) ≤ 1 / (Q : ℝ) := by
      exact one_div_le_one_div_of_le (by positivity) hQRReal
    calc
      ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R)
          (reciprocalSquareMultiplier K R)‖ ≤
          ‖euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R‖ *
            ‖reciprocalSquareMultiplier K R‖ :=
        norm_euclideanCoordinateMul_le _ _
      _ ≤ (2 * C * Real.sqrt (K : ℝ) * (R : ℝ)) *
          (1 / (R : ℝ) ^ 2) := by
        exact mul_le_mul hterminalRaw hterminalWeight
          (norm_nonneg _) (by positivity)
      _ = (2 * C * Real.sqrt (K : ℝ)) * (1 / (R : ℝ)) := by
        field_simp
      _ ≤ (2 * C * Real.sqrt (K : ℝ)) * (1 / (Q : ℝ)) :=
        mul_le_mul_of_nonneg_left hinv hfactor
      _ = 2 * C * Real.sqrt (K : ℝ) / (Q : ℝ) := by ring
  have hvariationPoint (q : ℕ) (hq : q ∈ Finset.Ico (Q + 1) R) :
      ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q)
          (reciprocalSquareMultiplier K q -
            reciprocalSquareMultiplier K (q + 1))‖ ≤
        (2 * C * Real.sqrt (K : ℝ)) *
          ((q : ℝ) *
            (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2)) := by
    have hqBounds := Finset.mem_Ico.mp hq
    have hQq : Q < q := by omega
    have hqT : q ≤ T := hqBounds.2.le.trans hRT
    have hraw := norm_euclideanIntervalPartialSum_raw_le_of_prefixEstimate
      C K T Q q hCK hQ hQq hqT
    have hweight := norm_reciprocalSquareMultiplier_sub_succ_le K q
      (hQ.trans hQq)
    calc
      ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q)
          (reciprocalSquareMultiplier K q -
            reciprocalSquareMultiplier K (q + 1))‖ ≤
          ‖euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q‖ *
            ‖reciprocalSquareMultiplier K q -
              reciprocalSquareMultiplier K (q + 1)‖ :=
        norm_euclideanCoordinateMul_le _ _
      _ ≤ (2 * C * Real.sqrt (K : ℝ) * (q : ℝ)) *
          (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2) := by
        exact mul_le_mul hraw hweight (norm_nonneg _)
          (mul_nonneg hfactor (by positivity))
      _ = (2 * C * Real.sqrt (K : ℝ)) *
          ((q : ℝ) *
            (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2)) := by ring
  have hvariation :
      (∑ q ∈ Finset.Ico (Q + 1) R,
        ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q)
          (reciprocalSquareMultiplier K q -
            reciprocalSquareMultiplier K (q + 1))‖) ≤
        4 * C * Real.sqrt (K : ℝ) / (Q : ℝ) := by
    have hsum := sum_reciprocalSquare_weightedVariation_le
      (Q + 1) R (by omega) hStartEnd
    have hQsuccInv : 1 / ((Q + 1 : ℕ) : ℝ) ≤ 1 / (Q : ℝ) := by
      apply one_div_le_one_div_of_le (by positivity)
      norm_num
    calc
      (∑ q ∈ Finset.Ico (Q + 1) R,
          ‖euclideanCoordinateMul
            (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q)
            (reciprocalSquareMultiplier K q -
              reciprocalSquareMultiplier K (q + 1))‖) ≤
          ∑ q ∈ Finset.Ico (Q + 1) R,
            (2 * C * Real.sqrt (K : ℝ)) *
              ((q : ℝ) *
                (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro q hq
        exact hvariationPoint q hq
      _ = (2 * C * Real.sqrt (K : ℝ)) *
          (∑ q ∈ Finset.Ico (Q + 1) R,
            (q : ℝ) *
              (1 / (q : ℝ) ^ 2 - 1 / ((q + 1 : ℕ) : ℝ) ^ 2)) := by
        rw [Finset.mul_sum]
      _ ≤ (2 * C * Real.sqrt (K : ℝ)) *
          (2 / ((Q + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum hfactor
      _ ≤ (2 * C * Real.sqrt (K : ℝ)) * (2 / (Q : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hfactor
        calc
          2 / ((Q + 1 : ℕ) : ℝ) =
              2 * (1 / ((Q + 1 : ℕ) : ℝ)) := by ring
          _ ≤ 2 * (1 / (Q : ℝ)) :=
            mul_le_mul_of_nonneg_left hQsuccInv (by norm_num)
          _ = 2 / (Q : ℝ) := by ring
      _ = 4 * C * Real.sqrt (K : ℝ) / (Q : ℝ) := by ring
  rw [sum_nearRamanujanVectorTerm_eq_raw_abel K (Q + 1) R hStartEnd]
  calc
    ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R)
          (reciprocalSquareMultiplier K R) +
        ∑ q ∈ Finset.Ico (Q + 1) R,
          euclideanCoordinateMul
            (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q)
            (reciprocalSquareMultiplier K q -
              reciprocalSquareMultiplier K (q + 1))‖ ≤
        ‖euclideanCoordinateMul
          (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) R)
          (reciprocalSquareMultiplier K R)‖ +
        ∑ q ∈ Finset.Ico (Q + 1) R,
          ‖euclideanCoordinateMul
            (euclideanIntervalPartialSum (rawRamanujanVectorTerm K) (Q + 1) q)
            (reciprocalSquareMultiplier K q -
              reciprocalSquareMultiplier K (q + 1))‖ := by
      exact (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ 2 * C * Real.sqrt (K : ℝ) / (Q : ℝ) +
        4 * C * Real.sqrt (K : ℝ) / (Q : ℝ) :=
      add_le_add hterminal hvariation
    _ = 6 * C * Real.sqrt (K : ℝ) / (Q : ℝ) := by ring

/-- Complete bridge from the norm-form prefix estimate to the finite
near-resonant multiplier. -/
theorem norm_finiteNearRamanujanMultiplierVector_le_of_prefixEstimate
    (C a ε : ℝ) (K T Q U : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K T)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQU : Q < U) (hUT : U ≤ T) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      (6 * C * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        (64 * Real.pi * nearProfileDecayConstant) := by
  have hStartEnd : Q + 1 ≤ U := by omega
  apply norm_finiteNearRamanujanMultiplierVector_le_of_partialSum
    a ε K (Q + 1) U
      (6 * C * Real.sqrt (K : ℝ) / (Q : ℝ))
      ha hε haε hK (by omega) hStartEnd
  intro R hR
  have hRBounds := Finset.mem_Icc.mp hR
  have hQR : Q < R := by omega
  have hRT : R ≤ T := hRBounds.2.trans hUT
  exact norm_sum_nearRamanujanVectorTerm_tail_le_of_prefixEstimate
    C K T Q R hCK hQ hQR hRT

/-- Complete bridge directly from the second-moment interface to the finite
near-resonant multiplier. -/
theorem norm_finiteNearRamanujanMultiplierVector_le_of_secondMomentEstimate
    (D a ε : ℝ) (K T Q U : ℕ)
    (hCK : RamanujanPrefixSecondMomentEstimate D K T)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQU : Q < U) (hUT : U ≤ T) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      (6 * Real.sqrt D * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        (64 * Real.pi * nearProfileDecayConstant) := by
  exact norm_finiteNearRamanujanMultiplierVector_le_of_prefixEstimate
    (Real.sqrt D) a ε K T Q U hCK.toL2
      ha hε haε hK hQ hQU hUT

/-- Source-faithful endpoint: a proof of the Chan--Kumchev estimate on the
full initial frequency interval implies the finite near-resonant multiplier
bound with no further analytic hypothesis. -/
theorem norm_finiteNearRamanujanMultiplierVector_le_of_chanKumchev
    (D a ε : ℝ) (K T Q U : ℕ)
    (hCK : ChanKumchevInitialSecondMomentEstimate D K T)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQU : Q < U) (hUT : U ≤ T) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      (6 * Real.sqrt D * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        (64 * Real.pi * nearProfileDecayConstant) := by
  exact norm_finiteNearRamanujanMultiplierVector_le_of_secondMomentEstimate
    D a ε K T Q U hCK.toDyadic ha hε haε hK hQ hQU hUT

end

end Erdos1002
