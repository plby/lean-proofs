import ErdosProblems.Erdos448.TauInvCorrection448
import ErdosProblems.Erdos448.Prop3WeightedT448

open scoped BigOperators ArithmeticFunction.Omega
open Finset

namespace Prop3ClosePair448

/-- The number of prime factors of `n` below `Y`, counted with
multiplicity.  This is the finite version of the Erdős--Tenenbaum
quantity `Ω(n,Y)`. -/
noncomputable def truncatedOmega (n Y : ℕ) : ℕ :=
  (n.primeFactorsList.filter fun p ↦ p < Y).length

/-- The specialized weight `2^(-Ω(n,Y))`, written with a natural power
to avoid any ambiguity about real exponentiation. -/
noncomputable def halfTruncatedOmegaWeight (n Y : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ truncatedOmega n Y

lemma halfTruncatedOmegaWeight_nonneg (n Y : ℕ) :
    0 ≤ halfTruncatedOmegaWeight n Y := by
  unfold halfTruncatedOmegaWeight
  positivity

lemma halfTruncatedOmegaWeight_two_pow (n k : ℕ) :
    halfTruncatedOmegaWeight n (2 ^ k) = Prop3WeightedT448.omegaWeight k n := by
  unfold halfTruncatedOmegaWeight truncatedOmega
  rw [Prop3WeightedT448.omegaWeight, Prop3WeightedT448.omegaBelow,
    zpow_neg, zpow_natCast, one_div, inv_pow]

/-- The remaining close-pair sum in the third mean-value application of
Erdős--Tenenbaum Proposition 3, after specializing
`σ = θ = 2` and `y = 1/2`.

The outer variable is in the `k`-th dyadic block and the inner variable is
in the one-sided close interval `(d,2d)`. -/
noncomputable def dyadicClosePairMean (w₃ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)),
    ∑ d' ∈ Finset.Ioo d (2 * d),
      halfTruncatedOmegaWeight d' (2 ^ k) * w₃ (d * d')

/-- Finite assembly of the third close-pair mean estimate in Proposition 3.

The hypothesis `hshift` is precisely the specialized output of the third
application of the shifted Halberstam--Richert lemma, with `d` as shift.  It
introduces another multiplicative weight `w₄` of divisor-reciprocal type.
The hypothesis `hmean` is the ordinary Halberstam--Richert mean bound for
that output weight on the dyadic block.  Their exponents `-3/4` and `-1/2`
add to the required `-5/4`.

The theorem performs all interval restriction, summation, constant, dyadic
power, and real-power bookkeeping.  In particular, there is no hidden
asymptotic notation in its conclusion. -/
theorem dyadicClosePairMean_le
    (w₃ w₄ : ℕ → ℝ) (Cshift Cmean : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hCshift : 0 ≤ Cshift)
    (hshift : ∀ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)),
      (∑ d' ∈ Finset.Ioo d (2 * d),
          halfTruncatedOmegaWeight d' (2 ^ k) * w₃ (d * d')) ≤
        Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d)
    (hmean :
      (∑ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)), w₄ d) ≤
        Cmean * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(1 : ℝ) / 2)) :
    dyadicClosePairMean w₃ k ≤
      (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  have hkReal : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hfactorNonneg :
      0 ≤ Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) := by
    positivity
  have hkPowers :
      (k : ℝ) ^ (-(3 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 2) =
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
    rw [← Real.rpow_add hkReal]
    congr 1
    norm_num
  have htwoPowers :
      (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) =
        (2 : ℝ) ^ (2 * k) := by
    norm_num [two_mul, pow_add]
  calc
    dyadicClosePairMean w₃ k
        ≤ ∑ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)),
            Cshift * ((2 ^ k : ℕ) : ℝ) *
              (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d := by
          unfold dyadicClosePairMean
          exact Finset.sum_le_sum hshift
    _ = (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) *
          (∑ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)), w₄ d) := by
          rw [Finset.mul_sum]
    _ ≤ (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) *
          (Cmean * ((2 ^ k : ℕ) : ℝ) *
            (k : ℝ) ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hmean hfactorNonneg
    _ = (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) := by
      rw [← hkPowers, ← htwoPowers]
      ring

/-- The same estimate with the shifted mean supplied on a fixed rectangular
range.  This is the direct consumer interface for a finite
Halberstam--Richert lemma: positivity restricts its `[1,2^(k+2)]` sum to the
moving close interval `(d,2d)` before `dyadicClosePairMean_le` combines it
with the mean of `w₄`. -/
theorem dyadicClosePairMean_le_of_rectangular_shifted_mean
    (w₃ w₄ : ℕ → ℝ) (Cshift Cmean : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hCshift : 0 ≤ Cshift)
    (hw₃ : ∀ n, 0 ≤ w₃ n)
    (hshift : ∀ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)),
      (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
          halfTruncatedOmegaWeight d' (2 ^ k) * w₃ (d * d')) ≤
        Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d)
    (hmean :
      (∑ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)), w₄ d) ≤
        Cmean * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(1 : ℝ) / 2)) :
    dyadicClosePairMean w₃ k ≤
      (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  apply dyadicClosePairMean_le w₃ w₄ Cshift Cmean k hk hCshift
  · intro d hd
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (hshift d hd)
    · intro d' hd'
      have hdMem := Finset.mem_Ioo.mp hd
      have hd'Mem := Finset.mem_Ioo.mp hd'
      rw [Finset.mem_Icc]
      constructor
      · omega
      · rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        omega
    · intro d' hd' _
      exact mul_nonneg (halfTruncatedOmegaWeight_nonneg _ _) (hw₃ _)
  · exact hmean

/-- Transposed form of `dyadicClosePairMean`.  This is the order in which
the primary proof performs the third application of its shifted mean-value
lemma: fix `d'`, first sum `w₃ (d*d')` over `d`, and retain the truncated
Omega weight for the outer `d'`-sum. -/
noncomputable def transposedDyadicClosePairMean (w₃ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d' ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 2)),
    halfTruncatedOmegaWeight d' (2 ^ k) *
      ∑ d ∈ (Finset.Ioo (2 ^ k) (2 ^ (k + 1))).filter
          (fun d ↦ d < d' ∧ d' < 2 * d),
        w₃ (d * d')

/-- Reversing the two finite sums introduces the widened range
`2^k < d' < 2^(k+2)` and no loss. -/
theorem dyadicClosePairMean_eq_transposed (w₃ : ℕ → ℝ) (k : ℕ) :
    dyadicClosePairMean w₃ k = transposedDyadicClosePairMean w₃ k := by
  let D : Finset ℕ := Finset.Ioo (2 ^ k) (2 ^ (k + 1))
  let E : Finset ℕ := Finset.Ioo (2 ^ k) (2 ^ (k + 2))
  have hinterval : ∀ d ∈ D,
      Finset.Ioo d (2 * d) = E.filter (fun d' ↦ d < d' ∧ d' < 2 * d) := by
    intro d hd
    apply Finset.ext
    intro d'
    rw [Finset.mem_Ioo, Finset.mem_filter]
    change (d < d' ∧ d' < 2 * d) ↔
      (d' ∈ E ∧ (d < d' ∧ d' < 2 * d))
    rw [show E = Finset.Ioo (2 ^ k) (2 ^ (k + 2)) by rfl, Finset.mem_Ioo]
    constructor
    · intro hd'
      have hdD : 2 ^ k < d ∧ d < 2 ^ (k + 1) := by
        simpa [D] using hd
      have hd'Upper : d' < 2 ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        omega
      exact ⟨⟨by omega, hd'Upper⟩, hd'⟩
    · exact fun hd' ↦ hd'.2
  calc
    dyadicClosePairMean w₃ k =
        ∑ d ∈ D, ∑ d' ∈ E.filter (fun d' ↦ d < d' ∧ d' < 2 * d),
          halfTruncatedOmegaWeight d' (2 ^ k) * w₃ (d * d') := by
      unfold dyadicClosePairMean
      apply Finset.sum_congr
      · rfl
      · intro d hd
        rw [hinterval d hd]
    _ = ∑ d' ∈ E,
          ∑ d ∈ D.filter (fun d ↦ d < d' ∧ d' < 2 * d),
            halfTruncatedOmegaWeight d' (2 ^ k) * w₃ (d * d') := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = transposedDyadicClosePairMean w₃ k := by
      unfold transposedDyadicClosePairMean
      dsimp [D, E]
      apply Finset.sum_congr rfl
      intro d' hd'
      rw [Finset.mul_sum]

/-- The specialized third close-pair estimate in the exact order used by
Erdős--Tenenbaum.

`hshift` is the third shifted Halberstam--Richert application.  It has the
ordinary divisor-reciprocal exponent `-1/2` and produces a correction weight
`w₄`.  `hweightedMean` is the Euler-product estimate for the outer
`2^(-Ω(d',2^k)) w₄(d')` sum and has exponent `-3/4`.  This theorem
combines them into the requested explicit `k^(-5/4)` bound. -/
theorem dyadicClosePairMean_le_of_transposed_HR
    (w₃ w₄ : ℕ → ℝ) (Cshift Cweighted : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hCshift : 0 ≤ Cshift)
    (hshift : ∀ d' ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 2)),
      (∑ d ∈ (Finset.Ioo (2 ^ k) (2 ^ (k + 1))).filter
          (fun d ↦ d < d' ∧ d' < 2 * d),
        w₃ (d * d')) ≤
      Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(1 : ℝ) / 2) * w₄ d')
    (hweightedMean :
      (∑ d' ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 2)),
          halfTruncatedOmegaWeight d' (2 ^ k) * w₄ d') ≤
        Cweighted * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) :
    dyadicClosePairMean w₃ k ≤
      (Cshift * Cweighted) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  have hkReal : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hfactorNonneg :
      0 ≤ Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(1 : ℝ) / 2) := by
    positivity
  have hkPowers :
      (k : ℝ) ^ (-(1 : ℝ) / 2) *
          (k : ℝ) ^ (-(3 : ℝ) / 4) =
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
    rw [← Real.rpow_add hkReal]
    congr 1
    norm_num
  have htwoPowers :
      (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) =
        (2 : ℝ) ^ (2 * k) := by
    norm_num [two_mul, pow_add]
  rw [dyadicClosePairMean_eq_transposed]
  calc
    transposedDyadicClosePairMean w₃ k ≤
        ∑ d' ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 2)),
          halfTruncatedOmegaWeight d' (2 ^ k) *
            (Cshift * ((2 ^ k : ℕ) : ℝ) *
              (k : ℝ) ^ (-(1 : ℝ) / 2) * w₄ d') := by
      unfold transposedDyadicClosePairMean
      refine Finset.sum_le_sum ?_
      intro d' hd'
      exact mul_le_mul_of_nonneg_left (hshift d' hd')
        (halfTruncatedOmegaWeight_nonneg _ _)
    _ = (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(1 : ℝ) / 2)) *
          (∑ d' ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 2)),
            halfTruncatedOmegaWeight d' (2 ^ k) * w₄ d') := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d' hd'
      ring
    _ ≤ (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(1 : ℝ) / 2)) *
          (Cweighted * ((2 ^ k : ℕ) : ℝ) *
            (k : ℝ) ^ (-(3 : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hweightedMean hfactorNonneg
    _ = (Cshift * Cweighted) * (2 : ℝ) ^ (2 * k) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) := by
      rw [← hkPowers, ← htwoPowers]
      ring

/-! ## Literal primary-source orientation

The paper's displayed third pair sum is symmetric, keeps the dyadic
restriction on `d`, and puts the truncated-Omega weight on that same
variable.  The preceding results retain the originally delegated one-sided
orientation.  The following definition and theorem record the corrected
primary-source form as well. -/

/-- Specialized literal pair sum: `d` is dyadic, `d ≠ d'`, and
`1/2 < d/d' < 2`.  Cross multiplication expresses the latter condition
without division or rounding. -/
noncomputable def sourceDyadicClosePairMean (w₃ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ioo (2 ^ k) (2 ^ (k + 1)),
    ∑ d' ∈ (Finset.Icc 1 (2 ^ (k + 2))).filter
        (fun d' ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
      halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d')

/-- Exact finite assembly of the corrected source sum.  `hshift` is the
weighted shifted Halberstam--Richert estimate in the dyadic variable `d`;
`hmean` is the ordinary divisor-reciprocal mean of the resulting correction
weight in the outer shift `d'`. -/
theorem sourceDyadicClosePairMean_le_of_HR
    (w₃ w₄ : ℕ → ℝ) (Cshift Cmean : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hCshift : 0 ≤ Cshift)
    (hshift : ∀ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
      (∑ d ∈ (Finset.Ioo (2 ^ k) (2 ^ (k + 1))).filter
          (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
        halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d')) ≤
      Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d')
    (hmean :
      (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)), w₄ d') ≤
        Cmean * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(1 : ℝ) / 2)) :
    sourceDyadicClosePairMean w₃ k ≤
      (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  have hkReal : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hfactorNonneg :
      0 ≤ Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) := by
    positivity
  have hkPowers :
      (k : ℝ) ^ (-(3 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 2) =
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
    rw [← Real.rpow_add hkReal]
    congr 1
    norm_num
  have htwoPowers :
      (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) =
        (2 : ℝ) ^ (2 * k) := by
    norm_num [two_mul, pow_add]
  have htranspose : sourceDyadicClosePairMean w₃ k =
      ∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
        ∑ d ∈ (Finset.Ioo (2 ^ k) (2 ^ (k + 1))).filter
            (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
          halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d') := by
    unfold sourceDyadicClosePairMean
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [htranspose]
  calc
    (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
        ∑ d ∈ (Finset.Ioo (2 ^ k) (2 ^ (k + 1))).filter
            (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
          halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d')) ≤
        ∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
          Cshift * ((2 ^ k : ℕ) : ℝ) *
            (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d' :=
      Finset.sum_le_sum hshift
    _ = (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) *
          (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)), w₄ d') := by
      rw [Finset.mul_sum]
    _ ≤ (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) *
          (Cmean * ((2 ^ k : ℕ) : ℝ) *
            (k : ℝ) ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hmean hfactorNonneg
    _ = (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) := by
      rw [← hkPowers, ← htwoPowers]
      ring

/-! ## Concrete correction-weight consumer -/

/-- The exact multiplicative correction produced by the weighted third
application of Erdős--Tenenbaum Lemma 2. -/
noncomputable def sourceCorrectionWeight
    (u : ArithmeticFunction ℝ) (k : ℕ) : ℕ → ℝ :=
  TauInvCorrection448.correctionWeight u (Prop3WeightedT448.omegaWeightAF k)

/-- The paper's hybrid shift factor: at each prime power it takes the larger
of the correction and the original weight, then extends those local values
multiplicatively.  This simultaneously covers primes below and above the
finite Euler-product cutoff. -/
noncomputable def sourceHybridWeight
    (u : ArithmeticFunction ℝ) (k : ℕ) : ℕ → ℝ :=
  TauInvCorrection448.maxPrimePowerWeight (sourceCorrectionWeight u k) u

/-- The logarithmic-error constant of the hybrid correction weight. -/
noncomputable def sourceHybridTypeConstant (C : ℝ) : ℝ :=
  max (3 * (16 + 17 * C)) C

/-- The explicit ordinary dyadic mean constant for the hybrid correction. -/
noncomputable def sourceHybridMeanConstant (C : ℝ) : ℝ :=
  4 * TauInvTypeMean448.meanConstant (sourceHybridTypeConstant C) /
    Real.sqrt (Real.log 2)

/-- Concrete wrapper for `sourceDyadicClosePairMean_le_of_HR`.

The only input retained is the weighted shifted estimate furnished by the
unconditional Lemma 2 engine.  The output correction `w₄`, its preservation
of tau-inverse type, the hybrid treatment of primes beyond the cutoff, and
the entire outer `k^(-1/2)` mean estimate are constructed and discharged by
the proved correction and mean-value packages. -/
theorem sourceDyadicClosePairMean_le_of_weighted_shift
    (u : ArithmeticFunction ℝ) {C Cshift : ℝ}
    (huType : TauInvTypeMean448.IsTauInverseLogType u C)
    (hCshift : 0 ≤ Cshift) (k : ℕ) (hk : 1 ≤ k)
    (hshift : ∀ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
      (∑ d ∈ (Finset.Ioo (2 ^ k) (2 ^ (k + 1))).filter
          (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
        halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) ≤
      Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) * sourceHybridWeight u k d') :
    sourceDyadicClosePairMean u k ≤
      (Cshift * sourceHybridMeanConstant C) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  let v : ArithmeticFunction ℝ := Prop3WeightedT448.omegaWeightAF k
  have hvOne : v 1 = 1 := by
    simpa [v] using Prop3WeightedT448.omegaWeightAF_one k
  have hvNonneg : ∀ n, 0 ≤ v n := by
    intro n
    exact Prop3WeightedT448.omegaWeightAF_nonneg k n
  have hvLeOne : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1 := by
    intro p hp j
    exact Prop3WeightedT448.omegaWeightAF_le_one k (p ^ j)
  have hcorr : TauInvTypeMean448.IsTauInverseLogType
      (TauInvCorrection448.correctionWeight u v) (3 * (16 + 17 * C)) :=
    TauInvCorrection448.correctionWeight_meanType
      u v huType hvOne hvNonneg hvLeOne
  have hhybrid : TauInvTypeMean448.IsTauInverseLogType
      (TauInvCorrection448.maxPrimePowerWeight
        (TauInvCorrection448.correctionWeight u v) u)
      (sourceHybridTypeConstant C) := by
    simpa [sourceHybridTypeConstant] using
      TauInvCorrection448.maxPrimePowerWeight_meanType hcorr huType
  have hmean := TauInvTypeMean448.mean_dyadic_le hhybrid k hk
  apply sourceDyadicClosePairMean_le_of_HR
    u (sourceHybridWeight u k) Cshift (sourceHybridMeanConstant C) k
    hk hCshift hshift
  simpa [sourceHybridWeight, sourceCorrectionWeight, sourceHybridMeanConstant, v]
    using hmean

/-! ## Formal half-open dyadic bins -/

/-- The close-pair mean using exactly the half-open formal bin
`[2^k,2^(k+1))` represented by `Finset.Ico`.  This is the convention used by
`Nat.log 2` and hence by the formal definition of `tauPlus`. -/
noncomputable def formalDyadicClosePairMean (w₃ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)),
    ∑ d' ∈ (Finset.Icc 1 (2 ^ (k + 2))).filter
        (fun d' ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
      halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d')

/-- Finite close-pair assembly for the exact formal half-open dyadic bin.
The proof is the same finite transposition and exponent addition as in the
primary-source version; only `Ioo` is replaced by `Ico`. -/
theorem formalDyadicClosePairMean_le_of_HR
    (w₃ w₄ : ℕ → ℝ) (Cshift Cmean : ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hCshift : 0 ≤ Cshift)
    (hshift : ∀ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
      (∑ d ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
        halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d')) ≤
      Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d')
    (hmean :
      (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)), w₄ d') ≤
        Cmean * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(1 : ℝ) / 2)) :
    formalDyadicClosePairMean w₃ k ≤
      (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  have hkReal : (0 : ℝ) < k := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hfactorNonneg :
      0 ≤ Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) := by
    positivity
  have hkPowers :
      (k : ℝ) ^ (-(3 : ℝ) / 4) *
          (k : ℝ) ^ (-(1 : ℝ) / 2) =
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
    rw [← Real.rpow_add hkReal]
    congr 1
    norm_num
  have htwoPowers :
      (((2 ^ k : ℕ) : ℝ) * ((2 ^ k : ℕ) : ℝ)) =
        (2 : ℝ) ^ (2 * k) := by
    norm_num [two_mul, pow_add]
  have htranspose : formalDyadicClosePairMean w₃ k =
      ∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
        ∑ d ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
            (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
          halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d') := by
    unfold formalDyadicClosePairMean
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [htranspose]
  calc
    (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
        ∑ d ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
            (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
          halfTruncatedOmegaWeight d (2 ^ k) * w₃ (d * d')) ≤
        ∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
          Cshift * ((2 ^ k : ℕ) : ℝ) *
            (k : ℝ) ^ (-(3 : ℝ) / 4) * w₄ d' :=
      Finset.sum_le_sum hshift
    _ = (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) *
          (∑ d' ∈ Finset.Icc 1 (2 ^ (k + 2)), w₄ d') := by
      rw [Finset.mul_sum]
    _ ≤ (Cshift * ((2 ^ k : ℕ) : ℝ) *
          (k : ℝ) ^ (-(3 : ℝ) / 4)) *
          (Cmean * ((2 ^ k : ℕ) : ℝ) *
            (k : ℝ) ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hmean hfactorNonneg
    _ = (Cshift * Cmean) * (2 : ℝ) ^ (2 * k) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) := by
      rw [← hkPowers, ← htwoPowers]
      ring

/-- Concrete correction-weight wrapper for formal half-open dyadic bins. -/
theorem formalDyadicClosePairMean_le_of_weighted_shift
    (u : ArithmeticFunction ℝ) {C Cshift : ℝ}
    (huType : TauInvTypeMean448.IsTauInverseLogType u C)
    (hCshift : 0 ≤ Cshift) (k : ℕ) (hk : 1 ≤ k)
    (hshift : ∀ d' ∈ Finset.Icc 1 (2 ^ (k + 2)),
      (∑ d ∈ (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
          (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d),
        halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) ≤
      Cshift * ((2 ^ k : ℕ) : ℝ) *
        (k : ℝ) ^ (-(3 : ℝ) / 4) * sourceHybridWeight u k d') :
    formalDyadicClosePairMean u k ≤
      (Cshift * sourceHybridMeanConstant C) * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  let v : ArithmeticFunction ℝ := Prop3WeightedT448.omegaWeightAF k
  have hvOne : v 1 = 1 := by
    simpa [v] using Prop3WeightedT448.omegaWeightAF_one k
  have hvNonneg : ∀ n, 0 ≤ v n := by
    intro n
    exact Prop3WeightedT448.omegaWeightAF_nonneg k n
  have hvLeOne : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, v (p ^ j) ≤ 1 := by
    intro p hp j
    exact Prop3WeightedT448.omegaWeightAF_le_one k (p ^ j)
  have hcorr : TauInvTypeMean448.IsTauInverseLogType
      (TauInvCorrection448.correctionWeight u v) (3 * (16 + 17 * C)) :=
    TauInvCorrection448.correctionWeight_meanType
      u v huType hvOne hvNonneg hvLeOne
  have hhybrid : TauInvTypeMean448.IsTauInverseLogType
      (TauInvCorrection448.maxPrimePowerWeight
        (TauInvCorrection448.correctionWeight u v) u)
      (sourceHybridTypeConstant C) := by
    simpa [sourceHybridTypeConstant] using
      TauInvCorrection448.maxPrimePowerWeight_meanType hcorr huType
  have hmean := TauInvTypeMean448.mean_dyadic_le hhybrid k hk
  apply formalDyadicClosePairMean_le_of_HR
    u (sourceHybridWeight u k) Cshift (sourceHybridMeanConstant C) k
    hk hCshift hshift
  simpa [sourceHybridWeight, sourceCorrectionWeight, sourceHybridMeanConstant, v]
    using hmean

/-! ## Unconditional sharp close-pair estimate -/

/-- The explicit constant obtained by combining the unconditional weighted
shifted mean with the ordinary mean of its hybrid correction weight. -/
noncomputable def sharpFormalClosePairConstant : ℝ :=
  Prop3WeightedT448.weightedShiftedDyadicConstant 1 1 1 *
    (4 * TauInvTypeMean448.meanConstant 99 / Real.sqrt (Real.log 2))

/-- Fully unconditional form of the third Erdős--Tenenbaum close-pair mean
estimate on the exact formal bin `[2^k,2^(k+1))`.

The inner filtered sum is restricted from the formal dyadic block to the
range of `sharpWeightedTSum_dyadic_le`.  On positive integers the roughness
indicator at `2` is one, so its kernel is exactly
`2^(-Ω(d,2^k)) w₃(dd')`.  The outer mean is then discharged by the bundled
tau-inverse type of the sharp hybrid correction. -/
theorem formalDyadicClosePairMean_sharp_le (k : ℕ) (hk : 1 ≤ k) :
    formalDyadicClosePairMean
        Prop3WeightedT448.sharpShiftedReciprocalWeightAF k ≤
      sharpFormalClosePairConstant * (2 : ℝ) ^ (2 * k) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) := by
  let u : ArithmeticFunction ℝ :=
    Prop3WeightedT448.sharpShiftedReciprocalWeightAF
  let w₄ : ℕ → ℝ :=
    Prop3WeightedT448.hybridCorrectionWeight u
      (Prop3WeightedT448.omegaWeightAF k)
  apply formalDyadicClosePairMean_le_of_HR
    u w₄ (Prop3WeightedT448.weightedShiftedDyadicConstant 1 1 1)
      (4 * TauInvTypeMean448.meanConstant 99 / Real.sqrt (Real.log 2))
      k hk
  · exact Prop3WeightedT448.weightedShiftedDyadicConstant_nonneg
      zero_le_one zero_le_one zero_le_one
  · intro d' hd'
    have hd'Pos : 0 < d' :=
      lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hd').1
    have hd'0 : d' ≠ 0 := hd'Pos.ne'
    let D : Finset ℕ :=
      (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter
        (fun d ↦ d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d)
    have hsub : D ⊆ Finset.Ico 1 (2 ^ (k + 2) + 1) := by
      intro d hd
      have hdBin : d ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) :=
        (Finset.mem_filter.mp hd).1
      have hdBounds := Finset.mem_Ico.mp hdBin
      apply Finset.mem_Ico.mpr
      constructor
      · have hpowPos : 0 < 2 ^ k := by positivity
        omega
      · have hpowLe : 2 ^ (k + 1) ≤ 2 ^ (k + 2) := by
          exact Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hrestricted :
        (∑ d ∈ D,
            halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) ≤
          Prop3WeightedT448.weightedTSum u d' k 2
            (2 ^ (k + 2) + 1) := by
      calc
        (∑ d ∈ D,
            halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) =
            ∑ d ∈ D,
              Prop3WeightedT448.weightedTKernel u d' k 2 d := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdBin : d ∈ Finset.Ico (2 ^ k) (2 ^ (k + 1)) :=
            (Finset.mem_filter.mp hd).1
          have hdPos : 0 < d := by
            have hpowPos : 0 < 2 ^ k := by positivity
            have hdLower := (Finset.mem_Ico.mp hdBin).1
            omega
          rw [halfTruncatedOmegaWeight_two_pow,
            Prop3WeightedT448.weightedTKernel,
            Prop3WeightedT448.roughIndicator_two_of_ne_zero hdPos.ne']
          ring
        _ ≤ ∑ d ∈ Finset.Ico 1 (2 ^ (k + 2) + 1),
              Prop3WeightedT448.weightedTKernel u d' k 2 d := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro d hd hnot
          exact Prop3WeightedT448.weightedTKernel_nonneg u
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF_nonneg d' k 2 d
        _ = Prop3WeightedT448.weightedTSum u d' k 2
              (2 ^ (k + 2) + 1) := by
          rfl
    change (∑ d ∈ D,
        halfTruncatedOmegaWeight d (2 ^ k) * u (d * d')) ≤ _
    exact hrestricted.trans
      (Prop3WeightedT448.sharpWeightedTSum_dyadic_le hd'0 k hk)
  · have hmean := TauInvTypeMean448.mean_dyadic_le
      (Prop3WeightedT448.sharpHybridCorrection_meanType k) k hk
    simpa [w₄, u] using hmean

end Prop3ClosePair448

#print axioms Prop3ClosePair448.sourceDyadicClosePairMean_le_of_HR
#print axioms Prop3ClosePair448.sourceDyadicClosePairMean_le_of_weighted_shift
#print axioms Prop3ClosePair448.formalDyadicClosePairMean_le_of_weighted_shift
#print axioms Prop3ClosePair448.formalDyadicClosePairMean_sharp_le
