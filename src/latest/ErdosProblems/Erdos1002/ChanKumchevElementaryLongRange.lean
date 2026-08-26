import ErdosProblems.Erdos1002.ChanKumchevInterface

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The exact elementary obstruction in the Chan--Kumchev range

This file removes every avoidable hypothesis from the finite
pair-correlation argument in `ChanKumchevInterface`.  It proves the literal
elementary estimate

`‖C_X‖₂² ≤ (2K + 1 + X) X² + 2 X⁴`

on `1 ≤ n ≤ 2K`.  In particular, the desired bound with an absolute
constant follows whenever `X² = O(K)`.  For a general terminal point `T ≤ K`
we also record the strongest direct consequence of this argument, with the
explicit (non-uniform) constant `4 + 2 T²/K`.

The `2 X⁴` term is precisely the endpoint-error term that the analytic
Chan--Kumchev theorem cancels in the genuinely long range `X² ≫ K`.
Nothing in this file assumes that cancellation.
-/

open Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

/-- The diagonal part of the initial Ramanujan second moment, without any
relation between `X` and `K`. -/
theorem sum_initialRamanujan_diagonal_le_general
    (K X : ℕ) :
    (∑ q ∈ Finset.Icc 1 X,
      (initialRamanujanPairCorrelation K q q).re) ≤
      ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) ^ 2 := by
  have hcard : (Finset.Icc 1 X).card = X := by
    rw [Nat.card_Icc]
    omega
  have hpoint (q : ℕ) (hq : q ∈ Finset.Icc 1 X) :
      (initialRamanujanPairCorrelation K q q).re ≤
        ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) := by
    have hqBounds := Finset.mem_Icc.mp hq
    calc
      (initialRamanujanPairCorrelation K q q).re ≤
          (((2 * K + 1 + q) * Nat.totient q : ℕ) : ℝ) :=
        initialRamanujanPairCorrelation_self_re_le_linear K q (by omega)
      _ ≤ (((2 * K + 1 + X) * X : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul
          (Nat.add_le_add_left hqBounds.2 (2 * K + 1))
          ((Nat.totient_le q).trans hqBounds.2)
      _ = ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) := by
        push_cast
        ring
  calc
    (∑ q ∈ Finset.Icc 1 X,
        (initialRamanujanPairCorrelation K q q).re) ≤
        ∑ _q ∈ Finset.Icc 1 X,
          (((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact hpoint q hq
    _ = (X : ℝ) *
          (((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ)) := by
      rw [sum_const, nsmul_eq_mul, hcard]
    _ = ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) ^ 2 := by ring

/-- The absolute off-diagonal part of the initial Ramanujan second moment,
without using `X² ≤ K`. -/
theorem sum_abs_initialRamanujan_offDiagonal_le_general
    (K X : ℕ) :
    (∑ q ∈ Finset.Icc 1 X, ∑ q' ∈ Finset.Icc 1 X,
      if q ≠ q' then |(initialRamanujanPairCorrelation K q q').re|
      else 0) ≤
      2 * (X : ℝ) ^ 4 := by
  let mass : ℕ → ℝ := fun q ↦ (ArithmeticFunction.sigma 1 q : ℝ)
  have hmass (q : ℕ) : 0 ≤ mass q := by
    dsimp [mass]
    positivity
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
      _ = 2 * mass q * mass q' := by
        dsimp [mass]
        ring
  have hmassSum : (∑ q ∈ Finset.Icc 1 X, mass q) ≤ (X : ℝ) ^ 2 := by
    simpa only [mass] using! sum_sigma_one_Icc_le_square X
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
    _ = 2 * (X : ℝ) ^ 4 := by ring

/-- Fully unconditional elementary second-moment estimate.  The two terms
are respectively the complete-period diagonal and the total endpoint error
off the diagonal. -/
theorem norm_sq_initialRamanujanPrefixVector_le_elementary_general
    (K X : ℕ) :
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
      ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) ^ 2 +
        2 * (X : ℝ) ^ 4 := by
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
    _ ≤ ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) ^ 2 +
          2 * (X : ℝ) ^ 4 := by
      exact add_le_add
        (sum_initialRamanujan_diagonal_le_general K X)
        (by simpa only [O] using!
          sum_abs_initialRamanujan_offDiagonal_le_general K X)

/-- In the natural manuscript range `1 ≤ X ≤ K`, the preceding estimate
has the familiar elementary shape `4 K X² + 2 X⁴`. -/
theorem norm_sq_initialRamanujanPrefixVector_le_elementary_error
    (K X : ℕ) (hK : 0 < K) (hXK : X ≤ K) :
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
      4 * (K : ℝ) * (X : ℝ) ^ 2 + 2 * (X : ℝ) ^ 4 := by
  have hmainNat : 2 * K + 1 + X ≤ 4 * K := by omega
  calc
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
        ((2 * K + 1 + X : ℕ) : ℝ) * (X : ℝ) ^ 2 +
          2 * (X : ℝ) ^ 4 :=
      norm_sq_initialRamanujanPrefixVector_le_elementary_general K X
    _ ≤ 4 * (K : ℝ) * (X : ℝ) ^ 2 + 2 * (X : ℝ) ^ 4 := by
      gcongr
      exact_mod_cast hmainNat

/-! ## The divisor-square bound used beyond the analytic cutoff -/

/-- The divisor formula and `|mu| ≤ 1` give the manuscript's pointwise
terminal estimate `|C_X(n)| ≤ X tau(n)`.  All sums here are finite. -/
theorem abs_initialRawRamanujanBlockCoefficient_le_divisorCard
    (X n : ℕ) (hn : n ≠ 0) :
    |initialRawRamanujanBlockCoefficient X n| ≤
      (X : ℝ) * (n.divisors.card : ℝ) := by
  have hpoint (p : ℕ) (hp : p ∈ Finset.Icc 1 X) :
      |(ramanujanSum p (n : ℤ)).re| ≤
        ∑ a ∈ n.divisors, if a ∣ p then (a : ℝ) else 0 := by
    have hp0 : p ≠ 0 := by
      have hpOne : 1 ≤ p := (Finset.mem_Icc.mp hp).1
      omega
    rw [ramanujanSum_re_eq_sum_frequency_divisors p n hp0 hn]
    calc
      |∑ a ∈ n.divisors,
          if a ∣ p then
            (a : ℝ) * (ArithmeticFunction.moebius (p / a) : ℝ)
          else 0| ≤
          ∑ a ∈ n.divisors,
            |if a ∣ p then
              (a : ℝ) * (ArithmeticFunction.moebius (p / a) : ℝ)
            else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ n.divisors, if a ∣ p then (a : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro a _ha
        by_cases hap : a ∣ p
        · rw [if_pos hap, if_pos hap, abs_mul,
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a : ℝ))]
          have hmu :
              |(ArithmeticFunction.moebius (p / a) : ℝ)| ≤ 1 := by
            exact_mod_cast
              (ArithmeticFunction.abs_moebius_le_one (n := p / a))
          nlinarith
        · simp [hap]
  unfold initialRawRamanujanBlockCoefficient
  calc
    |∑ p ∈ Finset.Icc 1 X, (ramanujanSum p (n : ℤ)).re| ≤
        ∑ p ∈ Finset.Icc 1 X, |(ramanujanSum p (n : ℤ)).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.Icc 1 X,
          ∑ a ∈ n.divisors, if a ∣ p then (a : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = ∑ a ∈ n.divisors,
          ∑ p ∈ Finset.Icc 1 X, if a ∣ p then (a : ℝ) else 0 := by
      exact Finset.sum_comm
    _ = ∑ a ∈ n.divisors,
          (a : ℝ) * ((X / a : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      calc
        (∑ p ∈ Finset.Icc 1 X, if a ∣ p then (a : ℝ) else 0) =
            ∑ _p ∈ positiveMultiplesIcc X a, (a : ℝ) := by
          symm
          simpa only [positiveMultiplesIcc] using!
            Finset.sum_filter (s := Finset.Icc 1 X)
              (p := fun p ↦ a ∣ p) (f := fun _p ↦ (a : ℝ))
        _ = (a : ℝ) * ((positiveMultiplesIcc X a).card : ℝ) := by
          rw [sum_const, nsmul_eq_mul]
          ring
        _ = (a : ℝ) * ((X / a : ℕ) : ℝ) := by
          rw [card_positiveMultiplesIcc X a haPos]
    _ ≤ ∑ _a ∈ n.divisors, (X : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      have haPos : 0 < a := Nat.pos_of_mem_divisors ha
      exact_mod_cast Nat.mul_div_le X a
    _ = (X : ℝ) * (n.divisors.card : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
      ring

/-- Squaring the pointwise divisor bound and using the proved elementary
mean square of `tau` gives a source-faithful terminal estimate. -/
theorem norm_sq_initialRamanujanPrefixVector_le_divisorSquare
    (K X : ℕ) :
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
      (X : ℝ) ^ 2 *
        (((2 * K : ℕ) : ℝ) * (harmonic (2 * K) : ℝ) ^ 3) := by
  rw [norm_sq_initialRamanujanPrefixVector_eq_coefficients]
  calc
    (∑ n ∈ Finset.Icc 1 (2 * K),
        initialRawRamanujanBlockCoefficient X n ^ 2) ≤
        ∑ n ∈ Finset.Icc 1 (2 * K),
          ((X : ℝ) * (n.divisors.card : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn0 : n ≠ 0 := by
        have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        omega
      have habs := abs_initialRawRamanujanBlockCoefficient_le_divisorCard
        X n hn0
      calc
        initialRawRamanujanBlockCoefficient X n ^ 2 =
            |initialRawRamanujanBlockCoefficient X n| ^ 2 := by
          rw [sq_abs]
        _ ≤ ((X : ℝ) * (n.divisors.card : ℝ)) ^ 2 := by
          gcongr
    _ = (X : ℝ) ^ 2 *
        (∑ n ∈ Finset.Icc 1 (2 * K),
          ((n.divisors.card : ℕ) : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ ≤ (X : ℝ) ^ 2 *
        (((2 * K : ℕ) : ℝ) * (harmonic (2 * K) : ℝ) ^ 3) := by
      gcongr
      exact sum_divisor_card_sq_le_harmonic_cube (2 * K)

/-- Fully unconditional long-range interface with the classical elementary
`H_{2K}^3` loss.  This is useful for the terminal denominator range, but its
constant is not uniform in `K` and therefore is not the Chan--Kumchev input. -/
theorem chanKumchevInitialLongRangeEstimate_divisorSquare
    (K T : ℕ) :
    ChanKumchevInitialLongRangeEstimate
      (2 * (harmonic (2 * K) : ℝ) ^ 3) K T := by
  have hH : 0 ≤ (harmonic (2 * K) : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  refine ⟨mul_nonneg (by norm_num) (pow_nonneg hH 3), ?_⟩
  intro X _hX _hLong
  calc
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
        (X : ℝ) ^ 2 *
          (((2 * K : ℕ) : ℝ) * (harmonic (2 * K) : ℝ) ^ 3) :=
      norm_sq_initialRamanujanPrefixVector_le_divisorSquare K X
    _ = (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          (K : ℝ) * (X : ℝ) ^ 2 := by
      push_cast
      ring

/-- The same divisor-square argument actually controls every prefix, so it
also gives the complete initial-second-moment interface (with the explicit
harmonic loss). -/
theorem chanKumchevInitialSecondMomentEstimate_divisorSquare
    (K T : ℕ) :
    ChanKumchevInitialSecondMomentEstimate
      (2 * (harmonic (2 * K) : ℝ) ^ 3) K T := by
  have hH : 0 ≤ (harmonic (2 * K) : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    positivity
  refine ⟨mul_nonneg (by norm_num) (pow_nonneg hH 3), ?_⟩
  intro X _hX
  calc
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
        (X : ℝ) ^ 2 *
          (((2 * K : ℕ) : ℝ) * (harmonic (2 * K) : ℝ) ^ 3) :=
      norm_sq_initialRamanujanPrefixVector_le_divisorSquare K X
    _ = (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          (K : ℝ) * (X : ℝ) ^ 2 := by
      push_cast
      ring

/-- Fully unconditional near-multiplier consequence of the divisor-square
prefix estimate.  The factor `sqrt(2 H_{2K}^3)` is displayed rather than
hidden in big-O notation; Chan--Kumchev is needed precisely to remove it. -/
theorem norm_finiteNearRamanujanMultiplierVector_le_divisorSquare
    (a ε : ℝ) (K T Q U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQU : Q < U) (hUT : U ≤ T) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      (6 * Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (Q : ℝ)) *
        (64 * Real.pi * nearProfileDecayConstant) := by
  exact norm_finiteNearRamanujanMultiplierVector_le_of_chanKumchev
    (2 * (harmonic (2 * K) : ℝ) ^ 3) a ε K T Q U
    (chanKumchevInitialSecondMomentEstimate_divisorSquare K T)
    ha hε haε hK hQ hQU hUT

/-- The elementary argument gives an absolute constant on every fixed
multiple of the square-root range. -/
theorem chanKumchevInitialLongRangeEstimate_of_terminal_sq_le
    (C : ℝ) (K T : ℕ) (hC : 0 ≤ C) (hK : 0 < K)
    (hTK : T ≤ K) (hTsq : (T : ℝ) ^ 2 ≤ C * (K : ℝ)) :
    ChanKumchevInitialLongRangeEstimate (4 + 2 * C) K T := by
  refine ⟨by positivity, ?_⟩
  intro X hX _hLong
  have hXT : X ≤ T := (Finset.mem_Icc.mp hX).2
  have hXK : X ≤ K := hXT.trans hTK
  have hXsq : (X : ℝ) ^ 2 ≤ C * (K : ℝ) := by
    calc
      (X : ℝ) ^ 2 ≤ (T : ℝ) ^ 2 := by
        gcongr
      _ ≤ C * (K : ℝ) := hTsq
  have hscale : 0 ≤ (X : ℝ) ^ 2 := sq_nonneg _
  calc
    ‖initialRamanujanPrefixVector K X‖ ^ 2 ≤
        4 * (K : ℝ) * (X : ℝ) ^ 2 + 2 * (X : ℝ) ^ 4 :=
      norm_sq_initialRamanujanPrefixVector_le_elementary_error K X hK hXK
    _ ≤ 4 * (K : ℝ) * (X : ℝ) ^ 2 +
          2 * (C * (K : ℝ)) * (X : ℝ) ^ 2 := by
      apply add_le_add_right
      calc
        2 * (X : ℝ) ^ 4 =
            2 * ((X : ℝ) ^ 2) * ((X : ℝ) ^ 2) := by ring
        _ ≤ 2 * (C * (K : ℝ)) * ((X : ℝ) ^ 2) := by gcongr
    _ = (4 + 2 * C) * (K : ℝ) * (X : ℝ) ^ 2 := by ring

/-- For arbitrary `T ≤ K`, the exact constant delivered by elementary
incomplete orthogonality is `4 + 2 T²/K`.  Its dependence on `T²/K` records
why this argument does not prove the source-faithful Chan--Kumchev bound in
the genuinely long range. -/
theorem chanKumchevInitialLongRangeEstimate_elementaryExplicit
    (K T : ℕ) (hK : 0 < K) (hTK : T ≤ K) :
    ChanKumchevInitialLongRangeEstimate
      (4 + 2 * (T : ℝ) ^ 2 / (K : ℝ)) K T := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hTsq : (T : ℝ) ^ 2 ≤
      ((T : ℝ) ^ 2 / (K : ℝ)) * (K : ℝ) := by
    field_simp
    exact le_rfl
  have h := chanKumchevInitialLongRangeEstimate_of_terminal_sq_le
    ((T : ℝ) ^ 2 / (K : ℝ)) K T (by positivity) hK hTK hTsq
  convert! h using 1
  ring

end

end Erdos1002
