import ErdosProblems.Erdos1002.NearResonantVectorAbel
import ErdosProblems.Erdos1002.NaturalDenominatorCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary dyadic bounds for reciprocal-square Ramanujan vectors

This file discharges the arithmetic hypothesis of
`NearResonantVectorAbel` first on one complete denominator shell
`Q < p ≤ 2Q`, uniformly for every truncated subset, and then on every
finite tail `Q < p ≤ R` with `R² ≤ K` by a lossless dyadic recursion.  No
external mean-square theorem is assumed.

The argument separates the exact finite square expansion into two pieces.
On the diagonal, complete-period orthogonality gives the correct average
size over the frequency block `K < n ≤ 2K`.  Off the diagonal, uniform
incomplete orthogonality and the elementary dyadic bound
`∑ sigma₁(p)/p² ≤ 4` give an absolute constant.  Consequently, when
`Q² ≤ K`, every truncated vector in the shell has squared `ℓ²` norm at
most `42 K/Q²`.  Summing the geometrically decreasing shell norms gives a
finite-tail bound `2 sqrt(42) sqrt(K)/Q` throughout the low range.

This is exactly the strongest range furnished by the elementary finite
orthogonality modules without a long-range cancellation theorem.  It does
not claim the Chan--Kumchev estimate across many denominator shells.  The
remaining external analytic statement, if the manuscript continues to use
it, is the mean-square bound for `C_x(n) = ∑_{q≤x} c_q(n)` in the range
`sqrt(2K) < x ≤ K/(log K)^B`; nothing from that statement is introduced
here as an axiom or hypothesis.
-/

open Finset
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-! ## Complete-period diagonal control -/

/-- The real norm-square of one Ramanujan sum. -/
def ramanujanNormSq (p n : ℕ) : ℝ :=
  Complex.normSq (ramanujanSum p (n : ℤ))

/-- Exact norm-square sum over an integral number of periods. -/
theorem sum_ramanujanNormSq_range_mul
    (p j : ℕ) (hp : p ≠ 0) :
    (∑ n ∈ Finset.range (j * p), ramanujanNormSq p n) =
      (j : ℝ) * (p * Nat.totient p : ℕ) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hperiod := sum_normSq_ramanujan_shifted_period p j hp
      change
        (j : ℝ) * (p * Nat.totient p : ℕ) +
            ∑ x ∈ Finset.range p,
              ramanujanNormSq p (j * p + x) =
          (j + 1 : ℕ) * (p * Nat.totient p : ℕ)
      rw [show (∑ x ∈ Finset.range p,
          ramanujanNormSq p (j * p + x)) =
          (p * Nat.totient p : ℕ) by
        simpa only [ramanujanNormSq] using! hperiod]
      push_cast
      ring

/-- An arbitrary initial interval is bounded by one more complete period. -/
theorem sum_ramanujanNormSq_range_le
    (p X : ℕ) (hp : p ≠ 0) :
    (∑ n ∈ Finset.range X, ramanujanNormSq p n) ≤
      ((X / p + 1 : ℕ) : ℝ) * (p * Nat.totient p : ℕ) := by
  have hpPos : 0 < p := Nat.pos_of_ne_zero hp
  have hX : X ≤ (X / p + 1) * p := by
    have hlt := Nat.lt_mul_div_succ X hpPos
    simpa only [mul_comm] using! hlt.le
  calc
    (∑ n ∈ Finset.range X, ramanujanNormSq p n) ≤
        ∑ n ∈ Finset.range ((X / p + 1) * p), ramanujanNormSq p n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hX)
      intro n _hn _hnot
      exact Complex.normSq_nonneg _
    _ = ((X / p + 1 : ℕ) : ℝ) * (p * Nat.totient p : ℕ) :=
      sum_ramanujanNormSq_range_mul p (X / p + 1) hp

/-! ## Exact finite square expansion -/

/-- The real coefficient `c_p(n)/p²`. -/
def reciprocalRamanujanCoefficientTerm (n p : ℕ) : ℝ :=
  (ramanujanSum p (n : ℤ)).re / (p : ℝ) ^ 2

/-- Sum of reciprocal-square Ramanujan coefficients over a finite set. -/
def reciprocalRamanujanBlockCoefficient (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, reciprocalRamanujanCoefficientTerm n p

/-- Pair correlation on the manuscript frequency shell `K < n ≤ 2K`. -/
def reciprocalRamanujanPairCorrelation (K p p' : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc K (2 * K),
    ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)

/-- Product identity separating denominator powers from the correlation. -/
theorem reciprocalRamanujanCoefficientTerm_mul
    (n p p' : ℕ) :
    reciprocalRamanujanCoefficientTerm n p *
        reciprocalRamanujanCoefficientTerm n p' =
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
        (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)).re := by
  simp only [reciprocalRamanujanCoefficientTerm, Complex.mul_re,
    ramanujanSum_im, mul_zero, sub_zero]
  ring

/-- Exact pointwise square expansion. -/
theorem reciprocalRamanujanBlockCoefficient_sq
    (S : Finset ℕ) (n : ℕ) :
    reciprocalRamanujanBlockCoefficient S n ^ 2 =
      ∑ p ∈ S, ∑ p' ∈ S,
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)).re := by
  rw [reciprocalRamanujanBlockCoefficient, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p' _hp'
  exact reciprocalRamanujanCoefficientTerm_mul n p p'

/-- Exact frequency-summed square expansion with all finite sums exchanged. -/
theorem sum_reciprocalRamanujanBlockCoefficient_sq
    (S : Finset ℕ) (K : ℕ) :
    (∑ n ∈ Finset.Ioc K (2 * K),
      reciprocalRamanujanBlockCoefficient S n ^ 2) =
      ∑ p ∈ S, ∑ p' ∈ S,
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (reciprocalRamanujanPairCorrelation K p p').re := by
  calc
    (∑ n ∈ Finset.Ioc K (2 * K),
        reciprocalRamanujanBlockCoefficient S n ^ 2) =
        ∑ n ∈ Finset.Ioc K (2 * K),
          ∑ p ∈ S, ∑ p' ∈ S,
            (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
              (ramanujanSum p (n : ℤ) *
                ramanujanSum p' (n : ℤ)).re := by
      apply Finset.sum_congr rfl
      intro n _hn
      exact reciprocalRamanujanBlockCoefficient_sq S n
    _ = ∑ p ∈ S, ∑ p' ∈ S,
          ∑ n ∈ Finset.Ioc K (2 * K),
            (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
              (ramanujanSum p (n : ℤ) *
                ramanujanSum p' (n : ℤ)).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ S, ∑ p' ∈ S,
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (reciprocalRamanujanPairCorrelation K p p').re := by
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro p' _hp'
      rw [← Finset.mul_sum]
      simp only [reciprocalRamanujanPairCorrelation, Complex.re_sum]

/-- The Euclidean vector definition agrees coordinatewise with the real
coefficient block. -/
theorem sum_nearRamanujanVectorTerm_eq_realBlock
    (S : Finset ℕ) (K : ℕ) (n : nearDyadicIndex K) :
    (∑ p ∈ S, nearRamanujanVectorTerm K p) n =
      (reciprocalRamanujanBlockCoefficient S (n : ℕ) : ℂ) := by
  simp only [WithLp.ofLp_sum, Finset.sum_apply, nearRamanujanVectorTerm_apply,
    reciprocalRamanujanBlockCoefficient, reciprocalRamanujanCoefficientTerm]
  push_cast
  apply Finset.sum_congr rfl
  intro p _hp
  rw [ramanujanSum_even]
  rw [← ofReal_re_ramanujanSum p ((n : ℕ) : ℤ)]
  rfl

/-- Identification of the Euclidean norm square with the frequency sum. -/
theorem norm_sq_sum_nearRamanujanVectorTerm
    (S : Finset ℕ) (K : ℕ) :
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ^ 2 =
      ∑ n ∈ Finset.Ioc K (2 * K),
        reciprocalRamanujanBlockCoefficient S n ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_coe_sort (Finset.Ioc K (2 * K))]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [sum_nearRamanujanVectorTerm_eq_realBlock]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## Diagonal and off-diagonal estimates -/

/-- Uniform off-diagonal incomplete-orthogonality estimate. -/
theorem norm_reciprocalRamanujanPairCorrelation_le
    (K : ℕ) {p p' : ℕ}
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖reciprocalRamanujanPairCorrelation K p p'‖ ≤
      2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) := by
  have hset : Finset.Ioc K (2 * K) = Finset.Icc (K + 1) (2 * K) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [reciprocalRamanujanPairCorrelation, hset]
  exact ramanujan_incomplete_orthogonality_nat_Icc
    (K + 1) (2 * K) hp hp' hpp'

/-- A diagonal frequency interval is bounded by one extra complete period. -/
theorem reciprocalRamanujanPairCorrelation_self_re_le
    (K p : ℕ) (hp : p ≠ 0) :
    (reciprocalRamanujanPairCorrelation K p p).re ≤
      (((2 * K + 1) / p + 1 : ℕ) : ℝ) *
        (p * Nat.totient p : ℕ) := by
  have hsubset : Finset.Ioc K (2 * K) ⊆ Finset.range (2 * K + 1) := by
    intro n hn
    rw [Finset.mem_range]
    exact Nat.lt_add_one_iff.mpr (Finset.mem_Ioc.mp hn).2
  calc
    (reciprocalRamanujanPairCorrelation K p p).re =
        ∑ n ∈ Finset.Ioc K (2 * K), ramanujanNormSq p n := by
      simp only [reciprocalRamanujanPairCorrelation, Complex.re_sum,
        Complex.mul_re, ramanujanSum_im, mul_zero, sub_zero,
        ramanujanNormSq, Complex.normSq_apply, add_zero]
    _ ≤ ∑ n ∈ Finset.range (2 * K + 1), ramanujanNormSq p n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n _hn _hnot
      exact Complex.normSq_nonneg _
    _ ≤ (((2 * K + 1) / p + 1 : ℕ) : ℝ) *
          (p * Nat.totient p : ℕ) :=
      sum_ramanujanNormSq_range_le p (2 * K + 1) hp

/-- Division-free linear form of the preceding diagonal estimate. -/
theorem reciprocalRamanujanPairCorrelation_self_re_le_linear
    (K p : ℕ) (hp : p ≠ 0) :
    (reciprocalRamanujanPairCorrelation K p p).re ≤
      (((2 * K + 1 + p) * Nat.totient p : ℕ) : ℝ) := by
  have hperiodCount : ((2 * K + 1) / p + 1) * p ≤ 2 * K + 1 + p := by
    rw [add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self (2 * K + 1) p) p
  calc
    (reciprocalRamanujanPairCorrelation K p p).re ≤
        (((2 * K + 1) / p + 1 : ℕ) : ℝ) *
          (p * Nat.totient p : ℕ) :=
      reciprocalRamanujanPairCorrelation_self_re_le K p hp
    _ = ((((2 * K + 1) / p + 1) * p * Nat.totient p : ℕ) : ℝ) := by
      push_cast
      ring
    _ ≤ (((2 * K + 1 + p) * Nat.totient p : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right (Nat.totient p) hperiodCount

/-- Summed diagonal contribution for an arbitrary subset of one denominator
shell. -/
theorem sum_reciprocalRamanujan_diagonal_le
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    (∑ p ∈ S,
      (1 / (p : ℝ) ^ 4) *
        (reciprocalRamanujanPairCorrelation K p p).re) ≤
      2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 := by
  have hQReal : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hcard : S.card ≤ Q := by
    calc
      S.card ≤ (Finset.Ioc Q (2 * Q)).card := Finset.card_le_card hS
      _ = Q := by rw [Nat.card_Ioc]; omega
  have hpoint (p : ℕ) (hp : p ∈ S) :
      (1 / (p : ℝ) ^ 4) *
          (reciprocalRamanujanPairCorrelation K p p).re ≤
        (1 / (Q : ℝ) ^ 4) *
          (((2 * K + 1 + 2 * Q) * (2 * Q) : ℕ) : ℝ) := by
    have hpBlock := hS hp
    have hpBounds := Finset.mem_Ioc.mp hpBlock
    have hpPos : 0 < p := hQ.trans hpBounds.1
    have hcorr := reciprocalRamanujanPairCorrelation_self_re_le_linear
      K p hpPos.ne'
    have hnumNat :
        (2 * K + 1 + p) * Nat.totient p ≤
          (2 * K + 1 + 2 * Q) * (2 * Q) := by
      apply Nat.mul_le_mul
      · exact Nat.add_le_add_left hpBounds.2 (2 * K + 1)
      · exact (Nat.totient_le p).trans hpBounds.2
    have hnumReal :
        ((((2 * K + 1 + p) * Nat.totient p : ℕ) : ℝ)) ≤
          (((2 * K + 1 + 2 * Q) * (2 * Q) : ℕ) : ℝ) := by
      exact_mod_cast hnumNat
    have hQpReal : (Q : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hpBounds.1.le
    have hpow : (Q : ℝ) ^ 4 ≤ (p : ℝ) ^ 4 := by
      exact pow_le_pow_left₀ (by positivity) hQpReal 4
    have hinv : 1 / (p : ℝ) ^ 4 ≤ 1 / (Q : ℝ) ^ 4 := by
      exact one_div_le_one_div_of_le (by positivity) hpow
    calc
      (1 / (p : ℝ) ^ 4) *
          (reciprocalRamanujanPairCorrelation K p p).re ≤
          (1 / (p : ℝ) ^ 4) *
            (((2 * K + 1 + p) * Nat.totient p : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcorr (by positivity)
      _ ≤ (1 / (Q : ℝ) ^ 4) *
          (((2 * K + 1 + 2 * Q) * (2 * Q) : ℕ) : ℝ) := by
        exact mul_le_mul hinv hnumReal (by positivity) (by positivity)
  calc
    (∑ p ∈ S,
        (1 / (p : ℝ) ^ 4) *
          (reciprocalRamanujanPairCorrelation K p p).re) ≤
        ∑ _p ∈ S, (1 / (Q : ℝ) ^ 4) *
          (((2 * K + 1 + 2 * Q) * (2 * Q) : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = (S.card : ℝ) * ((1 / (Q : ℝ) ^ 4) *
          (((2 * K + 1 + 2 * Q) * (2 * Q) : ℕ) : ℝ)) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ) * ((1 / (Q : ℝ) ^ 4) *
          (((2 * K + 1 + 2 * Q) * (2 * Q) : ℕ) : ℝ)) := by
      gcongr
    _ = 2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 := by
      push_cast
      field_simp

/-- The whole off-diagonal contribution of a denominator shell is at most
the absolute constant `32`. -/
theorem sum_abs_reciprocalRamanujan_offDiagonal_le
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    (∑ p ∈ S, ∑ p' ∈ S,
      if p ≠ p' then
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          |(reciprocalRamanujanPairCorrelation K p p').re|
      else 0) ≤ 32 := by
  let mass : ℕ → ℝ := fun p ↦
    (ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2
  have hmass (p : ℕ) : 0 ≤ mass p := by dsimp [mass]; positivity
  have hpoint {p p' : ℕ} (hp : p ∈ S) (hp' : p' ∈ S)
      (hne : p ≠ p') :
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          |(reciprocalRamanujanPairCorrelation K p p').re| ≤
        2 * mass p * mass p' := by
    have hpBounds := Finset.mem_Ioc.mp (hS hp)
    have hp'Bounds := Finset.mem_Ioc.mp (hS hp')
    have hpPos : 0 < p := hQ.trans hpBounds.1
    have hp'Pos : 0 < p' := hQ.trans hp'Bounds.1
    have hcorr := norm_reciprocalRamanujanPairCorrelation_le
      K hpPos.ne' hp'Pos.ne' hne
    have hre : |(reciprocalRamanujanPairCorrelation K p p').re| ≤
        ‖reciprocalRamanujanPairCorrelation K p p'‖ :=
      Complex.abs_re_le_norm _
    have hscalar : 0 ≤ 1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) := by positivity
    calc
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          |(reciprocalRamanujanPairCorrelation K p p').re| ≤
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            ‖reciprocalRamanujanPairCorrelation K p p'‖ :=
        mul_le_mul_of_nonneg_left hre hscalar
      _ ≤ (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
            (ArithmeticFunction.sigma 1 p' : ℝ))) :=
        mul_le_mul_of_nonneg_left hcorr hscalar
      _ = 2 * mass p * mass p' := by
        dsimp [mass]
        ring
  have hmassSum : (∑ p ∈ S, mass p) ≤ 4 := by
    calc
      (∑ p ∈ S, mass p) ≤
          ∑ p ∈ Finset.Ioc Q (2 * Q), mass p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hS
        intro p _hp _hnot
        exact hmass p
      _ ≤ 4 := by
        simpa only [mass] using! sum_sigma_one_div_sq_Ioc_le_four Q hQ
  have hmassSumNonneg : 0 ≤ ∑ p ∈ S, mass p :=
    Finset.sum_nonneg fun p _hp ↦ hmass p
  calc
    (∑ p ∈ S, ∑ p' ∈ S,
        if p ≠ p' then
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            |(reciprocalRamanujanPairCorrelation K p p').re|
        else 0) ≤
        ∑ p ∈ S, ∑ p' ∈ S, 2 * mass p * mass p' := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro p' hp'
      by_cases hne : p ≠ p'
      · rw [if_pos hne]
        exact hpoint hp hp' hne
      · rw [if_neg hne]
        positivity
    _ = 2 * (∑ p ∈ S, mass p) ^ 2 := by
      calc
        (∑ p ∈ S, ∑ p' ∈ S, 2 * mass p * mass p') =
            ∑ p ∈ S, (2 * mass p) * (∑ p' ∈ S, mass p') := by
          apply Finset.sum_congr rfl
          intro p _hp
          rw [Finset.mul_sum]
        _ = (∑ p ∈ S, 2 * mass p) * (∑ p' ∈ S, mass p') := by
          rw [Finset.sum_mul]
        _ = (2 * (∑ p ∈ S, mass p)) * (∑ p' ∈ S, mass p') := by
          have hf : (∑ p ∈ S, 2 * mass p) =
              2 * (∑ p ∈ S, mass p) :=
            (Finset.mul_sum S mass 2).symm
          rw [hf]
        _ = 2 * (∑ p ∈ S, mass p) ^ 2 := by ring
    _ ≤ 2 * 4 ^ 2 := by gcongr
    _ = 32 := by norm_num

/-! ## Closed dyadic vector estimates -/

/-- Unconditional squared `ℓ²` estimate for every subset of one shell. -/
theorem norm_sq_sum_nearRamanujanVectorTerm_dyadic_le
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ^ 2 ≤
      2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 + 32 := by
  let D : ℕ → ℝ := fun p ↦
    (1 / (p : ℝ) ^ 4) *
      (reciprocalRamanujanPairCorrelation K p p).re
  let O : ℕ → ℕ → ℝ := fun p p' ↦
    (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
      |(reciprocalRamanujanPairCorrelation K p p').re|
  have hpair {p p' : ℕ} (hp : p ∈ S) (hp' : p' ∈ S) :
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (reciprocalRamanujanPairCorrelation K p p').re ≤
        (if p = p' then D p else 0) +
          (if p ≠ p' then O p p' else 0) := by
    by_cases hpp' : p = p'
    · subst p'
      calc
        (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
            (reciprocalRamanujanPairCorrelation K p p).re = D p := by
          dsimp [D]
          ring
        _ = (if p = p then D p else 0) +
            (if p ≠ p then O p p else 0) := by simp
        _ ≤ (if p = p then D p else 0) +
            (if p ≠ p then O p p else 0) := le_rfl
    · have hre : (reciprocalRamanujanPairCorrelation K p p').re ≤
          |(reciprocalRamanujanPairCorrelation K p p').re| := le_abs_self _
      have hscalar : 0 ≤ 1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) := by positivity
      calc
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            (reciprocalRamanujanPairCorrelation K p p').re ≤
            (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
              |(reciprocalRamanujanPairCorrelation K p p').re| :=
          mul_le_mul_of_nonneg_left hre hscalar
        _ = (if p = p' then D p else 0) +
            (if p ≠ p' then O p p' else 0) := by simp [hpp', O]
  have hdiagEq :
      (∑ p ∈ S, ∑ p' ∈ S, if p = p' then D p else 0) =
        ∑ p ∈ S, D p := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
  calc
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ^ 2 =
        ∑ p ∈ S, ∑ p' ∈ S,
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            (reciprocalRamanujanPairCorrelation K p p').re := by
      rw [norm_sq_sum_nearRamanujanVectorTerm,
        sum_reciprocalRamanujanBlockCoefficient_sq]
    _ ≤ ∑ p ∈ S, ∑ p' ∈ S,
        ((if p = p' then D p else 0) +
          (if p ≠ p' then O p p' else 0)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro p' hp'
      exact hpair hp hp'
    _ = (∑ p ∈ S, ∑ p' ∈ S, if p = p' then D p else 0) +
          ∑ p ∈ S, ∑ p' ∈ S, if p ≠ p' then O p p' else 0 := by
      simp_rw [Finset.sum_add_distrib]
    _ = (∑ p ∈ S, D p) +
          ∑ p ∈ S, ∑ p' ∈ S, if p ≠ p' then O p p' else 0 := by
      rw [hdiagEq]
    _ ≤ 2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 + 32 := by
      gcongr
      · simpa only [D] using! sum_reciprocalRamanujan_diagonal_le S K Q hQ hS
      · simpa only [O] using!
          sum_abs_reciprocalRamanujan_offDiagonal_le S K Q hQ hS

/-- Norm form of the unconditional shell estimate. -/
theorem norm_sum_nearRamanujanVectorTerm_dyadic_le
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ≤
      Real.sqrt
        (2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 + 32) := by
  have hnonneg :
      0 ≤ 2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 + 32 := by
    positivity
  exact (Real.le_sqrt (norm_nonneg _) hnonneg).2
    (norm_sq_sum_nearRamanujanVectorTerm_dyadic_le S K Q hQ hS)

/-- In the elementary range `Q² ≤ K`, the shell has the expected
`O(K/Q²)` squared norm with an explicit constant. -/
theorem norm_sq_sum_nearRamanujanVectorTerm_dyadic_le_lowRange
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ^ 2 ≤
      42 * (K : ℝ) / (Q : ℝ) ^ 2 := by
  have hOneQ : 1 ≤ Q := hQ
  have hQleQsq : Q ≤ Q ^ 2 := by
    nlinarith
  have hQleK : Q ≤ K := hQleQsq.trans hQK
  have hOneK : 1 ≤ K := hOneQ.trans hQleK
  have hnumNat : 2 * K + 1 + 2 * Q ≤ 5 * K := by omega
  have hnumReal :
      (2 * K + 1 + 2 * Q : ℕ) ≤ (5 * K : ℕ) := hnumNat
  have hQKReal : ((Q : ℝ) ^ 2) ≤ (K : ℝ) := by exact_mod_cast hQK
  have hdenom : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
  calc
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ^ 2 ≤
        2 * (2 * K + 1 + 2 * Q : ℕ) / (Q : ℝ) ^ 2 + 32 :=
      norm_sq_sum_nearRamanujanVectorTerm_dyadic_le S K Q hQ hS
    _ ≤ 2 * (5 * K : ℕ) / (Q : ℝ) ^ 2 + 32 := by
      gcongr
    _ ≤ 42 * (K : ℝ) / (Q : ℝ) ^ 2 := by
      apply (le_div_iff₀ hdenom).2
      field_simp
      push_cast
      nlinarith

/-- Square-root form of the low-range estimate. -/
theorem norm_sum_nearRamanujanVectorTerm_dyadic_le_lowRange
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ≤
      Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) := by
  have hnonneg : 0 ≤ 42 * (K : ℝ) / (Q : ℝ) ^ 2 := by positivity
  exact (Real.le_sqrt (norm_nonneg _) hnonneg).2
    (norm_sq_sum_nearRamanujanVectorTerm_dyadic_le_lowRange
      S K Q hQ hQK hS)

/-- The same shell estimate in the scale-transparent form
`sqrt(42) * sqrt(K) / Q`. -/
theorem norm_sum_nearRamanujanVectorTerm_dyadic_le_lowRange_normalized
    (S : Finset ℕ) (K Q : ℕ) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K)
    (hS : S ⊆ Finset.Ioc Q (2 * Q)) :
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ≤
      Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by
  calc
    ‖∑ p ∈ S, nearRamanujanVectorTerm K p‖ ≤
        Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) :=
      norm_sum_nearRamanujanVectorTerm_dyadic_le_lowRange
        S K Q hQ hQK hS
    _ = Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by positivity)]

/-- Elementary finite-tail estimate throughout the full low range
`Q < p ≤ R ≤ sqrt K`.  The proof recursively splits into dyadic shells;
the geometric decay is retained exactly, so no logarithmic loss occurs. -/
theorem norm_sum_nearRamanujanVectorTerm_tail_le_lowRange
    (K Q R : ℕ) (hQ : 0 < Q) (hQR : Q < R) (hRK : R ^ 2 ≤ K) :
    ‖∑ p ∈ Finset.Ioc Q R, nearRamanujanVectorTerm K p‖ ≤
      2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by
  by_cases hRle : R ≤ 2 * Q
  · have hQK : Q ^ 2 ≤ K := by
      have hQRsq : Q ^ 2 ≤ R ^ 2 := by nlinarith
      exact hQRsq.trans hRK
    have hsubset : Finset.Ioc Q R ⊆ Finset.Ioc Q (2 * Q) := by
      intro p hp
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hp).1,
        (Finset.mem_Ioc.mp hp).2.trans hRle⟩
    have hshell :=
      norm_sum_nearRamanujanVectorTerm_dyadic_le_lowRange_normalized
        (Finset.Ioc Q R) K Q hQ hQK hsubset
    have hnonneg :
        0 ≤ Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by positivity
    calc
      ‖∑ p ∈ Finset.Ioc Q R, nearRamanujanVectorTerm K p‖ ≤
          Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := hshell
      _ ≤ 2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by
        have hdouble :
            Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) ≤
              2 * (Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) := by
          nlinarith
        calc
          Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) ≤
              2 * (Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) := hdouble
          _ = 2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by ring
  · have h2QR : 2 * Q < R := lt_of_not_ge hRle
    have h2Qpos : 0 < 2 * Q := by positivity
    have h2QK : (2 * Q) ^ 2 ≤ K := by
      have hsq : (2 * Q) ^ 2 ≤ R ^ 2 := by nlinarith
      exact hsq.trans hRK
    have hleftSubset : Finset.Ioc Q (2 * Q) ⊆ Finset.Ioc Q (2 * Q) :=
      fun _ hp ↦ hp
    have hleft :=
      norm_sum_nearRamanujanVectorTerm_dyadic_le_lowRange_normalized
        (Finset.Ioc Q (2 * Q)) K Q hQ
        (by
          have hsq : Q ^ 2 ≤ (2 * Q) ^ 2 := by nlinarith
          exact hsq.trans h2QK)
        hleftSubset
    have hright := norm_sum_nearRamanujanVectorTerm_tail_le_lowRange
      K (2 * Q) R h2Qpos h2QR hRK
    have hdisjoint : Disjoint (Finset.Ioc Q (2 * Q)) (Finset.Ioc (2 * Q) R) := by
      rw [Finset.disjoint_left]
      intro p hpLeft hpRight
      have hl := Finset.mem_Ioc.mp hpLeft
      have hr := Finset.mem_Ioc.mp hpRight
      omega
    have hsplit :
        (∑ p ∈ Finset.Ioc Q R, nearRamanujanVectorTerm K p) =
          (∑ p ∈ Finset.Ioc Q (2 * Q), nearRamanujanVectorTerm K p) +
            ∑ p ∈ Finset.Ioc (2 * Q) R,
              nearRamanujanVectorTerm K p := by
      rw [← Finset.sum_union hdisjoint]
      rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) h2QR.le]
    rw [hsplit]
    calc
      ‖(∑ p ∈ Finset.Ioc Q (2 * Q), nearRamanujanVectorTerm K p) +
          ∑ p ∈ Finset.Ioc (2 * Q) R,
            nearRamanujanVectorTerm K p‖ ≤
          ‖∑ p ∈ Finset.Ioc Q (2 * Q), nearRamanujanVectorTerm K p‖ +
            ‖∑ p ∈ Finset.Ioc (2 * Q) R,
              nearRamanujanVectorTerm K p‖ := norm_add_le _ _
      _ ≤ Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) +
          2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (2 * Q : ℕ) := by
        exact add_le_add hleft hright
      _ = 2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by
        push_cast
        field_simp
        ring
termination_by R - Q
decreasing_by omega

/-- Uniform bound for every truncated prefix of the denominator shell; this
is the exact arithmetic input expected by finite vector Abel summation. -/
theorem norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_lowRange
    (K Q R : ℕ) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K)
    (hR : R ∈ Finset.Icc (Q + 1) (2 * Q)) :
    ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤
      Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) := by
  have hsubset : Finset.Icc (Q + 1) R ⊆ Finset.Ioc Q (2 * Q) := by
    intro p hp
    have hpBounds := Finset.mem_Icc.mp hp
    have hRBounds := Finset.mem_Icc.mp hR
    exact Finset.mem_Ioc.mpr ⟨by omega, hpBounds.2.trans hRBounds.2⟩
  simpa only [euclideanIntervalPartialSum] using!
    norm_sum_nearRamanujanVectorTerm_dyadic_le_lowRange
      (Finset.Icc (Q + 1) R) K Q hQ hQK hsubset

/-- Uniform prefix estimate for any upper endpoint still below `sqrt K`.
This is the full elementary part of the finite-tail estimate, not merely a
single denominator shell. -/
theorem norm_euclideanIntervalPartialSum_nearRamanujan_tail_le_lowRange
    (K Q U R : ℕ) (hQ : 0 < Q) (hUK : U ^ 2 ≤ K)
    (hR : R ∈ Finset.Icc (Q + 1) U) :
    ‖euclideanIntervalPartialSum (nearRamanujanVectorTerm K) (Q + 1) R‖ ≤
      2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ) := by
  have hRBounds := Finset.mem_Icc.mp hR
  have hQR : Q < R := by omega
  have hRK : R ^ 2 ≤ K := by
    have hRU : R ≤ U := hRBounds.2
    have hsq : R ^ 2 ≤ U ^ 2 := by nlinarith
    exact hsq.trans hUK
  have hset : Finset.Icc (Q + 1) R = Finset.Ioc Q R := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [euclideanIntervalPartialSum, hset]
  exact norm_sum_nearRamanujanVectorTerm_tail_le_lowRange
    K Q R hQ hQR hRK

/-- Fully unconditional application of the near-resonant vector Abel bridge
on one low-range denominator shell. -/
theorem norm_finiteNearRamanujanMultiplierVector_dyadic_le_lowRange
    (a ε : ℝ) (K Q : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQK : Q ^ 2 ≤ K) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) (2 * Q)‖ ≤
      Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2) *
        (64 * Real.pi * nearProfileDecayConstant) := by
  have hQU : Q + 1 ≤ 2 * Q := by omega
  apply norm_finiteNearRamanujanMultiplierVector_le_of_partialSum
    a ε K (Q + 1) (2 * Q)
      (Real.sqrt (42 * (K : ℝ) / (Q : ℝ) ^ 2))
      ha hε haε hK (by omega) hQU
  intro R hR
  exact norm_euclideanIntervalPartialSum_nearRamanujan_dyadic_le_lowRange
    K Q R hQ hQK hR

/-- Fully unconditional vector-Abel estimate for every finite denominator
tail ending below `sqrt K`. -/
theorem norm_finiteNearRamanujanMultiplierVector_tail_le_lowRange
    (a ε : ℝ) (K Q U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hK : 0 < K) (hQ : 0 < Q) (hQU : Q < U) (hUK : U ^ 2 ≤ K) :
    ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ ≤
      (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
        (64 * Real.pi * nearProfileDecayConstant) := by
  have hStartEnd : Q + 1 ≤ U := by omega
  apply norm_finiteNearRamanujanMultiplierVector_le_of_partialSum
    a ε K (Q + 1) U
      (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ))
      ha hε haε hK (by omega) hStartEnd
  intro R hR
  exact norm_euclideanIntervalPartialSum_nearRamanujan_tail_le_lowRange
    K Q U R hQ hUK hR

end

end Erdos1002
