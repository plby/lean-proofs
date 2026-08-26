import ErdosProblems.Erdos1002.ReconstructionCoefficients
import ErdosProblems.Erdos1002.RamanujanIncompleteOrthogonality
import ErdosProblems.Erdos1002.DivisorSquareAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The natural-denominator cutoff

This file formalizes the arithmetic estimates used when the all-denominator
Fourier--Ramanujan reconstruction is truncated in the *natural* denominator
variable.  In particular, it keeps the finite Abel boundary term explicit,
proves the bounded-variation estimate for the product of the two sampled
`HStar` tails, and records the complete-period diagonal identity at the
precise scale occurring in the manuscript.

No limiting convention is hidden in the definitions below: a dyadic block is
the finite set `Q < p <= 2Q`, and every frequency interval is a closed natural
interval `u <= n <= v`.
-/

open Finset
open scoped ArithmeticFunction.sigma BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-- The real summand contributed by the natural denominator `p` to a positive
Fourier coefficient, before multiplication by the universal constant
`-i/(2*pi)`.  It is totalized at `p = 0`, although all applications below use
positive denominators. -/
def naturalDenominatorCoefficientTerm (N n p : ℕ) : ℝ :=
  (ramanujanSum p (n : ℤ)).re / (p : ℝ) ^ 2 * hStarRatio n (p * N)

/-- The manuscript's dyadic natural-denominator block `Q < p <= 2Q`. -/
def naturalDenominatorBlockCoefficient (N Q n : ℕ) : ℝ :=
  ∑ p ∈ Ioc Q (2 * Q), naturalDenominatorCoefficientTerm N n p

/-- The same block with the universal complex Fourier normalization restored. -/
def normalizedNaturalDenominatorBlockCoefficient (N Q n : ℕ) : ℂ :=
  (-Complex.I / (2 * (Real.pi : ℂ))) *
    (naturalDenominatorBlockCoefficient N Q n : ℂ)

theorem naturalDenominatorBlock_mem_pos {Q p : ℕ}
    (hQ : 0 < Q) (hp : p ∈ Ioc Q (2 * Q)) : 0 < p := by
  exact hQ.trans (mem_Ioc.mp hp).1

/-- Multiplying both the sampled argument and scale by the same positive
integer does not change one `HStar` summand.  The strict and equality cases
are both cancelled explicitly by arithmetic, so the midpoint convention is
preserved. -/
theorem hStarRatioWeight_mul_scale_cancel (n s k p : ℕ) (hp : 0 < p) :
    hStarRatioWeight (n * p) (s * p) k = hStarRatioWeight n s k := by
  unfold hStarRatioWeight
  have hlt : n * p < k * (s * p) ↔ n < k * s := by
    rw [← Nat.mul_assoc, Nat.mul_lt_mul_right hp]
  have heq : n * p = k * (s * p) ↔ n = k * s := by
    rw [← Nat.mul_assoc, mul_right_cancel_iff_of_pos hp]
  simp only [hlt, heq]

/-- Exact cancellation of a common positive integral scale in the sampled
half-weighted tail. -/
theorem hStarRatio_mul_scale_cancel (n s p : ℕ) (hp : 0 < p) :
    hStarRatio (n * p) (s * p) = hStarRatio n s := by
  unfold hStarRatio
  apply tsum_congr
  intro k
  exact hStarRatioWeight_mul_scale_cancel n s k p hp

/-- The real product weight used in every off-diagonal term. -/
def naturalCutoffPairWeight (N p p' n : ℕ) : ℝ :=
  hStarRatio n (p * N) * hStarRatio n (p' * N)

theorem naturalCutoffPairWeight_nonneg (N p p' n : ℕ) :
    0 ≤ naturalCutoffPairWeight N p p' n := by
  exact mul_nonneg (hStarRatio_nonneg _ _) (hStarRatio_nonneg _ _)

theorem naturalCutoffPairWeight_antitone (N p p' : ℕ) :
    Antitone (naturalCutoffPairWeight N p p') := by
  exact hStarRatio_mul_antitone (p * N) (p' * N)

/-- Exact telescoping of the discrete total variation.  This is the envelope
that the paper's abbreviated phrase "weighted Abel summation" requires. -/
theorem naturalCutoffPairWeight_variation_eq
    (N p p' u v : ℕ) (huv : u ≤ v) :
    (∑ n ∈ Ico u v,
      |naturalCutoffPairWeight N p p' (n + 1) -
        naturalCutoffPairWeight N p p' n|) =
      naturalCutoffPairWeight N p p' u -
        naturalCutoffPairWeight N p p' v := by
  exact sum_Ico_abs_sub_antitone
    (naturalCutoffPairWeight_antitone N p p') huv

/-- Uniform total-variation envelope for the sampled product weight. -/
theorem naturalCutoffPairWeight_variation_le
    (N p p' u v : ℕ) (huv : u ≤ v) :
    (∑ n ∈ Ico u v,
      |naturalCutoffPairWeight N p p' (n + 1) -
        naturalCutoffPairWeight N p p' n|) ≤
      (Real.pi ^ 2 / 6) ^ 2 := by
  simpa only [naturalCutoffPairWeight] using!
    hStarRatio_mul_totalVariation_le (p * N) (p' * N) u v huv

/-- The right-endpoint term in finite Abel summation has the same uniform
envelope as the total variation. -/
theorem naturalCutoffPairWeight_le (N p p' n : ℕ) :
    naturalCutoffPairWeight N p p' n ≤ (Real.pi ^ 2 / 6) ^ 2 := by
  unfold naturalCutoffPairWeight
  nlinarith [hStarRatio_nonneg n (p * N),
    hStarRatio_nonneg n (p' * N),
    hStarRatio_le_zetaTwo n (p * N),
    hStarRatio_le_zetaTwo n (p' * N),
    sq_nonneg (hStarRatio n (p * N) - hStarRatio n (p' * N))]

/-- The finite pair correlation that appears after expanding a dyadic block
square.  Keeping it complex makes the connection to incomplete Ramanujan
orthogonality literal; the sum is real because each Ramanujan sum is real. -/
def naturalCutoffPairCorrelation
    (N p p' u v : ℕ) : ℂ :=
  ∑ n ∈ Icc u v,
    (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
      (naturalCutoffPairWeight N p p' n : ℂ)

/-- Multiplication of two individual natural-denominator coefficient terms,
with the two denominator powers separated from the pair correlation. -/
theorem naturalDenominatorCoefficientTerm_mul
    (N n p p' : ℕ) :
    naturalDenominatorCoefficientTerm N n p *
        naturalDenominatorCoefficientTerm N n p' =
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
        ((ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
          (naturalCutoffPairWeight N p p' n : ℂ)).re := by
  simp only [naturalDenominatorCoefficientTerm, naturalCutoffPairWeight,
    Complex.mul_re, ramanujanSum_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  ring

/-- Exact pointwise square expansion of the dyadic coefficient block. -/
theorem naturalDenominatorBlockCoefficient_sq
    (N Q n : ℕ) :
    naturalDenominatorBlockCoefficient N Q n ^ 2 =
      ∑ p ∈ Ioc Q (2 * Q),
        ∑ p' ∈ Ioc Q (2 * Q),
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            ((ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
              (naturalCutoffPairWeight N p p' n : ℂ)).re := by
  rw [naturalDenominatorBlockCoefficient, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p' _hp'
  exact naturalDenominatorCoefficientTerm_mul N n p p'

/-- Exact finite-frequency square expansion, including both diagonal and
off-diagonal pairs.  All three finite sums are interchanged explicitly. -/
theorem sum_naturalDenominatorBlockCoefficient_sq_Icc
    (N Q u v : ℕ) :
    (∑ n ∈ Icc u v,
      naturalDenominatorBlockCoefficient N Q n ^ 2) =
      ∑ p ∈ Ioc Q (2 * Q),
        ∑ p' ∈ Ioc Q (2 * Q),
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            (naturalCutoffPairCorrelation N p p' u v).re := by
  let P : Finset ℕ := Ioc Q (2 * Q)
  let S : Finset ℕ := Icc u v
  calc
    (∑ n ∈ Icc u v,
        naturalDenominatorBlockCoefficient N Q n ^ 2) =
        ∑ n ∈ S, ∑ p ∈ P, ∑ p' ∈ P,
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            ((ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
              (naturalCutoffPairWeight N p p' n : ℂ)).re := by
      apply Finset.sum_congr rfl
      intro n _hn
      simpa only [P, S] using! naturalDenominatorBlockCoefficient_sq N Q n
    _ = ∑ p ∈ P, ∑ p' ∈ P, ∑ n ∈ S,
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            ((ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
              (naturalCutoffPairWeight N p p' n : ℂ)).re := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ P, ∑ p' ∈ P,
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            (naturalCutoffPairCorrelation N p p' u v).re := by
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro p' _hp'
      rw [← Finset.mul_sum]
      simp only [naturalCutoffPairCorrelation, Complex.re_sum, S]
    _ = ∑ p ∈ Ioc Q (2 * Q),
          ∑ p' ∈ Ioc Q (2 * Q),
            (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
              (naturalCutoffPairCorrelation N p p' u v).re := by
      rfl

/-- Finite off-diagonal weighted Abel estimate with every boundary term
visible.  The hypothesis `p != p'` is essential: it is exactly what makes
the unweighted Ramanujan partial sums uniformly bounded. -/
theorem norm_weighted_ramanujan_hStar_product_Icc_le
    {N p p' u v : ℕ} (huv : u ≤ v)
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc u v,
      (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
        (naturalCutoffPairWeight N p p' n : ℂ)‖ ≤
      (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ))) *
        ((naturalCutoffPairWeight N p p' v) +
          ∑ n ∈ Ico u v,
            |naturalCutoffPairWeight N p p' n -
              naturalCutoffPairWeight N p p' (n + 1)|) := by
  have h := norm_weighted_ramanujan_product_le
    (fun n : ℕ ↦ (naturalCutoffPairWeight N p p' n : ℂ))
    huv hp hp' hpp'
  have hend : ‖(naturalCutoffPairWeight N p p' v : ℂ)‖ =
      naturalCutoffPairWeight N p p' v := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (naturalCutoffPairWeight_nonneg N p p' v)]
  have hvariation :
      (∑ n ∈ Ico u v,
        ‖(naturalCutoffPairWeight N p p' n : ℂ) -
          (naturalCutoffPairWeight N p p' (n + 1) : ℂ)‖) =
      ∑ n ∈ Ico u v,
        |naturalCutoffPairWeight N p p' n -
          naturalCutoffPairWeight N p p' (n + 1)| := by
    apply Finset.sum_congr rfl
    intro n _hn
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hend, hvariation] at h
  exact h

/-- Coarse uniform form of the preceding finite Abel estimate.  The factor
four consists of the incomplete-orthogonality constant two and the two
explicit BV boundary contributions. -/
theorem norm_weighted_ramanujan_hStar_product_Icc_le_uniform
    {N p p' u v : ℕ} (huv : u ≤ v)
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖∑ n ∈ Icc u v,
      (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
        (naturalCutoffPairWeight N p p' n : ℂ)‖ ≤
      4 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) *
        (Real.pi ^ 2 / 6) ^ 2 := by
  calc
    ‖∑ n ∈ Icc u v,
        (ramanujanSum p (n : ℤ) * ramanujanSum p' (n : ℤ)) *
          (naturalCutoffPairWeight N p p' n : ℂ)‖ ≤
        (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
          (ArithmeticFunction.sigma 1 p' : ℝ))) *
          ((naturalCutoffPairWeight N p p' v) +
            ∑ n ∈ Ico u v,
              |naturalCutoffPairWeight N p p' n -
                naturalCutoffPairWeight N p p' (n + 1)|) :=
      norm_weighted_ramanujan_hStar_product_Icc_le huv hp hp' hpp'
    _ ≤ (2 * ((ArithmeticFunction.sigma 1 p : ℝ) *
          (ArithmeticFunction.sigma 1 p' : ℝ))) *
          ((Real.pi ^ 2 / 6) ^ 2 + (Real.pi ^ 2 / 6) ^ 2) := by
      gcongr
      · exact naturalCutoffPairWeight_le N p p' v
      · simpa only [abs_sub_comm] using!
          naturalCutoffPairWeight_variation_le N p p' u v huv
    _ = 4 * ((ArithmeticFunction.sigma 1 p : ℝ) *
          (ArithmeticFunction.sigma 1 p' : ℝ)) *
          (Real.pi ^ 2 / 6) ^ 2 := by ring

theorem norm_naturalCutoffPairCorrelation_le_uniform
    {N p p' u v : ℕ} (huv : u ≤ v)
    (hp : p ≠ 0) (hp' : p' ≠ 0) (hpp' : p ≠ p') :
    ‖naturalCutoffPairCorrelation N p p' u v‖ ≤
      4 * ((ArithmeticFunction.sigma 1 p : ℝ) *
        (ArithmeticFunction.sigma 1 p' : ℝ)) *
        (Real.pi ^ 2 / 6) ^ 2 := by
  exact norm_weighted_ramanujan_hStar_product_Icc_le_uniform
    huv hp hp' hpp'

/-! ## Complete-period diagonal blocks -/

/-- Shifting the frequency through an integral number of complete periods
does not alter a Ramanujan sum. -/
theorem ramanujanSum_nat_period_shift (p j r : ℕ) :
    ramanujanSum p ((j * p + r : ℕ) : ℤ) =
      ramanujanSum p (r : ℤ) := by
  have h := (ramanujanSum_periodic p).nat_mul j (r : ℤ)
  norm_num [Nat.cast_add, Nat.cast_mul, add_comm] at h ⊢
  exact h

/-- Real norm-square form of the complete-period diagonal identity. -/
theorem sum_normSq_ramanujan_complete_period (p : ℕ) (hp : p ≠ 0) :
    (∑ r ∈ range p, Complex.normSq (ramanujanSum p (r : ℤ))) =
      (p * Nat.totient p : ℕ) := by
  have h := congrArg Complex.re (ramanujan_complete_period_square p hp)
  simpa only [Complex.re_sum, Complex.mul_re, pow_two,
    ramanujanSum_im, mul_zero, zero_mul, sub_zero, Complex.natCast_re,
    Complex.sq_norm, Complex.normSq_apply, add_zero] using! h

/-- The same complete-period identity after a block shift. -/
theorem sum_normSq_ramanujan_shifted_period (p j : ℕ) (hp : p ≠ 0) :
    (∑ r ∈ range p,
      Complex.normSq (ramanujanSum p ((j * p + r : ℕ) : ℤ))) =
      (p * Nat.totient p : ℕ) := by
  calc
    (∑ r ∈ range p,
        Complex.normSq (ramanujanSum p ((j * p + r : ℕ) : ℤ))) =
        ∑ r ∈ range p, Complex.normSq (ramanujanSum p (r : ℤ)) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [ramanujanSum_nat_period_shift]
    _ = (p * Nat.totient p : ℕ) :=
      sum_normSq_ramanujan_complete_period p hp

/-- A single diagonal period block at the manuscript's natural scale.

For `0 <= r < p`, monotonicity bounds the sampled tail at `j*p+r` by its
value at `j*p`; cancelling the common factor `p` then gives exactly
`HStar(j/N)`.  The complete-period Ramanujan square sum supplies the factor
`p*phi(p)`. -/
theorem diagonal_ramanujan_hStar_period_block_le
    (N p j : ℕ) (hp : 0 < p) :
    (∑ r ∈ range p,
      Complex.normSq (ramanujanSum p ((j * p + r : ℕ) : ℤ)) *
        hStarRatio (j * p + r) (p * N) ^ 2) ≤
      ((p * Nat.totient p : ℕ) : ℝ) * hStarRatio j N ^ 2 := by
  have hscale : hStarRatio (j * p) (p * N) = hStarRatio j N := by
    simpa only [mul_comm] using! hStarRatio_mul_scale_cancel j N p hp
  calc
    (∑ r ∈ range p,
        Complex.normSq (ramanujanSum p ((j * p + r : ℕ) : ℤ)) *
          hStarRatio (j * p + r) (p * N) ^ 2) ≤
        ∑ r ∈ range p,
          Complex.normSq (ramanujanSum p ((j * p + r : ℕ) : ℤ)) *
            hStarRatio (j * p) (p * N) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      have hrle : j * p ≤ j * p + r := Nat.le_add_right _ _
      have htail := hStarRatio_antitone (p * N) hrle
      gcongr
      · exact Complex.normSq_nonneg _
      · exact hStarRatio_nonneg _ _
    _ = (∑ r ∈ range p,
          Complex.normSq (ramanujanSum p ((j * p + r : ℕ) : ℤ))) *
          hStarRatio (j * p) (p * N) ^ 2 := by
      rw [Finset.sum_mul]
    _ = ((p * Nat.totient p : ℕ) : ℝ) *
          hStarRatio (j * p) (p * N) ^ 2 := by
      rw [sum_normSq_ramanujan_shifted_period p j hp.ne']
    _ = ((p * Nat.totient p : ℕ) : ℝ) * hStarRatio j N ^ 2 := by
      rw [hscale]

/-- Adding back the single zero-frequency value preserves summability of the
`HStar` square series. -/
theorem summable_hStarRatio_square (s : ℕ) (hs : 0 < s) :
    Summable (fun n : ℕ ↦ hStarRatio n s ^ 2) := by
  let fpos : ℕ → ℝ :=
    fun n ↦ if n = 0 then 0 else hStarRatio n s ^ 2
  let fzero : ℕ → ℝ :=
    fun n ↦ if n = 0 then hStarRatio 0 s ^ 2 else 0
  have hpos : Summable fpos := by
    simpa only [fpos] using! summable_hStarRatio_positive_square s hs
  have hzero : Summable fzero := by
    exact (hasSum_ite_eq 0 (hStarRatio 0 s ^ 2)).summable
  have hdecomp : (fun n : ℕ ↦ hStarRatio n s ^ 2) =
      fun n ↦ fpos n + fzero n := by
    funext n
    by_cases hn : n = 0 <;> simp [fpos, fzero, hn]
  rw [hdecomp]
  exact hpos.add hzero

/-- A full (zero frequency included) square-sum envelope.  The `64*s` part
is the positive-frequency estimate; the extra `16*s` absorbs the one
zero-frequency term. -/
theorem tsum_hStarRatio_square_le (s : ℕ) (hs : 0 < s) :
    (∑' n : ℕ, hStarRatio n s ^ 2) ≤ 80 * (s : ℝ) := by
  let fpos : ℕ → ℝ :=
    fun n ↦ if n = 0 then 0 else hStarRatio n s ^ 2
  let fzero : ℕ → ℝ :=
    fun n ↦ if n = 0 then hStarRatio 0 s ^ 2 else 0
  have hpos : Summable fpos := by
    simpa only [fpos] using! summable_hStarRatio_positive_square s hs
  have hzeroHas : HasSum fzero (hStarRatio 0 s ^ 2) := by
    exact hasSum_ite_eq 0 (hStarRatio 0 s ^ 2)
  have hzero : Summable fzero := hzeroHas.summable
  have hdecomp : (fun n : ℕ ↦ hStarRatio n s ^ 2) =
      fun n ↦ fpos n + fzero n := by
    funext n
    by_cases hn : n = 0 <;> simp [fpos, fzero, hn]
  have hzeroBound : hStarRatio 0 s ^ 2 ≤ 16 := by
    have hπ : Real.pi ^ 2 / 6 ≤ (4 : ℝ) := by
      nlinarith [Real.pi_pos, Real.pi_le_four]
    nlinarith [hStarRatio_nonneg 0 s, hStarRatio_le_zetaTwo 0 s]
  calc
    (∑' n : ℕ, hStarRatio n s ^ 2) =
        (∑' n : ℕ, (fpos n + fzero n)) := by rw [hdecomp]
    _ = (∑' n : ℕ, fpos n) + (∑' n : ℕ, fzero n) :=
      hpos.tsum_add hzero
    _ = (∑' n : ℕ, if n = 0 then 0 else hStarRatio n s ^ 2) +
        hStarRatio 0 s ^ 2 := by
      rw [hzeroHas.tsum_eq]
    _ ≤ 64 * (s : ℝ) + 16 := by
      gcongr
      exact tsum_hStarRatio_positive_square_le s hs
    _ ≤ 80 * (s : ℝ) := by
      have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      nlinarith

/-- The nonnegative diagonal summand before the denominator factor `p^-4`
is inserted. -/
def naturalCutoffDiagonalTerm (N p n : ℕ) : ℝ :=
  Complex.normSq (ramanujanSum p (n : ℤ)) *
    hStarRatio n (p * N) ^ 2

theorem naturalCutoffDiagonalTerm_nonneg (N p n : ℕ) :
    0 ≤ naturalCutoffDiagonalTerm N p n := by
  exact mul_nonneg (Complex.normSq_nonneg _)
    (sq_nonneg (hStarRatio n (p * N)))

theorem normSq_ramanujanSum_le_totient_sq (p : ℕ) (n : ℤ) :
    Complex.normSq (ramanujanSum p n) ≤ (Nat.totient p : ℝ) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h := norm_ramanujanSum_le_totient p n
  nlinarith [norm_nonneg (ramanujanSum p n)]

theorem summable_naturalCutoffDiagonalTerm
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    Summable (naturalCutoffDiagonalTerm N p) := by
  have hscale : 0 < p * N := Nat.mul_pos hp hN
  have htail := summable_hStarRatio_square (p * N) hscale
  have hdom : Summable
      (fun n : ℕ ↦ (Nat.totient p : ℝ) ^ 2 *
        hStarRatio n (p * N) ^ 2) :=
    htail.mul_left ((Nat.totient p : ℝ) ^ 2)
  apply Summable.of_nonneg_of_le
    (g := naturalCutoffDiagonalTerm N p)
    (f := fun n : ℕ ↦ (Nat.totient p : ℝ) ^ 2 *
      hStarRatio n (p * N) ^ 2)
  · exact naturalCutoffDiagonalTerm_nonneg N p
  · intro n
    unfold naturalCutoffDiagonalTerm
    exact mul_le_mul_of_nonneg_right
      (normSq_ramanujanSum_le_totient_sq p (n : ℤ))
      (sq_nonneg (hStarRatio n (p * N)))
  · exact hdom

/-- On the diagonal the pair correlation is exactly the finite sum of the
nonnegative diagonal terms. -/
theorem naturalCutoffPairCorrelation_self_re
    (N p u v : ℕ) :
    (naturalCutoffPairCorrelation N p p u v).re =
      ∑ n ∈ Icc u v, naturalCutoffDiagonalTerm N p n := by
  unfold naturalCutoffPairCorrelation naturalCutoffDiagonalTerm
  simp only [Complex.re_sum, Complex.mul_re, ramanujanSum_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    naturalCutoffPairWeight, Complex.normSq_apply, add_zero]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem naturalCutoffPairCorrelation_self_re_le_tsum
    (N p u v : ℕ) (hN : 0 < N) (hp : 0 < p) :
    (naturalCutoffPairCorrelation N p p u v).re ≤
      ∑' n : ℕ, naturalCutoffDiagonalTerm N p n := by
  rw [naturalCutoffPairCorrelation_self_re]
  exact (summable_naturalCutoffDiagonalTerm N p hN hp).sum_le_tsum
    (Icc u v) (fun n _hn ↦ naturalCutoffDiagonalTerm_nonneg N p n)

/-- Global diagonal estimate obtained by summing the exact complete-period
blocks.  This is the precise source of the factor `p*phi(p)`; replacing the
Ramanujan sum by its pointwise bound would lose a full power of `p`. -/
theorem tsum_naturalCutoffDiagonalTerm_le
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    (∑' n : ℕ, naturalCutoffDiagonalTerm N p n) ≤
      80 * ((p * Nat.totient p : ℕ) : ℝ) * (N : ℝ) := by
  letI : NeZero p := ⟨hp.ne'⟩
  let f : ℕ → ℝ := naturalCutoffDiagonalTerm N p
  let g : ℕ × Fin p → ℝ := fun z ↦ f (z.1 * p + z.2)
  have hf : Summable f := by
    simpa only [f] using! summable_naturalCutoffDiagonalTerm N p hN hp
  have hg : Summable g := by
    have hcomp := hf.comp_injective (Nat.divModEquiv p).symm.injective
    simpa only [g, f, Nat.divModEquiv_symm_apply] using! hcomp
  have hblocks : Summable (fun j : ℕ ↦ ∑ r : Fin p, g (j, r)) :=
    summable_sum fun r _hr ↦ hg.prod_symm.prod_factor r
  have hmajor : Summable (fun j : ℕ ↦
      ((p * Nat.totient p : ℕ) : ℝ) * hStarRatio j N ^ 2) :=
    (summable_hStarRatio_square N hN).mul_left _
  have hblockLe (j : ℕ) :
      (∑ r : Fin p, g (j, r)) ≤
        ((p * Nat.totient p : ℕ) : ℝ) * hStarRatio j N ^ 2 := by
    change (∑ r : Fin p, f (j * p + (r : ℕ))) ≤
      ((p * Nat.totient p : ℕ) : ℝ) * hStarRatio j N ^ 2
    rw [Fin.sum_univ_eq_sum_range
      (fun r : ℕ ↦ f (j * p + r))]
    simpa only [g, f, naturalCutoffDiagonalTerm] using!
      diagonal_ramanujan_hStar_period_block_le N p j hp
  calc
    (∑' n : ℕ, naturalCutoffDiagonalTerm N p n) = ∑' n : ℕ, f n := by rfl
    _ = ∑' z : ℕ × Fin p, g z := by
      rw [← (Nat.divModEquiv p).symm.tsum_eq f]
      rfl
    _ = ∑' j : ℕ, ∑ r : Fin p, g (j, r) := by
      simpa only [tsum_fintype] using! hg.tsum_prod
    _ ≤ ∑' j : ℕ,
        ((p * Nat.totient p : ℕ) : ℝ) * hStarRatio j N ^ 2 :=
      hblocks.tsum_le_tsum hblockLe hmajor
    _ = ((p * Nat.totient p : ℕ) : ℝ) *
        (∑' j : ℕ, hStarRatio j N ^ 2) := tsum_mul_left
    _ ≤ ((p * Nat.totient p : ℕ) : ℝ) * (80 * (N : ℝ)) := by
      gcongr
      exact tsum_hStarRatio_square_le N hN
    _ = 80 * ((p * Nat.totient p : ℕ) : ℝ) * (N : ℝ) := by ring

/-- After restoring the coefficient denominator `p^-4`, one diagonal
denominator contributes at most `80*N/p^2`.  The final inequality uses only
`phi(p) <= p`; no average-order input is hidden here. -/
theorem scaled_tsum_naturalCutoffDiagonalTerm_le
    (N p : ℕ) (hN : 0 < N) (hp : 0 < p) :
    (1 / (p : ℝ) ^ 4) *
        (∑' n : ℕ, naturalCutoffDiagonalTerm N p n) ≤
      80 * (N : ℝ) / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hφ : (Nat.totient p : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast Nat.totient_le p
  calc
    (1 / (p : ℝ) ^ 4) *
        (∑' n : ℕ, naturalCutoffDiagonalTerm N p n) ≤
        (1 / (p : ℝ) ^ 4) *
          (80 * ((p * Nat.totient p : ℕ) : ℝ) * (N : ℝ)) := by
      gcongr
      exact tsum_naturalCutoffDiagonalTerm_le N p hN hp
    _ = 80 * (N : ℝ) * (Nat.totient p : ℝ) / (p : ℝ) ^ 3 := by
      push_cast
      field_simp
    _ ≤ 80 * (N : ℝ) * (p : ℝ) / (p : ℝ) ^ 3 := by
      gcongr
    _ = 80 * (N : ℝ) / (p : ℝ) ^ 2 := by
      field_simp

/-- The diagonal contribution of the exact dyadic block `Q < p <= 2Q`.
The cardinality of this interval and the lower bound `p > Q` are both used
explicitly, giving the manuscript's `N/Q` scale. -/
theorem sum_scaled_tsum_naturalCutoffDiagonalTerm_Ioc_le
    (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q) :
    (∑ p ∈ Ioc Q (2 * Q),
      (1 / (p : ℝ) ^ 4) *
        (∑' n : ℕ, naturalCutoffDiagonalTerm N p n)) ≤
      80 * (N : ℝ) / (Q : ℝ) := by
  have hcard : (Ioc Q (2 * Q)).card = Q := by
    simp only [Nat.card_Ioc]
    omega
  have hQposR : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  calc
    (∑ p ∈ Ioc Q (2 * Q),
        (1 / (p : ℝ) ^ 4) *
          (∑' n : ℕ, naturalCutoffDiagonalTerm N p n)) ≤
        ∑ p ∈ Ioc Q (2 * Q),
          80 * (N : ℝ) / (p : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hpBlock
      exact scaled_tsum_naturalCutoffDiagonalTerm_le N p hN
        (naturalDenominatorBlock_mem_pos hQ hpBlock)
    _ ≤ ∑ _p ∈ Ioc Q (2 * Q),
          80 * (N : ℝ) / (Q : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p hpBlock
      have hQp : Q ≤ p := (mem_Ioc.mp hpBlock).1.le
      have hQpR : (Q : ℝ) ≤ (p : ℝ) := by exact_mod_cast hQp
      have hsq : (Q : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by nlinarith
      have hinv : 1 / (p : ℝ) ^ 2 ≤ 1 / (Q : ℝ) ^ 2 := by
        exact one_div_le_one_div_of_le (sq_pos_of_pos hQposR) hsq
      have hNnonneg : (0 : ℝ) ≤ 80 * (N : ℝ) := by positivity
      simpa only [div_eq_mul_inv, one_mul] using!
        mul_le_mul_of_nonneg_left hinv hNnonneg
    _ = ((Ioc Q (2 * Q)).card : ℝ) *
          (80 * (N : ℝ) / (Q : ℝ) ^ 2) := by
      rw [sum_const, nsmul_eq_mul]
    _ = (Q : ℝ) * (80 * (N : ℝ) / (Q : ℝ) ^ 2) := by rw [hcard]
    _ = 80 * (N : ℝ) / (Q : ℝ) := by
      field_simp

/-- The entire off-diagonal part of one natural-denominator block is bounded
by an absolute constant.  The outer `sigma_1` average is treated explicitly,
not by a pointwise `log log` estimate. -/
theorem sum_abs_offDiagonalPairCorrelation_Ioc_le
    (N Q u v : ℕ) (hQ : 0 < Q) (huv : u ≤ v) :
    (∑ p ∈ Ioc Q (2 * Q), ∑ p' ∈ Ioc Q (2 * Q),
      if p ≠ p' then
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          |(naturalCutoffPairCorrelation N p p' u v).re|
      else 0) ≤
      64 * (Real.pi ^ 2 / 6) ^ 2 := by
  let Z : ℝ := Real.pi ^ 2 / 6
  let mass : ℕ → ℝ := fun p ↦
    (ArithmeticFunction.sigma 1 p : ℝ) / (p : ℝ) ^ 2
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hmass (p : ℕ) : 0 ≤ mass p := by dsimp [mass]; positivity
  have hpoint {p p' : ℕ}
      (hp : p ∈ Ioc Q (2 * Q)) (hp' : p' ∈ Ioc Q (2 * Q))
      (hne : p ≠ p') :
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          |(naturalCutoffPairCorrelation N p p' u v).re| ≤
        4 * Z ^ 2 * mass p * mass p' := by
    have hpPos := naturalDenominatorBlock_mem_pos hQ hp
    have hp'Pos := naturalDenominatorBlock_mem_pos hQ hp'
    have hcorr := norm_naturalCutoffPairCorrelation_le_uniform
      (N := N) (u := u) (v := v) huv hpPos.ne' hp'Pos.ne' hne
    have hre : |(naturalCutoffPairCorrelation N p p' u v).re| ≤
        ‖naturalCutoffPairCorrelation N p p' u v‖ := Complex.abs_re_le_norm _
    have hscalar : 0 ≤ 1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) := by positivity
    calc
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          |(naturalCutoffPairCorrelation N p p' u v).re| ≤
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            ‖naturalCutoffPairCorrelation N p p' u v‖ :=
        mul_le_mul_of_nonneg_left hre hscalar
      _ ≤ (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (4 * ((ArithmeticFunction.sigma 1 p : ℝ) *
            (ArithmeticFunction.sigma 1 p' : ℝ)) * Z ^ 2) :=
        mul_le_mul_of_nonneg_left hcorr hscalar
      _ = 4 * Z ^ 2 * mass p * mass p' := by
        dsimp [mass, Z]
        ring
  calc
    (∑ p ∈ Ioc Q (2 * Q), ∑ p' ∈ Ioc Q (2 * Q),
        if p ≠ p' then
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            |(naturalCutoffPairCorrelation N p p' u v).re|
        else 0) ≤
        ∑ p ∈ Ioc Q (2 * Q), ∑ p' ∈ Ioc Q (2 * Q),
          4 * Z ^ 2 * mass p * mass p' := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro p' hp'
      by_cases hne : p ≠ p'
      · rw [if_pos hne]
        exact hpoint hp hp' hne
      · rw [if_neg hne]
        positivity
    _ = 4 * Z ^ 2 *
        (∑ p ∈ Ioc Q (2 * Q), mass p) ^ 2 := by
      let S : Finset ℕ := Ioc Q (2 * Q)
      calc
        (∑ p ∈ S, ∑ p' ∈ S, 4 * Z ^ 2 * mass p * mass p') =
            ∑ p ∈ S, (4 * Z ^ 2 * mass p) * (∑ p' ∈ S, mass p') := by
          apply Finset.sum_congr rfl
          intro p _hp
          rw [Finset.mul_sum]
        _ = (∑ p ∈ S, 4 * Z ^ 2 * mass p) *
            (∑ p' ∈ S, mass p') := by
          rw [Finset.sum_mul]
        _ = (4 * Z ^ 2 * (∑ p ∈ S, mass p)) *
            (∑ p' ∈ S, mass p') := by
          have hfactor : (∑ p ∈ S, 4 * Z ^ 2 * mass p) =
              4 * Z ^ 2 * (∑ p ∈ S, mass p) := by
            rw [Finset.mul_sum]
          rw [hfactor]
        _ = 4 * Z ^ 2 * (∑ p ∈ S, mass p) ^ 2 := by ring
        _ = 4 * Z ^ 2 *
            (∑ p ∈ Ioc Q (2 * Q), mass p) ^ 2 := by rfl
    _ ≤ 4 * Z ^ 2 * 4 ^ 2 := by
      have hmassSum : (∑ p ∈ Ioc Q (2 * Q), mass p) ≤ 4 := by
        simpa only [mass] using! sum_sigma_one_div_sq_Ioc_le_four Q hQ
      have hmassSumNonneg : 0 ≤ ∑ p ∈ Ioc Q (2 * Q), mass p := by
        exact Finset.sum_nonneg fun p _hp ↦ hmass p
      gcongr
    _ = 64 * (Real.pi ^ 2 / 6) ^ 2 := by
      dsimp [Z]
      ring

/-- Complete finite-frequency square bound for one dyadic natural-denominator
block.  This combines the exact pair expansion, the `N/Q` diagonal estimate,
and the absolute off-diagonal estimate. -/
theorem sum_naturalDenominatorBlockCoefficient_sq_Icc_le
    (N Q u v : ℕ) (hN : 0 < N) (hQ : 0 < Q) (huv : u ≤ v) :
    (∑ n ∈ Icc u v, naturalDenominatorBlockCoefficient N Q n ^ 2) ≤
      80 * (N : ℝ) / (Q : ℝ) +
        64 * (Real.pi ^ 2 / 6) ^ 2 := by
  let S : Finset ℕ := Ioc Q (2 * Q)
  let D : ℕ → ℝ := fun p ↦
    (1 / (p : ℝ) ^ 4) *
      (∑' n : ℕ, naturalCutoffDiagonalTerm N p n)
  let O : ℕ → ℕ → ℝ := fun p p' ↦
    (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
      |(naturalCutoffPairCorrelation N p p' u v).re|
  have hpair {p p' : ℕ}
      (hp : p ∈ S) (hp' : p' ∈ S) :
      (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
          (naturalCutoffPairCorrelation N p p' u v).re ≤
        (if p = p' then D p else 0) +
          (if p ≠ p' then O p p' else 0) := by
    by_cases hpp' : p = p'
    · subst p'
      have hpPos : 0 < p := naturalDenominatorBlock_mem_pos hQ hp
      have hcorr := naturalCutoffPairCorrelation_self_re_le_tsum
        N p u v hN hpPos
      have hscalar : 0 ≤ 1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2) := by positivity
      calc
        (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
            (naturalCutoffPairCorrelation N p p u v).re ≤
            (1 / ((p : ℝ) ^ 2 * (p : ℝ) ^ 2)) *
              (∑' n : ℕ, naturalCutoffDiagonalTerm N p n) :=
          mul_le_mul_of_nonneg_left hcorr hscalar
        _ = D p := by
          dsimp [D]
          ring
        _ = (if p = p then D p else 0) +
            (if p ≠ p then O p p else 0) := by simp
    · have hre : (naturalCutoffPairCorrelation N p p' u v).re ≤
          |(naturalCutoffPairCorrelation N p p' u v).re| := le_abs_self _
      have hscalar : 0 ≤ 1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2) := by positivity
      calc
        (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            (naturalCutoffPairCorrelation N p p' u v).re ≤
            (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
              |(naturalCutoffPairCorrelation N p p' u v).re| :=
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
    (∑ n ∈ Icc u v, naturalDenominatorBlockCoefficient N Q n ^ 2) =
        ∑ p ∈ S, ∑ p' ∈ S,
          (1 / ((p : ℝ) ^ 2 * (p' : ℝ) ^ 2)) *
            (naturalCutoffPairCorrelation N p p' u v).re := by
      simpa only [S] using!
        sum_naturalDenominatorBlockCoefficient_sq_Icc N Q u v
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
    _ ≤ (80 * (N : ℝ) / (Q : ℝ)) +
          64 * (Real.pi ^ 2 / 6) ^ 2 := by
      gcongr
      · simpa only [S, D] using!
          sum_scaled_tsum_naturalCutoffDiagonalTerm_Ioc_le N Q hN hQ
      · simpa only [S, O] using!
          sum_abs_offDiagonalPairCorrelation_Ioc_le N Q u v hQ huv

theorem summable_sq_naturalDenominatorBlockCoefficient
    (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q) :
    Summable fun n : ℕ ↦ naturalDenominatorBlockCoefficient N Q n ^ 2 := by
  let C : ℝ := 80 * (N : ℝ) / (Q : ℝ) +
    64 * (Real.pi ^ 2 / 6) ^ 2
  apply summable_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro k
  calc
    (∑ n ∈ range k, naturalDenominatorBlockCoefficient N Q n ^ 2) ≤
        ∑ n ∈ Icc 0 k, naturalDenominatorBlockCoefficient N Q n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [mem_Icc]
        exact ⟨Nat.zero_le n, (mem_range.mp hn).le⟩
      · intro n _hn _hnot
        positivity
    _ ≤ C := by
      exact sum_naturalDenominatorBlockCoefficient_sq_Icc_le
        N Q 0 k hN hQ (Nat.zero_le k)

theorem tsum_sq_naturalDenominatorBlockCoefficient_le
    (N Q : ℕ) (hN : 0 < N) (hQ : 0 < Q) :
    (∑' n : ℕ, naturalDenominatorBlockCoefficient N Q n ^ 2) ≤
      80 * (N : ℝ) / (Q : ℝ) +
        64 * (Real.pi ^ 2 / 6) ^ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro k
  calc
    (∑ n ∈ range k, naturalDenominatorBlockCoefficient N Q n ^ 2) ≤
        ∑ n ∈ Icc 0 k, naturalDenominatorBlockCoefficient N Q n ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [mem_Icc]
        exact ⟨Nat.zero_le n, (mem_range.mp hn).le⟩
      · intro n _hn _hnot
        positivity
    _ ≤ 80 * (N : ℝ) / (Q : ℝ) +
          64 * (Real.pi ^ 2 / 6) ^ 2 :=
      sum_naturalDenominatorBlockCoefficient_sq_Icc_le
        N Q 0 k hN hQ (Nat.zero_le k)

/-! ## The divisor-expanded all-denominator tail -/

/-- Positive integers strictly above `M`, parametrized without a boundary
ambiguity by `j |-> M+1+j`. -/
def positiveAboveEquiv (M : ℕ) :
    ℕ ≃ {r : ℕ+ // M < (r : ℕ)} where
  toFun j :=
    ⟨⟨M + 1 + j, by omega⟩, by
      change M < M + 1 + j
      omega⟩
  invFun r := (r : ℕ) - (M + 1)
  left_inv j := by
    dsimp
    omega
  right_inv r := by
    apply Subtype.ext
    apply PNat.eq
    dsimp
    omega

/-- Reindex a strict positive-integer inverse-square tail by its first term.
This equality fixes the endpoint convention used in `r > P/d`. -/
theorem tsum_positiveInverseSquareTerm_above_eq (M : ℕ) :
    (∑' r : ℕ+,
      if M < (r : ℕ) then positiveInverseSquareTerm r else 0) =
      ∑' j : ℕ, inverseSquare (M + 1 + j) := by
  let S : Set ℕ+ := {r | M < (r : ℕ)}
  let f : ℕ+ → ℝ := positiveInverseSquareTerm
  calc
    (∑' r : ℕ+,
        if M < (r : ℕ) then positiveInverseSquareTerm r else 0) =
        ∑' r : ℕ+, S.indicator f r := by
      apply tsum_congr
      intro r
      by_cases hr : M < (r : ℕ) <;> simp [S, f, hr]
    _ = ∑' r : S, f r := by
      symm
      exact tsum_subtype S f
    _ = ∑' j : ℕ, f (positiveAboveEquiv M j) := by
      symm
      exact (positiveAboveEquiv M).tsum_eq (fun r : S ↦ f r)
    _ = ∑' j : ℕ, inverseSquare (M + 1 + j) := by
      apply tsum_congr
      intro j
      change 1 / ((M + 1 + j : ℕ) : ℝ) ^ 2 =
        inverseSquare (M + 1 + j)
      rw [inverseSquare_eq]

/-- Explicit strict inverse-square tail bound. -/
theorem tsum_positiveInverseSquareTerm_above_le (M : ℕ) :
    (∑' r : ℕ+,
      if M < (r : ℕ) then positiveInverseSquareTerm r else 0) ≤
      2 / (M + 1 : ℕ) := by
  rw [tsum_positiveInverseSquareTerm_above_eq]
  exact tsum_inverseSquare_nat_add_le (M + 1) (by omega)

/-- Positive integers at most `T`, identified with the natural interval
`[1,T]`. -/
def positiveAtMostEquiv (T : ℕ) :
    {r : ℕ+ // (r : ℕ) ≤ T} ≃ {k : ℕ // k ∈ Icc 1 T} where
  toFun r := ⟨(r : ℕ), mem_Icc.mpr ⟨r.1.pos, r.2⟩⟩
  invFun k := ⟨⟨(k : ℕ), lt_of_lt_of_le Nat.zero_lt_one
    (mem_Icc.mp k.2).1⟩, (mem_Icc.mp k.2).2⟩
  left_inv r := by
    apply Subtype.ext
    apply PNat.eq
    rfl
  right_inv k := by
    apply Subtype.ext
    rfl

/-- The finite positive reciprocal sum is exactly the harmonic number. -/
theorem tsum_positiveReciprocal_atMost_eq_harmonic (T : ℕ) :
    (∑' r : ℕ+, if (r : ℕ) ≤ T then (1 / (r : ℝ)) else 0) =
      (harmonic T : ℝ) := by
  let S : Set ℕ+ := {r | (r : ℕ) ≤ T}
  let f : ℕ+ → ℝ := fun r ↦ 1 / (r : ℝ)
  calc
    (∑' r : ℕ+, if (r : ℕ) ≤ T then (1 / (r : ℝ)) else 0) =
        ∑' r : ℕ+, S.indicator f r := by
      apply tsum_congr
      intro r
      by_cases hr : (r : ℕ) ≤ T <;> simp [S, f, hr]
    _ = ∑' r : S, f r := by
      symm
      exact tsum_subtype S f
    _ = ∑' k : {k : ℕ // k ∈ Icc 1 T},
          f ((positiveAtMostEquiv T).symm k) := by
      exact ((positiveAtMostEquiv T).symm.tsum_eq (fun r : S ↦ f r)).symm
    _ = ∑ k : {k : ℕ // k ∈ Icc 1 T}, (1 / ((k : ℕ) : ℝ)) := by
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro k _hk
      rfl
    _ = ∑ k ∈ Icc 1 T, (1 / (k : ℝ)) := by
      exact Finset.sum_attach (Icc 1 T) (fun k ↦ 1 / ((k : ℕ) : ℝ))
    _ = (harmonic T : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]

theorem summable_positiveReciprocal_atMost (T : ℕ) :
    Summable fun r : ℕ+ ↦
      if (r : ℕ) ≤ T then (1 / (r : ℝ)) else 0 := by
  have hdom : Summable fun r : ℕ+ ↦
      (T : ℝ) * positiveInverseSquareTerm r :=
    summable_positiveInverseSquareTerm.mul_left (T : ℝ)
  apply Summable.of_nonneg_of_le
    (f := fun r : ℕ+ ↦ (T : ℝ) * positiveInverseSquareTerm r)
  · intro r
    split_ifs <;> positivity
  · intro r
    by_cases hr : (r : ℕ) ≤ T
    · rw [if_pos hr, positiveInverseSquareTerm]
      have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
      have hrR : (r : ℝ) ≤ (T : ℝ) := by exact_mod_cast hr
      rw [div_le_iff₀ hrpos]
      field_simp
      nlinarith
    · rw [if_neg hr]
      exact mul_nonneg (by positivity)
        (by unfold positiveInverseSquareTerm; positivity)
  · exact hdom

/-- The Möbius--`HStar` tail at a fixed divisor `d`.  The strict condition
is the exact integer rendering of `r > P/d`. -/
def mobiusHStarTailAtDivisor (N P n d : ℕ) : ℝ :=
  ∑' r : ℕ+,
    if P / d < (r : ℕ) then
      mobiusSquareTerm r * hStarRatio n (d * (r : ℕ) * N)
    else 0

theorem summable_norm_mobiusHStarTailAtDivisor
    (N P n d : ℕ) :
    Summable fun r : ℕ+ ↦
      ‖if P / d < (r : ℕ) then
          mobiusSquareTerm r * hStarRatio n (d * (r : ℕ) * N)
        else 0‖ := by
  let S : Set ℕ+ := {r | P / d < (r : ℕ)}
  let g : ℕ+ → ℝ := fun r ↦
    (Real.pi ^ 2 / 6) * positiveInverseSquareTerm r
  have hg : Summable g :=
    summable_positiveInverseSquareTerm.mul_left (Real.pi ^ 2 / 6)
  have hgS : Summable (S.indicator g) := hg.indicator S
  apply Summable.of_nonneg_of_le (f := S.indicator g)
  · exact fun r ↦ norm_nonneg _
  · intro r
    by_cases hr : P / d < (r : ℕ)
    · simp only [if_pos hr, norm_mul, Real.norm_eq_abs]
      have hmu := summable_norm_mobiusSquareTerm
      have hμbound : ‖mobiusSquareTerm r‖ ≤ positiveInverseSquareTerm r := by
        have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
        have hμ : |(ArithmeticFunction.moebius (r : ℕ) : ℝ)| ≤ 1 := by
          exact_mod_cast
            (ArithmeticFunction.abs_moebius_le_one (n := (r : ℕ)))
        rw [mobiusSquareTerm, positiveInverseSquareTerm, Real.norm_eq_abs,
          abs_div, abs_pow, abs_of_pos hrpos]
        exact div_le_div_of_nonneg_right hμ (sq_nonneg (r : ℝ))
      have hh0 := hStarRatio_nonneg n (d * (r : ℕ) * N)
      have hh1 := hStarRatio_le_zetaTwo n (d * (r : ℕ) * N)
      rw [abs_of_nonneg hh0]
      have hposInv : 0 ≤ positiveInverseSquareTerm r := by
        unfold positiveInverseSquareTerm
        positivity
      have hproduct :
          ‖mobiusSquareTerm r‖ * hStarRatio n (d * (r : ℕ) * N) ≤
            (Real.pi ^ 2 / 6) * positiveInverseSquareTerm r := by
        calc
          ‖mobiusSquareTerm r‖ * hStarRatio n (d * (r : ℕ) * N) ≤
              positiveInverseSquareTerm r *
                hStarRatio n (d * (r : ℕ) * N) :=
            mul_le_mul_of_nonneg_right hμbound hh0
          _ ≤ positiveInverseSquareTerm r * (Real.pi ^ 2 / 6) :=
            mul_le_mul_of_nonneg_left hh1 hposInv
          _ = (Real.pi ^ 2 / 6) * positiveInverseSquareTerm r := mul_comm _ _
      simpa only [S, g, Set.indicator_of_mem (show r ∈ S by exact hr),
        Real.norm_eq_abs] using!
        hproduct
    · simp only [if_neg hr, norm_zero]
      exact Set.indicator_nonneg (fun _ _ ↦ mul_nonneg (by positivity)
        (by unfold positiveInverseSquareTerm; positivity)) _
  · exact hgS

/-- Fixed-divisor absolute tail estimate.  The first inequality is the
triangle inequality for an absolutely convergent series; the second uses the
strict inverse-square tail and the exact integer division endpoint. -/
theorem abs_mobiusHStarTailAtDivisor_le
    (N P n d : ℕ) (hP : 0 < P) (hd : 0 < d) :
    |mobiusHStarTailAtDivisor N P n d| ≤
      (Real.pi ^ 2 / 6) * (2 * (d : ℝ) / (P : ℝ)) := by
  let S : Set ℕ+ := {r | P / d < (r : ℕ)}
  let g : ℕ+ → ℝ := fun r ↦
    if P / d < (r : ℕ) then
      (Real.pi ^ 2 / 6) * positiveInverseSquareTerm r
    else 0
  have hnorm := summable_norm_mobiusHStarTailAtDivisor N P n d
  have hg : Summable g := by
    have hbase := summable_positiveInverseSquareTerm.mul_left
      (Real.pi ^ 2 / 6)
    have hind := hbase.indicator S
    apply hind.congr
    intro r
    by_cases hr : P / d < (r : ℕ) <;> simp [g, S, hr]
  have hpoint (r : ℕ+) :
      ‖if P / d < (r : ℕ) then
          mobiusSquareTerm r * hStarRatio n (d * (r : ℕ) * N)
        else 0‖ ≤ g r := by
    by_cases hr : P / d < (r : ℕ)
    · simp only [if_pos hr, norm_mul, Real.norm_eq_abs, g]
      have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
      have hμ : |(ArithmeticFunction.moebius (r : ℕ) : ℝ)| ≤ 1 := by
        exact_mod_cast
          (ArithmeticFunction.abs_moebius_le_one (n := (r : ℕ)))
      have hh0 := hStarRatio_nonneg n (d * (r : ℕ) * N)
      have hh1 := hStarRatio_le_zetaTwo n (d * (r : ℕ) * N)
      have hμbound : |mobiusSquareTerm r| ≤ positiveInverseSquareTerm r := by
        rw [mobiusSquareTerm, positiveInverseSquareTerm, abs_div,
          abs_pow, abs_of_pos hrpos]
        exact div_le_div_of_nonneg_right hμ (sq_nonneg (r : ℝ))
      rw [abs_of_nonneg hh0]
      have hposInv : 0 ≤ positiveInverseSquareTerm r := by
        unfold positiveInverseSquareTerm
        positivity
      calc
        |mobiusSquareTerm r| * hStarRatio n (d * (r : ℕ) * N) ≤
            positiveInverseSquareTerm r *
              hStarRatio n (d * (r : ℕ) * N) :=
          mul_le_mul_of_nonneg_right hμbound hh0
        _ ≤ positiveInverseSquareTerm r * (Real.pi ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left hh1 hposInv
        _ = (Real.pi ^ 2 / 6) * positiveInverseSquareTerm r := mul_comm _ _
    · simp [g, hr]
  have htail :
      (∑' r : ℕ+, g r) =
        (Real.pi ^ 2 / 6) *
          (∑' r : ℕ+,
            if P / d < (r : ℕ) then positiveInverseSquareTerm r else 0) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    by_cases hr : P / d < (r : ℕ) <;> simp [g, hr]
  have hdivNat : P < (P / d + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (P / d))
  have hdivReal : (P : ℝ) < ((P / d + 1 : ℕ) : ℝ) * (d : ℝ) := by
    exact_mod_cast hdivNat
  have hPReal : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hMReal : (0 : ℝ) < ((P / d + 1 : ℕ) : ℝ) := by positivity
  have hratio : 2 / ((P / d + 1 : ℕ) : ℝ) ≤
      2 * (d : ℝ) / (P : ℝ) := by
    rw [div_le_div_iff₀ hMReal hPReal]
    nlinarith
  calc
    |mobiusHStarTailAtDivisor N P n d| ≤
        ∑' r : ℕ+,
          ‖if P / d < (r : ℕ) then
              mobiusSquareTerm r * hStarRatio n (d * (r : ℕ) * N)
            else 0‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ+, g r := hnorm.tsum_le_tsum hpoint hg
    _ = (Real.pi ^ 2 / 6) *
          (∑' r : ℕ+,
            if P / d < (r : ℕ) then positiveInverseSquareTerm r else 0) :=
      htail
    _ ≤ (Real.pi ^ 2 / 6) *
          (2 / ((P / d + 1 : ℕ) : ℝ)) := by
      gcongr
      exact tsum_positiveInverseSquareTerm_above_le (P / d)
    _ ≤ (Real.pi ^ 2 / 6) * (2 * (d : ℝ) / (P : ℝ)) := by
      gcongr

/-- High-frequency fixed-divisor estimate.  Compared with the manuscript's
sharper logarithm of `n/(NP)`, this self-contained form uses `H_n`; it is
still more than sufficient after the superlinear cutoff
`P = N(1+log N)^10`. -/
theorem abs_mobiusHStarTailAtDivisor_high_le
    (N P n d : ℕ) (hN : 0 < N) (hn : 0 < n) (hd : 0 < d) :
    |mobiusHStarTailAtDivisor N P n d| ≤
      ((d : ℝ) * (N : ℝ) / (n : ℝ)) *
        (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6)) := by
  let s : ℕ := d * N
  let T : ℕ := n / s
  let C : ℝ := 4 * (s : ℝ) / (n : ℝ)
  let Z : ℝ := Real.pi ^ 2 / 6
  let pref : ℕ+ → ℝ := fun r ↦
    if (r : ℕ) ≤ T then 1 / (r : ℝ) else 0
  let tail : ℕ+ → ℝ := fun r ↦
    if T < (r : ℕ) then positiveInverseSquareTerm r else 0
  let g : ℕ+ → ℝ := fun r ↦ C * pref r + Z * tail r
  have hs : 0 < s := Nat.mul_pos hd hN
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hpref : Summable pref := by
    simpa only [pref] using! summable_positiveReciprocal_atMost T
  have htail : Summable tail := by
    let S : Set ℕ+ := {r | T < (r : ℕ)}
    have h := summable_positiveInverseSquareTerm.indicator S
    apply h.congr
    intro r
    by_cases hr : T < (r : ℕ) <;> simp [tail, S, hr]
  have hg : Summable g := by
    exact (hpref.mul_left C).add (htail.mul_left Z)
  have hmuBound (r : ℕ+) :
      ‖mobiusSquareTerm r‖ ≤ positiveInverseSquareTerm r := by
    have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
    have hμ : |(ArithmeticFunction.moebius (r : ℕ) : ℝ)| ≤ 1 := by
      exact_mod_cast
        (ArithmeticFunction.abs_moebius_le_one (n := (r : ℕ)))
    rw [mobiusSquareTerm, positiveInverseSquareTerm, Real.norm_eq_abs,
      abs_div, abs_pow, abs_of_pos hrpos]
    exact div_le_div_of_nonneg_right hμ (sq_nonneg (r : ℝ))
  have hpoint (r : ℕ+) :
      ‖if P / d < (r : ℕ) then
          mobiusSquareTerm r * hStarRatio n (d * (r : ℕ) * N)
        else 0‖ ≤ g r := by
    by_cases hcut : P / d < (r : ℕ)
    · rw [if_pos hcut, norm_mul]
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (hStarRatio_nonneg n (d * (r : ℕ) * N))]
      by_cases hrT : (r : ℕ) ≤ T
      · have hscale : 0 < d * (r : ℕ) * N := by positivity
        have hdecay := hStarRatio_le_four_mul_scale_div
          n (d * (r : ℕ) * N) hn hscale
        have hbaseNonneg : 0 ≤ positiveInverseSquareTerm r := by
          unfold positiveInverseSquareTerm
          positivity
        calc
          ‖mobiusSquareTerm r‖ *
              hStarRatio n (d * (r : ℕ) * N) ≤
              positiveInverseSquareTerm r *
                hStarRatio n (d * (r : ℕ) * N) :=
            mul_le_mul_of_nonneg_right (hmuBound r)
              (hStarRatio_nonneg _ _)
          _ ≤ positiveInverseSquareTerm r *
              (4 * ((d * (r : ℕ) * N : ℕ) : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hdecay hbaseNonneg
          _ = C * (1 / (r : ℝ)) := by
            dsimp [C, s, positiveInverseSquareTerm]
            have hrR : (r : ℝ) ≠ 0 := by positivity
            push_cast
            field_simp
          _ = g r := by
            have hnotTail : ¬T < (r : ℕ) := Nat.not_lt.mpr hrT
            simp [g, pref, tail, hrT, hnotTail]
      · have hTr : T < (r : ℕ) := Nat.lt_of_not_ge hrT
        calc
          ‖mobiusSquareTerm r‖ *
              hStarRatio n (d * (r : ℕ) * N) ≤
              positiveInverseSquareTerm r *
                hStarRatio n (d * (r : ℕ) * N) :=
            mul_le_mul_of_nonneg_right (hmuBound r)
              (hStarRatio_nonneg _ _)
          _ ≤ positiveInverseSquareTerm r * Z := by
            exact mul_le_mul_of_nonneg_left
              (hStarRatio_le_zetaTwo _ _) (by
                unfold positiveInverseSquareTerm
                positivity)
          _ = g r := by
            simp [g, pref, tail, hrT, hTr, mul_comm, Z]
    · rw [if_neg hcut, norm_zero]
      dsimp [g]
      exact add_nonneg (mul_nonneg hC (by
        dsimp [pref]
        split_ifs <;> positivity))
        (mul_nonneg hZ (by
          dsimp [tail]
          by_cases hr : T < (r : ℕ)
          · rw [if_pos hr]
            unfold positiveInverseSquareTerm
            positivity
          · rw [if_neg hr]))
  have hnorm := summable_norm_mobiusHStarTailAtDivisor N P n d
  have hTsum :
      (∑' r : ℕ+, g r) =
        C * (harmonic T : ℝ) +
          Z * (∑' r : ℕ+,
            if T < (r : ℕ) then positiveInverseSquareTerm r else 0) := by
    calc
      (∑' r : ℕ+, g r) =
          (∑' r : ℕ+, C * pref r) + ∑' r : ℕ+, Z * tail r :=
        (hpref.mul_left C).tsum_add (htail.mul_left Z)
      _ = C * (∑' r : ℕ+, pref r) + Z * (∑' r : ℕ+, tail r) := by
        rw [tsum_mul_left, tsum_mul_left]
      _ = C * (harmonic T : ℝ) +
          Z * (∑' r : ℕ+,
            if T < (r : ℕ) then positiveInverseSquareTerm r else 0) := by
        rw [tsum_positiveReciprocal_atMost_eq_harmonic]
  have hTle : T ≤ n := by
    dsimp [T]
    exact Nat.div_le_self n s
  have hHarmonic : (harmonic T : ℝ) ≤ (harmonic n : ℝ) := by
    have hsub : Icc 1 T ⊆ Icc 1 n := by
      intro k hk
      rw [mem_Icc] at hk ⊢
      exact ⟨hk.1, hk.2.trans hTle⟩
    have hsum :
        (∑ k ∈ Icc 1 T, (1 / (k : ℝ))) ≤
          ∑ k ∈ Icc 1 n, (1 / (k : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k _hk _hnot
      positivity
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, one_div] using! hsum
  have hdivNat : n < (T + 1) * s := by
    dsimp [T]
    exact (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self (n / s))
  have hdivReal : (n : ℝ) < ((T + 1 : ℕ) : ℝ) * (s : ℝ) := by
    exact_mod_cast hdivNat
  have hTposR : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
  have htailRatio : 2 / ((T + 1 : ℕ) : ℝ) ≤
      2 * (s : ℝ) / (n : ℝ) := by
    rw [div_le_div_iff₀ hTposR hnR]
    nlinarith
  calc
    |mobiusHStarTailAtDivisor N P n d| ≤
        ∑' r : ℕ+,
          ‖if P / d < (r : ℕ) then
              mobiusSquareTerm r * hStarRatio n (d * (r : ℕ) * N)
            else 0‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' r : ℕ+, g r := hnorm.tsum_le_tsum hpoint hg
    _ = C * (harmonic T : ℝ) +
          Z * (∑' r : ℕ+,
            if T < (r : ℕ) then positiveInverseSquareTerm r else 0) := hTsum
    _ ≤ C * (harmonic n : ℝ) +
          Z * (2 / ((T + 1 : ℕ) : ℝ)) := by
      gcongr
      exact tsum_positiveInverseSquareTerm_above_le T
    _ ≤ C * (harmonic n : ℝ) +
          Z * (2 * (s : ℝ) / (n : ℝ)) := by
      gcongr
    _ = ((d : ℝ) * (N : ℝ) / (n : ℝ)) *
          (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6)) := by
      dsimp [C, Z, s]
      push_cast
      ring

/-- The exact divisor--Möbius coefficient denoted `A_P(n)` in the crude
all-denominator tail argument. -/
def crudeAllPTailCoefficient (N P n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors,
    (1 / (d : ℝ)) * mobiusHStarTailAtDivisor N P n d

/-- The same tail in its original natural-denominator form. -/
def naturalDenominatorTailCoefficient (N P n : ℕ) : ℝ :=
  ∑' p : ℕ+,
    if P < (p : ℕ) then
      naturalDenominatorCoefficientTerm N n (p : ℕ)
    else 0

/-- Absolute convergence of the full natural-denominator coefficient at a
fixed nonzero frequency.  The proof expands the Ramanujan sum over the
finitely many divisors of `n`; each fixed-multiple series is absolutely
convergent. -/
theorem summable_naturalDenominatorCoefficientTerm
    (N n : ℕ) (hn : n ≠ 0) :
    Summable fun p : ℕ+ ↦
      naturalDenominatorCoefficientTerm N n (p : ℕ) := by
  have hsum : Summable fun p : ℕ+ ↦
      ∑ a ∈ n.divisors,
        if a ∣ (p : ℕ) then
          ((a : ℝ) *
              (ArithmeticFunction.moebius ((p : ℕ) / a) : ℝ) /
            (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
        else 0 := by
    apply summable_sum
    intro a ha
    exact fixed_multiple_term_summable n N
      ⟨a, Nat.pos_of_mem_divisors ha⟩
  apply hsum.congr
  intro p
  unfold naturalDenominatorCoefficientTerm
  rw [ramanujanSum_re_eq_sum_frequency_divisors (p : ℕ) n
    p.ne_zero hn]
  rw [Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  split_ifs <;> ring

theorem summable_naturalDenominatorTailCoefficient
    (N P n : ℕ) (hn : n ≠ 0) :
    Summable fun p : ℕ+ ↦
      if P < (p : ℕ) then
        naturalDenominatorCoefficientTerm N n (p : ℕ)
      else 0 := by
  let S : Set ℕ+ := {p | P < (p : ℕ)}
  have h := (summable_naturalDenominatorCoefficientTerm N n hn).indicator S
  apply h.congr
  intro p
  by_cases hp : P < (p : ℕ) <;> simp [S, hp]

/-- A fixed divisor's contribution above the strict natural cutoff, reindexed
by `p = a*r`. -/
theorem tsum_fixed_multiple_term_above
    (n N P : ℕ) (a : ℕ+) :
    (∑' p : ℕ+,
      if P < (p : ℕ) then
        if (a : ℕ) ∣ (p : ℕ) then
          ((a : ℝ) *
              (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
            (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
        else 0
      else 0) =
      (1 / (a : ℝ)) *
        mobiusHStarTailAtDivisor N P n (a : ℕ) := by
  let S : Set ℕ+ := {p | (a : ℕ) ∣ (p : ℕ)}
  let f : ℕ+ → ℝ := fun p ↦
    if P < (p : ℕ) then
      ((a : ℝ) *
          (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
        (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
    else 0
  calc
    (∑' p : ℕ+,
        if P < (p : ℕ) then
          if (a : ℕ) ∣ (p : ℕ) then
            ((a : ℝ) *
                (ArithmeticFunction.moebius ((p : ℕ) / (a : ℕ)) : ℝ) /
              (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
          else 0
        else 0) = ∑' p : ℕ+, S.indicator f p := by
      apply tsum_congr
      intro p
      by_cases hpCut : P < (p : ℕ)
      · by_cases hpMul : (a : ℕ) ∣ (p : ℕ) <;>
          simp [S, f, hpCut, hpMul]
      · by_cases hpMul : (a : ℕ) ∣ (p : ℕ) <;>
          simp [S, f, hpCut, hpMul]
    _ = ∑' p : S, f p := by
      symm
      exact tsum_subtype S f
    _ = ∑' r : ℕ+, f (positiveMultiplesEquiv a r) := by
      symm
      exact (positiveMultiplesEquiv a).tsum_eq (fun p : S ↦ f p)
    _ = ∑' r : ℕ+,
        if P / (a : ℕ) < (r : ℕ) then
          (1 / (a : ℝ)) *
            (mobiusSquareTerm r *
              hStarRatio n ((a : ℕ) * (r : ℕ) * N))
        else 0 := by
      apply tsum_congr
      intro r
      have hcut : P < (a : ℕ) * (r : ℕ) ↔
          P / (a : ℕ) < (r : ℕ) := by
        constructor
        · intro h
          exact (Nat.div_lt_iff_lt_mul a.pos).mpr
            (by simpa only [mul_comm] using! h)
        · intro h
          have := (Nat.div_lt_iff_lt_mul a.pos).mp h
          simpa only [mul_comm] using! this
      by_cases hr : P / (a : ℕ) < (r : ℕ)
      · have hpa : P < (a : ℕ) * (r : ℕ) := hcut.mpr hr
        change
          (if P < (a : ℕ) * (r : ℕ) then
            ((a : ℝ) *
                (ArithmeticFunction.moebius
                  (((a : ℕ) * (r : ℕ)) / (a : ℕ)) : ℝ) /
              (((a : ℕ) * (r : ℕ) : ℕ) : ℝ) ^ 2) *
                hStarRatio n ((a : ℕ) * (r : ℕ) * N)
            else 0) =
          if P / (a : ℕ) < (r : ℕ) then
            (1 / (a : ℝ)) *
              (mobiusSquareTerm r *
                hStarRatio n ((a : ℕ) * (r : ℕ) * N))
          else 0
        rw [if_pos hpa, if_pos hr]
        have haR : (a : ℝ) ≠ 0 := by positivity
        have hrR : (r : ℝ) ≠ 0 := by positivity
        rw [Nat.mul_div_cancel_left (r : ℕ) a.pos]
        dsimp only [mobiusSquareTerm]
        push_cast
        field_simp
      · have hpa : ¬P < (a : ℕ) * (r : ℕ) := fun h ↦ hr (hcut.mp h)
        change
          (if P < (a : ℕ) * (r : ℕ) then
            ((a : ℝ) *
                (ArithmeticFunction.moebius
                  (((a : ℕ) * (r : ℕ)) / (a : ℕ)) : ℝ) /
              (((a : ℕ) * (r : ℕ) : ℕ) : ℝ) ^ 2) *
                hStarRatio n ((a : ℕ) * (r : ℕ) * N)
            else 0) =
          if P / (a : ℕ) < (r : ℕ) then
            (1 / (a : ℝ)) *
              (mobiusSquareTerm r *
                hStarRatio n ((a : ℕ) * (r : ℕ) * N))
          else 0
        simp [hr, hpa]
    _ = (1 / (a : ℝ)) *
        (∑' r : ℕ+,
          if P / (a : ℕ) < (r : ℕ) then
            mobiusSquareTerm r *
              hStarRatio n ((a : ℕ) * (r : ℕ) * N)
          else 0) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro r
      by_cases hr : P / (a : ℕ) < (r : ℕ) <;> simp [hr]
    _ = (1 / (a : ℝ)) *
        mobiusHStarTailAtDivisor N P n (a : ℕ) := rfl

/-- Exact equality between the original `p > P` Fourier coefficient tail and
the divisor--Möbius expression used for its pointwise estimate. -/
theorem naturalDenominatorTailCoefficient_eq_crudeAllP
    (N P n : ℕ) (hn : n ≠ 0) :
    naturalDenominatorTailCoefficient N P n =
      crudeAllPTailCoefficient N P n := by
  unfold naturalDenominatorTailCoefficient crudeAllPTailCoefficient
  calc
    (∑' p : ℕ+,
        if P < (p : ℕ) then
          naturalDenominatorCoefficientTerm N n (p : ℕ)
        else 0) =
        ∑' p : ℕ+, ∑ a ∈ n.divisors,
          if P < (p : ℕ) then
            if a ∣ (p : ℕ) then
              ((a : ℝ) *
                  (ArithmeticFunction.moebius ((p : ℕ) / a) : ℝ) /
                (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
            else 0
          else 0 := by
      apply tsum_congr
      intro p
      by_cases hpCut : P < (p : ℕ)
      · simp only [hpCut, if_true]
        unfold naturalDenominatorCoefficientTerm
        rw [ramanujanSum_re_eq_sum_frequency_divisors (p : ℕ) n
          p.ne_zero hn]
        rw [Finset.sum_div, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        split_ifs <;> ring
      · simp [hpCut]
    _ = ∑ a ∈ n.divisors, ∑' p : ℕ+,
          if P < (p : ℕ) then
            if a ∣ (p : ℕ) then
              ((a : ℝ) *
                  (ArithmeticFunction.moebius ((p : ℕ) / a) : ℝ) /
                (p : ℝ) ^ 2) * hStarRatio n ((p : ℕ) * N)
            else 0
          else 0 := by
      rw [Summable.tsum_finsetSum]
      intro a ha
      let S : Set ℕ+ := {p | P < (p : ℕ)}
      have hfixed := (fixed_multiple_term_summable n N
        ⟨a, Nat.pos_of_mem_divisors ha⟩).indicator S
      apply hfixed.congr
      intro p
      by_cases hpCut : P < (p : ℕ) <;> simp [S, hpCut]
    _ = ∑ a ∈ n.divisors,
          (1 / (a : ℝ)) * mobiusHStarTailAtDivisor N P n a := by
      apply Finset.sum_congr rfl
      intro a ha
      simpa using! tsum_fixed_multiple_term_above n N P
        ⟨a, Nat.pos_of_mem_divisors ha⟩

/-- The low-frequency pointwise estimate in the crude all-denominator tail.
Here `n.divisors.card` is exactly the divisor-counting function `tau(n)`.
The proof does not need the extra assumption `n <= N*P`; that restriction is
used only when the manuscript sums the resulting squares. -/
theorem abs_crudeAllPTailCoefficient_le
    (N P n : ℕ) (hP : 0 < P) (hn : n ≠ 0) :
    |crudeAllPTailCoefficient N P n| ≤
      (n.divisors.card : ℝ) *
        ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) := by
  unfold crudeAllPTailCoefficient
  calc
    |∑ d ∈ n.divisors,
        (1 / (d : ℝ)) * mobiusHStarTailAtDivisor N P n d| ≤
        ∑ d ∈ n.divisors,
          |(1 / (d : ℝ)) * mobiusHStarTailAtDivisor N P n d| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors,
          (Real.pi ^ 2 / 6) * (2 / (P : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors hdmem) (Nat.pos_of_ne_zero hn)
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (d : ℝ)))]
      calc
        1 / (d : ℝ) * |mobiusHStarTailAtDivisor N P n d| ≤
            1 / (d : ℝ) *
              ((Real.pi ^ 2 / 6) * (2 * (d : ℝ) / (P : ℝ))) := by
          gcongr
          exact abs_mobiusHStarTailAtDivisor_le N P n d hP hd
        _ = (Real.pi ^ 2 / 6) * (2 / (P : ℝ)) := by
          field_simp
    _ = (n.divisors.card : ℝ) *
          ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) := by
      rw [sum_const, nsmul_eq_mul]

/-- High-frequency pointwise form of the crude all-`p` tail. -/
theorem abs_crudeAllPTailCoefficient_high_le
    (N P n : ℕ) (hN : 0 < N) (hn : 0 < n) :
    |crudeAllPTailCoefficient N P n| ≤
      (n.divisors.card : ℝ) *
        (((N : ℝ) / (n : ℝ)) *
          (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6))) := by
  unfold crudeAllPTailCoefficient
  calc
    |∑ d ∈ n.divisors,
        (1 / (d : ℝ)) * mobiusHStarTailAtDivisor N P n d| ≤
        ∑ d ∈ n.divisors,
          |(1 / (d : ℝ)) * mobiusHStarTailAtDivisor N P n d| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors,
          ((N : ℝ) / (n : ℝ)) *
            (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6)) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hd : 0 < d := Nat.pos_of_dvd_of_pos
        (Nat.dvd_of_mem_divisors hdmem) hn
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (d : ℝ)))]
      calc
        1 / (d : ℝ) * |mobiusHStarTailAtDivisor N P n d| ≤
            1 / (d : ℝ) *
              (((d : ℝ) * (N : ℝ) / (n : ℝ)) *
                (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6))) := by
          gcongr
          exact abs_mobiusHStarTailAtDivisor_high_le N P n d hN hn hd
        _ = ((N : ℝ) / (n : ℝ)) *
              (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6)) := by
          field_simp
    _ = (n.divisors.card : ℝ) *
          (((N : ℝ) / (n : ℝ)) *
            (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6))) := by
      rw [sum_const, nsmul_eq_mul]

/-! ## Square summation of the crude tail -/

/-- The low-frequency part `1 <= n <= NP`, using the divisor-square mean
bound from `DivisorSquareAverage`. -/
theorem sum_sq_crudeAllPTailCoefficient_low_le
    (N P : ℕ) (hP : 0 < P) :
    (∑ n ∈ Icc 1 (N * P), crudeAllPTailCoefficient N P n ^ 2) ≤
      ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
        (((N * P : ℕ) : ℝ) * (harmonic (N * P) : ℝ) ^ 3) := by
  let C : ℝ := (Real.pi ^ 2 / 6) * (2 / (P : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    (∑ n ∈ Icc 1 (N * P), crudeAllPTailCoefficient N P n ^ 2) ≤
        ∑ n ∈ Icc 1 (N * P),
          ((n.divisors.card : ℝ) * C) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hnRange
      have hn : n ≠ 0 := by
        have := (mem_Icc.mp hnRange).1
        omega
      have hpoint := abs_crudeAllPTailCoefficient_le N P n hP hn
      have habsNonneg : 0 ≤ |crudeAllPTailCoefficient N P n| := abs_nonneg _
      have hrightNonneg : 0 ≤ (n.divisors.card : ℝ) * C := by positivity
      calc
        crudeAllPTailCoefficient N P n ^ 2 =
            |crudeAllPTailCoefficient N P n| ^ 2 := by
          rw [sq_abs]
        _ ≤ ((n.divisors.card : ℝ) * C) ^ 2 := by
          gcongr
    _ = C ^ 2 *
        ∑ n ∈ Icc 1 (N * P), ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ ≤ C ^ 2 *
        (((N * P : ℕ) : ℝ) * (harmonic (N * P) : ℝ) ^ 3) := by
      gcongr
      exact sum_divisor_card_sq_le_harmonic_cube (N * P)
    _ = ((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
        (((N * P : ℕ) : ℝ) * (harmonic (N * P) : ℝ) ^ 3) := by rfl

/-- A uniform square-sum estimate on any high-frequency interval
`M < n <= X`. -/
theorem sum_sq_crudeAllPTailCoefficient_Ioc_le
    (N P M X : ℕ) (hN : 0 < N) (hM : 0 < M) (hMX : M ≤ X) :
    (∑ n ∈ Ioc M X, crudeAllPTailCoefficient N P n ^ 2) ≤
      (((N : ℝ) / (M : ℝ)) *
        (4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6))) ^ 2 *
        ((X : ℝ) * (harmonic X : ℝ) ^ 3) := by
  let B : ℝ := 4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6)
  let C : ℝ := ((N : ℝ) / (M : ℝ)) * B
  have hXpos : 0 < X := hM.trans_le hMX
  have hB : 0 ≤ B := by
    dsimp [B]
    have hH : 0 ≤ (harmonic X : ℝ) := by
      simpa using! harmonic_cast_mono (A := 0) (B := X) hXpos.le
    positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsubset : Ioc M X ⊆ Icc 1 X := by
    intro n hnRange
    rw [mem_Ioc] at hnRange
    rw [mem_Icc]
    exact ⟨by omega, hnRange.2⟩
  have hsquareSubset :
      (∑ n ∈ Ioc M X, ((n.divisors.card : ℕ) : ℝ) ^ 2) ≤
        ∑ n ∈ Icc 1 X, ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n _hn _hnot
    positivity
  calc
    (∑ n ∈ Ioc M X, crudeAllPTailCoefficient N P n ^ 2) ≤
        ∑ n ∈ Ioc M X, ((n.divisors.card : ℝ) * C) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hnRange
      have hnIoc := mem_Ioc.mp hnRange
      have hn : 0 < n := by omega
      have hpoint := abs_crudeAllPTailCoefficient_high_le N P n hN hn
      have hMn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnIoc.1.le
      have hMReal : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
      have hrecip : (N : ℝ) / (n : ℝ) ≤ (N : ℝ) / (M : ℝ) := by
        have hinv : 1 / (n : ℝ) ≤ 1 / (M : ℝ) :=
          one_div_le_one_div_of_le hMReal hMn
        simpa only [div_eq_mul_inv, one_mul] using!
          mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ (N : ℝ))
      have hHarmonic := harmonic_cast_mono hnIoc.2
      have hHarmonicNonneg : 0 ≤ (harmonic n : ℝ) := by
        simpa using! harmonic_cast_mono (A := 0) (B := n) (Nat.zero_le n)
      have hleftFactor :
          0 ≤ 4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6) := by
        positivity
      have hrightFirst : 0 ≤ (N : ℝ) / (M : ℝ) := by positivity
      have hfactor :
          ((N : ℝ) / (n : ℝ)) *
              (4 * (harmonic n : ℝ) + 2 * (Real.pi ^ 2 / 6)) ≤ C := by
        dsimp [C, B]
        exact mul_le_mul hrecip (by linarith)
          hleftFactor hrightFirst
      have htotal : |crudeAllPTailCoefficient N P n| ≤
          (n.divisors.card : ℝ) * C :=
        hpoint.trans (mul_le_mul_of_nonneg_left hfactor (by positivity))
      calc
        crudeAllPTailCoefficient N P n ^ 2 =
            |crudeAllPTailCoefficient N P n| ^ 2 := by rw [sq_abs]
        _ ≤ ((n.divisors.card : ℝ) * C) ^ 2 := by gcongr
    _ = C ^ 2 *
        ∑ n ∈ Ioc M X, ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ ≤ C ^ 2 *
        ∑ n ∈ Icc 1 X, ((n.divisors.card : ℕ) : ℝ) ^ 2 := by
      gcongr
    _ ≤ C ^ 2 * ((X : ℝ) * (harmonic X : ℝ) ^ 3) := by
      gcongr
      exact sum_divisor_card_sq_le_harmonic_cube X
    _ = (((N : ℝ) / (M : ℝ)) *
          (4 * (harmonic X : ℝ) + 2 * (Real.pi ^ 2 / 6))) ^ 2 *
        ((X : ℝ) * (harmonic X : ℝ) ^ 3) := by rfl

end

end Erdos1002
