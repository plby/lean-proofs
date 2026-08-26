import ErdosProblems.Erdos67b.MRLemma14TwoLengthSplit

/-!
# Assembly of the source high-frequency smoothing estimate

This file connects the source-normalized smoothing estimates in
`MRLemma14TwoLengthHigh` to the actual two-length Perron segment used by
the finite-`U`/Perron-limit join.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67b

noncomputable section

/-- The actual two-length Perron segment is the difference of the two
single-length normalized Perron segments. -/
theorem dyadicTwoLengthPerronSegment_eq_perronKernelSegment_sub
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y x H₁ H₂ : ℕ} (hx : 0 < x) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (A B : ℝ) :
    dyadicTwoLengthPerronSegment S f Y x H₁ H₂ A B =
      perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₁ A B -
        perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₂ A B := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  have h₁ := continuous_mul_perronIncrementKernel_nat F hF hx hH₁
  have h₂ := continuous_mul_perronIncrementKernel_nat F hF hx hH₂
  unfold dyadicTwoLengthPerronSegment perronKernelSegmentOn
  change (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ t in A..B, F t *
        (perronIncrementKernel x H₁ t - perronIncrementKernel x H₂ t)) = _
  rw [← mul_sub]
  rw [← intervalIntegral.integral_sub
    (h₁.intervalIntegrable A B) (h₂.intervalIntegrable A B)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  ring

/-- Abstract one-band assembly: two single-length source bounds control
the actual two-length Perron segment with only the standard quadratic
triangle factor. -/
theorem sum_normSq_dyadicTwoLengthPerronSegment_le_of_singleBounds
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (A B E₁ E₂ : ℝ)
    (h₁ : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₁ A B)) ≤ E₁)
    (h₂ : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₂ A B)) ≤ E₂) :
    (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ A B)) ≤
      2 * (E₁ + E₂) := by
  have hpoint (x : ℕ) (hxmem : x ∈ Finset.Ioc X (2 * X)) :
      Complex.normSq
          (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ A B) ≤
        2 * (Complex.normSq
            (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
              x H₁ A B) +
          Complex.normSq
            (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
              x H₂ A B)) := by
    have hx : 0 < x := by have := Finset.mem_Ioc.mp hxmem; omega
    rw [dyadicTwoLengthPerronSegment_eq_perronKernelSegment_sub
      S f hx hH₁ hH₂ A B]
    exact normSq_sub_le_two_mul_add _ _
  calc
    (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ A B)) ≤
      ∑ x ∈ Finset.Ioc X (2 * X),
        2 * (Complex.normSq
            (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
              x H₁ A B) +
          Complex.normSq
            (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
              x H₂ A B)) := Finset.sum_le_sum hpoint
    _ = 2 * ((∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
              x H₁ A B)) +
        ∑ x ∈ Finset.Ioc X (2 * X),
          Complex.normSq
            (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
              x H₂ A B)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * (E₁ + E₂) := by linarith

/-- Direct endpoint for the high-frequency quantity in the Perron-limit
join.  Four single-length source estimates (negative/positive band for
each length) give the required finite-`U` high mean square. -/
theorem dyadicTwoLengthPerronHighMeanSquare_le_of_four_singleBounds
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hX : 0 < X) (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    {T U E₁neg E₂neg E₁pos E₂pos : ℝ}
    (h₁neg : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₁ (-U) (-T))) ≤ E₁neg)
    (h₂neg : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₂ (-U) (-T))) ≤ E₂neg)
    (h₁pos : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₁ T U)) ≤ E₁pos)
    (h₂pos : (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H₂ T U)) ≤ E₂pos) :
    dyadicTwoLengthPerronHighMeanSquare S f Y X H₁ H₂ T U ≤
      2 * (E₁neg + E₂neg + E₁pos + E₂pos) := by
  have hneg := sum_normSq_dyadicTwoLengthPerronSegment_le_of_singleBounds
    S f hX hH₁ hH₂ (-U) (-T) E₁neg E₂neg h₁neg h₂neg
  have hpos := sum_normSq_dyadicTwoLengthPerronSegment_le_of_singleBounds
    S f hX hH₁ hH₂ T U E₁pos E₂pos h₁pos h₂pos
  unfold dyadicTwoLengthPerronHighMeanSquare
  rw [Finset.sum_add_distrib]
  linarith

/-- Actual two-length central-band source estimate, still expressed in
terms of the original finite Dirichlet polynomial. -/
theorem sum_normSq_dyadicTwoLengthPerronSegment_le_sourceVerticalEnergy
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hX : 0 < X)
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X)
    {A B : ℝ} (hAB : A ≤ B) :
    (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ A B)) ≤
      2 *
        (sourceSingleVerticalEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₁ A B +
          sourceSingleVerticalEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₂ A B) := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  apply sum_normSq_dyadicTwoLengthPerronSegment_le_of_singleBounds
    S f hX hH₁ hH₂ A B
      (sourceSingleVerticalEnergyBound F X H₁ A B)
      (sourceSingleVerticalEnergyBound F X H₂ A B)
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleVerticalEnergyBound
      F hF hX hH₁ hH₁X hAB
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleVerticalEnergyBound
      F hF hX hH₂ hH₂X hAB

/-- Actual two-length reciprocal-frequency estimate on one band. -/
theorem sum_normSq_dyadicTwoLengthPerronSegment_le_sourceShellEnergy
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hX : 0 < X)
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X)
    {A B T : ℝ} (hAB : A ≤ B) (hT : 0 < T)
    (haway : ∀ t ∈ Set.Icc A B, T ≤ |t|) :
    (∑ x ∈ Finset.Ioc X (2 * X),
      Complex.normSq
        (dyadicTwoLengthPerronSegment S f Y x H₁ H₂ A B)) ≤
      2 *
        (sourceSingleShellEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₁ A B T +
          sourceSingleShellEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₂ A B T) := by
  let F : ℝ → ℂ := dyadicVerticalDirichletPolynomial S f Y
  have hF : Continuous F := continuous_dyadicVerticalDirichletPolynomial S f Y
  apply sum_normSq_dyadicTwoLengthPerronSegment_le_of_singleBounds
    S f hX hH₁ hH₂ A B
      (sourceSingleShellEnergyBound F X H₁ A B T)
      (sourceSingleShellEnergyBound F X H₂ A B T)
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      F hF hX hH₁ hH₁X hAB hT haway
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      F hF hX hH₂ hH₂X hAB hT haway

/-- Finite-`U` source high-frequency endpoint in exactly the shape used
by `dyadicTwoLengthShortMeanSquare_le_of_uniform_high`.  The remaining
uniformity problem is now isolated to bounding the four explicit
`sourceSingleShellEnergyBound` terms. -/
theorem dyadicTwoLengthPerronHighMeanSquare_le_sourceShellEnergy
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H₁ H₂ : ℕ} (hX : 0 < X)
    (hH₁ : 0 < H₁) (hH₂ : 0 < H₂)
    (hH₁X : H₁ ≤ X) (hH₂X : H₂ ≤ X)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    dyadicTwoLengthPerronHighMeanSquare S f Y X H₁ H₂ T U ≤
      2 *
        (sourceSingleShellEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₁ (-U) (-T) T +
          sourceSingleShellEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₂ (-U) (-T) T +
          sourceSingleShellEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₁ T U T +
          sourceSingleShellEnergyBound
            (dyadicVerticalDirichletPolynomial S f Y) X H₂ T U T) := by
  apply dyadicTwoLengthPerronHighMeanSquare_le_of_four_singleBounds
    S f hX hH₁ hH₂
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      _ (continuous_dyadicVerticalDirichletPolynomial S f Y)
      hX hH₁ hH₁X (by linarith) hT (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [abs_of_nonpos (by linarith)]
        linarith)
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      _ (continuous_dyadicVerticalDirichletPolynomial S f Y)
      hX hH₂ hH₂X (by linarith) hT (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [abs_of_nonpos (by linarith)]
        linarith)
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      _ (continuous_dyadicVerticalDirichletPolynomial S f Y)
      hX hH₁ hH₁X hTU hT (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [abs_of_nonneg (by linarith)]
        linarith)
  · exact sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      _ (continuous_dyadicVerticalDirichletPolynomial S f Y)
      hX hH₂ hH₂X hTU hT (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [abs_of_nonneg (by linarith)]
        linarith)

/-- One-length positive/negative high-frequency mass.  This is the
high-frequency quantity needed when the same Perron-limit method is used
to control the longer normalized average in `MRLemma14UncenteredJoin`. -/
def dyadicSinglePerronHighMeanSquare
    (S : Finset ℕ) (f : ℕ → ℂ) (Y X H : ℕ) (T U : ℝ) : ℝ :=
  ∑ x ∈ Finset.Ioc X (2 * X),
    (Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H (-U) (-T)) +
      Complex.normSq
        (perronKernelSegmentOn (dyadicVerticalDirichletPolynomial S f Y)
          x H T U))

/-- The one-length finite-`U` source shell endpoint, expressed through
the same original-polynomial energies as the two-length theorem. -/
theorem dyadicSinglePerronHighMeanSquare_le_sourceShellEnergy
    (S : Finset ℕ) (f : ℕ → ℂ)
    {Y X H : ℕ} (hX : 0 < X) (hH : 0 < H) (hHX : H ≤ X)
    {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U) :
    dyadicSinglePerronHighMeanSquare S f Y X H T U ≤
      sourceSingleShellEnergyBound
        (dyadicVerticalDirichletPolynomial S f Y) X H (-U) (-T) T +
      sourceSingleShellEnergyBound
        (dyadicVerticalDirichletPolynomial S f Y) X H T U T := by
  have hneg :=
    sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      (dyadicVerticalDirichletPolynomial S f Y)
      (continuous_dyadicVerticalDirichletPolynomial S f Y)
      hX hH hHX (show -U ≤ -T by linarith) hT (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [abs_of_nonpos (by linarith)]
        linarith)
  have hpos :=
    sum_normSq_perronKernelSegmentOn_le_sourceSingleShellEnergyBound
      (dyadicVerticalDirichletPolynomial S f Y)
      (continuous_dyadicVerticalDirichletPolynomial S f Y)
      hX hH hHX hTU hT (by
        intro t ht
        rw [Set.mem_Icc] at ht
        rw [abs_of_nonneg (by linarith)]
        linarith)
  unfold dyadicSinglePerronHighMeanSquare
  rw [Finset.sum_add_distrib]
  linarith

end

end Erdos67b
