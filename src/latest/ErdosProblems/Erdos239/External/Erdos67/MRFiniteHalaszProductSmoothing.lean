import ErdosProblems.Erdos239.External.Erdos67.MRFiniteHalaszCountableSmoothing

/-!
# Exact compact smoothing of the finite Halasz three-band product

The selected prime band is kept as a complete, absolutely convergent Euler
factor, while the two complementary bands are positive finite prefixes.  The
coefficient of their convolution is the original multiplicative coefficient
exactly when both complementary prime bands occur, and is zero otherwise.

Compact support of the logarithmic window turns the countable smoothing
identity into a genuinely finite sum.  Thus the product identity below makes
no comparison between a complete L-series and a finite tail.
-/

open scoped BigOperators LSeries.notation
open Complex Finset MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67.MRFiniteHalaszSmoothing

/-- The one-complete/two-positive-finite coefficient used in the direct
finite Halasz argument. -/
def finiteHalaszHybridCoefficient
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (N : ℕ) : ℕ → ℂ :=
  LSeries.convolution
    (primeBandCoefficient f P₁)
    (LSeries.convolution
      (positivePrefixTruncate
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
      (positivePrefixTruncate
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N))

/-- The finite typical coefficient selected by the two complementary prime
bands. -/
def finiteHalaszTypicalCoefficient
    (f : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] : ℕ → ℂ :=
  fun n ↦
    if HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ P₂ p) n ∧
        HasPrimeFactor (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p) n then
      f n else 0

theorem finiteHalaszHybridCoefficient_apply
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    finiteHalaszHybridCoefficient f P₁ P₂ N n =
      finiteHalaszTypicalCoefficient f P₁ P₂ n := by
  exact convolution_oneFull_twoPositiveTruncated_apply_ite
    hmul P₁ P₂ hn hnN

theorem finiteHalaszHybridCoefficient_LSeriesSummable
    {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (N : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (finiteHalaszHybridCoefficient f P₁ P₂ N) s := by
  exact (primeBandCoefficient_LSeriesSummable hbound P₁ hs).convolution
    ((positivePrefixTruncate_LSeriesSummable
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N s).convolution
      (positivePrefixTruncate_LSeriesSummable
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N s))

/-- Compact logarithmic smoothing of the hybrid L-series is exactly a finite
sum of the typical coefficients.  The upper support condition `B ≤ log N`
is the only truncation input; outside it the window vanishes identically. -/
theorem integral_finiteHalaszHybrid_mul_logTrapezoidKernel
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N : ℕ} (hN : 0 < N) {sigma : ℝ} (hsigma : 1 < sigma)
    (delta A B : ℝ) (hdelta : 0 < delta) (hB : B ≤ Real.log N)
    (t0 : ℝ) :
    (∫ xi : ℝ,
        LSeries (finiteHalaszHybridCoefficient f P₁ P₂ N)
            ((sigma : ℂ) + Complex.I * ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          logTrapezoidKernel delta A B hdelta xi) =
      ∑ n ∈ Finset.Ioc 1 N,
        LSeries.term (finiteHalaszTypicalCoefficient f P₁ P₂)
            (sigma : ℂ) n *
          logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  classical
  rw [integral_LSeries_mul_logTrapezoidKernel
    (finiteHalaszHybridCoefficient f P₁ P₂ N) sigma
    (finiteHalaszHybridCoefficient_LSeriesSummable
      hbound P₁ P₂ N (by simpa using hsigma))
    delta A B hdelta t0]
  rw [tsum_eq_sum (s := Finset.Ioc 1 N)]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnI := Finset.mem_Ioc.mp hn
    have hnpos : 0 < n := by omega
    have hnN : n ≤ N := hnI.2
    rw [LSeries.term_of_ne_zero hnpos.ne',
      LSeries.term_of_ne_zero hnpos.ne',
      finiteHalaszHybridCoefficient_apply hmul P₁ P₂ hnpos hnN]
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n ≤ 1
    · have hnEq : n = 1 := by omega
      subst n
      rw [LSeries.term_of_ne_zero (by norm_num),
        finiteHalaszHybridCoefficient_apply hmul P₁ P₂ (by norm_num)
          (by omega)]
      simp [finiteHalaszTypicalCoefficient, HasPrimeFactor]
    · have hNn : N < n := by
        by_contra hnot
        exact hn (Finset.mem_Ioc.mpr ⟨Nat.lt_of_not_ge hn1,
          Nat.le_of_not_gt hnot⟩)
      have hlog : Real.log (N : ℝ) < Real.log (n : ℝ) :=
        Real.strictMonoOn_log
          (show (N : ℝ) ∈ Set.Ioi 0 by
            rw [Set.mem_Ioi]
            exact_mod_cast hN)
          (show (n : ℝ) ∈ Set.Ioi 0 by
            rw [Set.mem_Ioi]
            exact_mod_cast (Nat.pos_of_ne_zero hn0))
          (by exact_mod_cast hNn)
      have hnotmem : Real.log (n : ℝ) ∉ Set.Icc A B := by
        intro hmem
        linarith [hmem.2]
      rw [logTrapezoidWindow_eq_zero_of_not_mem delta A B hdelta hnotmem,
        mul_zero]

/-- Exact analytic factorization of the compactly smoothed hybrid.  The
selected prime band is complete, while both other factors are finite. -/
theorem integral_finiteHalaszProduct_mul_logTrapezoidKernel
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {N : ℕ} (hN : 0 < N) {sigma : ℝ} (hsigma : 1 < sigma)
    (delta A B : ℝ) (hdelta : 0 < delta) (hB : B ≤ Real.log N)
    (t0 : ℝ) :
    (∫ xi : ℝ,
        (LSeries (primeBandCoefficient f P₁)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          (LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
            LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)))) *
          logTrapezoidKernel delta A B hdelta xi) =
      ∑ n ∈ Finset.Ioc 1 N,
        LSeries.term (finiteHalaszTypicalCoefficient f P₁ P₂)
            (sigma : ℂ) n *
          logarithmicPhase n (-t0) *
          logTrapezoidWindow delta A B hdelta (Real.log n) := by
  rw [← integral_finiteHalaszHybrid_mul_logTrapezoidKernel
    hmul hbound P₁ P₂ hN hsigma delta A B hdelta hB t0]
  apply integral_congr_ae
  filter_upwards with xi
  have hsxi :
      1 < (((sigma : ℂ) + Complex.I *
        ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))).re := by
    simpa using hsigma
  rw [show
      LSeries (finiteHalaszHybridCoefficient f P₁ P₂ N)
          ((sigma : ℂ) + Complex.I *
            ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) =
        LSeries (primeBandCoefficient f P₁)
            ((sigma : ℂ) + Complex.I *
              ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
          (LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ)) *
            LSeries
              (positivePrefixTruncate
                (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) N)
              ((sigma : ℂ) + Complex.I *
                ((t0 - 2 * Real.pi * xi : ℝ) : ℂ))) by
      unfold finiteHalaszHybridCoefficient
      exact LSeries_convolution_oneFull_twoPositiveTruncated
        hbound P₁ P₂ N hsxi]

end

end Erdos67.MRHalaszBands
