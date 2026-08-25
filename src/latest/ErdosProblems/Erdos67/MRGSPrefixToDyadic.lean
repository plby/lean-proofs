import ErdosProblems.Erdos67.MRFiniteHalaszAbel
import ErdosProblems.Erdos67.MRGSLemma71
import ErdosProblems.Erdos67.MRAppendixLargeValues
import ErdosProblems.Erdos67.MRFiniteHalaszTypicalSetBridge

/-!
# From GS normalized prefixes to the dyadic vertical polynomial

The A.8--A.9 argument controls every normalized prefix between `X` and
`2X`.  This module takes the difference of the two relevant prefixes and
then applies the existing finite Abel transform.  The explicit loss is only
the harmless factor three.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

/-- The two logarithmic-phase conventions used by the GS prefix and the
dyadic vertical polynomial agree on positive integers. -/
theorem natLogTwist_eq_logarithmicPhase_neg
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    LogPhaseSum.natLogTwist n t = logarithmicPhase n (-t) := by
  rw [LogPhaseSum.natLogTwist_eq_archimedeanTwist_neg,
    logarithmicPhase_eq_archimedeanTwist hn]

/-- A raw interval prefix on `(X,y]` is the difference of two GS prefixes. -/
theorem complexIntervalPartialSum_dyadicHalaszRaw_full_eq_gsPrefix_sub
    (a : ℕ → ℂ) {X y : ℕ} (hXy : X ≤ y) (hy : y ≤ 2 * X) (t : ℝ) :
    LSeriesLogPhaseBridge.complexIntervalPartialSum
        (dyadicHalaszRawCoefficient (Finset.Ioc X (2 * X)) a t)
        (X + 1) y =
      gsTwistedPositivePrefixSum a t y -
        gsTwistedPositivePrefixSum a t X := by
  unfold LSeriesLogPhaseBridge.complexIntervalPartialSum
  have hset : Finset.Icc (X + 1) y = Finset.Ioc X y := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  have hraw :
      (∑ n ∈ Finset.Ioc X y,
          dyadicHalaszRawCoefficient (Finset.Ioc X (2 * X)) a t n) =
        ∑ n ∈ Finset.Ioc X y,
          a n * LogPhaseSum.natLogTwist n t := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnIoc := Finset.mem_Ioc.mp hn
    have hnFull : n ∈ Finset.Ioc X (2 * X) := by
      exact Finset.mem_Ioc.mpr ⟨hnIoc.1, hnIoc.2.trans hy⟩
    simp only [dyadicHalaszRawCoefficient, hnFull, if_true]
    rw [natLogTwist_eq_logarithmicPhase_neg (by omega)]
  rw [hraw]
  unfold gsTwistedPositivePrefixSum
  have hsubset : Finset.Ioc 0 X ⊆ Finset.Ioc 0 y := by
    intro n hn
    exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans hXy⟩
  have hdiff : Finset.Ioc 0 y \ Finset.Ioc 0 X = Finset.Ioc X y := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  rw [← hdiff]
  exact eq_sub_of_add_eq (Finset.sum_sdiff hsubset
    (f := fun n ↦ a n * LogPhaseSum.natLogTwist n t))

/-- A normalized GS prefix bound on `[X,2X]` implies the corresponding
dyadic vertical polynomial bound with constant `3`. -/
theorem norm_dyadicVerticalDirichletPolynomial_le_of_normalized_gsPrefixes
    (a : ℕ → ℂ) {X : ℕ} (hX : 0 < X) (t : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ N ∈ Finset.Icc X (2 * X),
      ‖gsTwistedPositivePrefixSum a t N / (N : ℂ)‖ ≤ B) :
    ‖dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) a X t‖ ≤
      3 * B := by
  apply norm_dyadicVerticalDirichletPolynomial_le_of_prefix_bound_mul
    (Finset.Ioc X (2 * X)) a hX t (mul_nonneg (by norm_num) hB)
  intro y hy
  have hyIcc := Finset.mem_Icc.mp hy
  have hXy : X ≤ y := by omega
  have hypos : 0 < y := hX.trans_le hXy
  have hXmem : X ∈ Finset.Icc X (2 * X) := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hymem : y ∈ Finset.Icc X (2 * X) :=
    Finset.mem_Icc.mpr ⟨hXy, hyIcc.2⟩
  have hprefixX := hprefix X hXmem
  have hprefixy := hprefix y hymem
  have hsumX : ‖gsTwistedPositivePrefixSum a t X‖ ≤ B * X := by
    rw [norm_div, Complex.norm_natCast] at hprefixX
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    calc
      ‖gsTwistedPositivePrefixSum a t X‖ =
          (‖gsTwistedPositivePrefixSum a t X‖ / X) * X := by
        field_simp
      _ ≤ B * X := mul_le_mul_of_nonneg_right hprefixX hXR.le
  have hsumy : ‖gsTwistedPositivePrefixSum a t y‖ ≤ B * y := by
    rw [norm_div, Complex.norm_natCast] at hprefixy
    have hyR : (0 : ℝ) < y := by exact_mod_cast hypos
    calc
      ‖gsTwistedPositivePrefixSum a t y‖ =
          (‖gsTwistedPositivePrefixSum a t y‖ / y) * y := by
        field_simp
      _ ≤ B * y := mul_le_mul_of_nonneg_right hprefixy hyR.le
  rw [complexIntervalPartialSum_dyadicHalaszRaw_full_eq_gsPrefix_sub
    a hXy hyIcc.2 t]
  calc
    ‖gsTwistedPositivePrefixSum a t y -
        gsTwistedPositivePrefixSum a t X‖ ≤
      ‖gsTwistedPositivePrefixSum a t y‖ +
        ‖gsTwistedPositivePrefixSum a t X‖ := norm_sub_le _ _
    _ ≤ B * y + B * X := add_le_add hsumy hsumX
    _ ≤ (3 * B) * X := by
      have hyR : (y : ℝ) ≤ 2 * X := by exact_mod_cast hyIcc.2
      nlinarith

/-- Actual MRT two-block typical-set form of the normalized-prefix bridge. -/
theorem norm_twoBlockTypical_dyadicVerticalDirichletPolynomial_le_of_normalized_gsPrefixes
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    (f : ℕ → ℂ) {Y Z : ℕ} (hY : 0 < Y) (hYZ : 2 * Y ≤ Z)
    (t : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ N ∈ Finset.Icc Y (2 * Y),
      ‖gsTwistedPositivePrefixSum
          (MRHalaszBands.finiteHalaszTypicalCoefficient f
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) t N /
          (N : ℂ)‖ ≤ B) :
    ‖dyadicVerticalDirichletPolynomial
        (typicalFactorizationSet {I₁, I₂} Z) f Y t‖ ≤ 3 * B := by
  rw [dyadicVerticalDirichletPolynomial_twoBlockTypical_eq_finiteHalasz
    hdisj f hY hYZ]
  rw [MRHalaszBands.dyadicVerticalDirichletPolynomial_typicalSet_eq_coefficient]
  exact norm_dyadicVerticalDirichletPolynomial_le_of_normalized_gsPrefixes
    (MRHalaszBands.finiteHalaszTypicalCoefficient f
      (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)) hY t hB hprefix

end

end Erdos67
