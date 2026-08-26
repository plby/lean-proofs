import ErdosProblems.Erdos1002.FixedAwayPartialDyadic
import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Literal `L²` realization of fixed-away coefficient blocks

Square summability is not merely treated as a formal Parseval identity here.
The Fourier Hilbert basis produces an actual element of `L²(ℝ/ℤ)` whose
coefficients are the prescribed sequence, and Parseval identifies its norm
with the real square sum.  This is the precise functional-analytic step used
when the manuscript defines a dyadic block by its Fourier coefficients.
-/

open Filter MeasureTheory Set AddCircle
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

local instance unitCirclePositive : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- An actual unit-circle `L²` element realizing a square-summable integer
coefficient sequence. -/
def fixedAwayCoefficientL2
    (c : ℤ → ℂ) (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2) :
    Lp ℂ 2 (@haarAddCircle 1 unitCirclePositive) :=
  (@fourierBasis 1 unitCirclePositive).repr.symm
    ⟨c, by
      apply memℓp_gen
      simpa using! hc⟩

@[simp] theorem fourierCoeff_fixedAwayCoefficientL2
    (c : ℤ → ℂ) (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2) (n : ℤ) :
    fourierCoeff (fixedAwayCoefficientL2 c hc) n = c n := by
  rw [← fourierBasis_repr]
  simp [fixedAwayCoefficientL2]

/-- Parseval for the coefficient-defined element, with no unidentified
representative function and no unproved exchange of infinite sums. -/
theorem integral_norm_sq_fixedAwayCoefficientL2
    (c : ℤ → ℂ) (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2) :
    (∫ z : AddCircle (1 : ℝ), ‖fixedAwayCoefficientL2 c hc z‖ ^ 2
        ∂haarAddCircle) =
      ∑' n : ℤ, ‖c n‖ ^ 2 := by
  rw [← tsum_sq_fourierCoeff (fixedAwayCoefficientL2 c hc)]
  apply tsum_congr
  intro n
  rw [fourierCoeff_fixedAwayCoefficientL2]

/-- The Hilbert-space norm of the coefficient realization is exactly the
square root of the coefficient energy.  We record the squared form because
it is the one used to sum the infinitely many Bernoulli carriers. -/
theorem norm_fixedAwayCoefficientL2_sq
    (c : ℤ → ℂ) (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2) :
    ‖fixedAwayCoefficientL2 c hc‖ ^ 2 = ∑' n : ℤ, ‖c n‖ ^ 2 := by
  unfold fixedAwayCoefficientL2
  rw [LinearIsometryEquiv.norm_map]
  let x : lp (λ _ : ℤ => ℂ) 2 :=
    ⟨c, by
      apply memℓp_gen
      simpa using! hc⟩
  change ‖x‖ ^ 2 = _
  have hx := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x
  norm_num at hx
  simpa only [x] using! hx

/-- Fourier coefficients determine the `L²` class.  Consequently any
physical construction with the prescribed coefficients is exactly the
Hilbert-basis realization, not merely an element with the same norm. -/
theorem eq_fixedAwayCoefficientL2_of_fourierCoeff
    (f : Lp ℂ 2 (@haarAddCircle 1 unitCirclePositive))
    (c : ℤ → ℂ) (hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2)
    (hcoeff : ∀ n : ℤ, fourierCoeff f n = c n) :
    f = fixedAwayCoefficientL2 c hc := by
  apply (@fourierBasis 1 unitCirclePositive).repr.injective
  ext n
  rw [fourierBasis_repr, fourierBasis_repr,
    fourierCoeff_fixedAwayCoefficientL2, hcoeff]

/-- The literal shifted dyadic block therefore exists in `L²`, has exactly
the manuscript's coefficients, and obeys the proved one-block bound. -/
theorem exists_fixedAwayShiftedDyadicBlockL2
    {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    {J : ℕ} (hJ : 0 < J) :
    ∃ f : Lp ℂ 2 (@haarAddCircle 1 unitCirclePositive),
      (∀ n : ℤ, fourierCoeff f n =
        fixedAwayShiftedDyadicBlock t δ N ell Q n) ∧
      (∫ z : AddCircle (1 : ℝ), ‖f z‖ ^ 2 ∂haarAddCircle) ≤
        fixedAwayShiftedDyadicEnergyConstant t δ J := by
  let c : ℤ → ℂ := fixedAwayShiftedDyadicBlock t δ N ell Q
  have hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2 := by
    simpa only [c] using! summable_fixedAwayShiftedDyadicBlock_norm_sq
      (N := N) (ell := ell) hδ hδt hQ
  refine ⟨fixedAwayCoefficientL2 c hc, ?_, ?_⟩
  · intro n
    simpa only [c] using! fourierCoeff_fixedAwayCoefficientL2 c hc n
  · rw [integral_norm_sq_fixedAwayCoefficientL2]
    simpa only [c] using!
      (tsum_fixedAwayShiftedDyadicBlock_norm_sq_le
        (N := N) (ell := ell) hδ hδt hQ hJ)

/-- The same realization for a partial terminal block. -/
theorem exists_fixedAwayShiftedPartialDyadicBlockL2
    {P : Finset ℕ} {t δ : ℝ} {N Q : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (hQ : 0 < Q)
    (hP : P ⊆ fixedAwayDyadicDenominators Q)
    {J : ℕ} (hJ : 0 < J) :
    ∃ f : Lp ℂ 2 (@haarAddCircle 1 unitCirclePositive),
      (∀ n : ℤ, fourierCoeff f n =
        fixedAwayShiftedPartialDyadicBlock P t δ N ell n) ∧
      (∫ z : AddCircle (1 : ℝ), ‖f z‖ ^ 2 ∂haarAddCircle) ≤
        fixedAwayShiftedDyadicEnergyConstant t δ J := by
  let c : ℤ → ℂ := fixedAwayShiftedPartialDyadicBlock P t δ N ell
  have hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2 := by
    simpa only [c] using! summable_fixedAwayShiftedPartialDyadicBlock_norm_sq
      hδ hδt hQ hP
  refine ⟨fixedAwayCoefficientL2 c hc, ?_, ?_⟩
  · intro n
    simpa only [c] using! fourierCoeff_fixedAwayCoefficientL2 c hc n
  · rw [integral_norm_sq_fixedAwayCoefficientL2]
    simpa only [c] using!
      (tsum_fixedAwayShiftedPartialDyadicBlock_norm_sq_le
        hδ hδt hQ hP hJ)

/-- Low-denominator coefficients also define an actual `L²` element;
its norm is controlled uniformly in the moving threshold. -/
theorem exists_fixedAwayShiftedDyadicTotalSumL2_uniform
    {t δ T R : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hN : 0 < N) (hell : ell ≠ 0) (hR : 0 < R)
    (hcut : ∀ s ∈ nearCarrierDyadicExponents M,
      ((2 ^ s : ℕ) : ℝ) * R ≤ (N : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    ∃ f : Lp ℂ 2 (@haarAddCircle 1 unitCirclePositive),
      (∀ n : ℤ, fourierCoeff f n =
        fixedAwayShiftedDyadicTotalSum t δ N M ell n) ∧
      (∫ z : AddCircle (1 : ℝ), ‖f z‖ ^ 2 ∂haarAddCircle) ≤
        fixedAwayLowCommonEnergyUniformBound T δ R M J := by
  let c : ℤ → ℂ := fixedAwayShiftedDyadicTotalSum t δ N M ell
  have hc : Summable fun n : ℤ ↦ ‖c n‖ ^ 2 := by
    simpa only [c] using! summable_fixedAwayShiftedDyadicTotalSum_norm_sq
      hδ hδt hN hell
  refine ⟨fixedAwayCoefficientL2 c hc, ?_, ?_⟩
  · intro n
    simpa only [c] using! fourierCoeff_fixedAwayCoefficientL2 c hc n
  · rw [integral_norm_sq_fixedAwayCoefficientL2]
    simpa only [c, fixedAwayLowCommonEnergyUniformBound] using!
      (tsum_fixedAwayShiftedDyadicTotalSum_norm_sq_le_of_cutoff_uniform
        (t := t) (δ := δ) (T := T) (R := R)
        (N := N) (M := M) (ell := ell)
        hδ hδt htT hN hell hR hcut hJ)

end

end Erdos1002
