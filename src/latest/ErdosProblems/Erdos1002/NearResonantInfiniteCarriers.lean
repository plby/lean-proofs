import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.NearResonantLiteralMerge
import ErdosProblems.Erdos1002.FixedAwayInfiniteCarriers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Infinite nonzero Bernoulli carriers for the smooth near tail

The pointwise Bernoulli Fourier series is not by itself an `L²` estimate.
This file puts every physical nonzero carrier tail into circle `L²`, proves
its exact norm identity on the fundamental interval, and then sums all
nonzero carriers in the Hilbert space under a common square-energy bound.
Thus later use of the carrier expansion does not exchange a pointwise tsum
with an `L²` norm implicitly.
-/

open Filter MeasureTheory Set AddCircle
open scoped BigOperators ComplexConjugate ENNReal Real Topology

namespace Erdos1002

noncomputable section

local instance nearInfiniteUnitCirclePositive : Fact (0 < (1 : ℝ)) :=
  ⟨by norm_num⟩

/-! ## One physical carrier as a circle `L²` element -/

def smoothNearPrimitivePoleCarrierTailCircle
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ) :
    AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0
    (smoothNearPrimitivePoleCarrierTail N ell a ε Q U)

private theorem smoothNearPrimitivePoleCarrierTail_memLp_Ioc
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hcont := smoothNearPrimitivePoleCarrierTail_continuous
    N Q U ell a ε ha haε
  have hmeas : AEStronglyMeasurable
      (smoothNearPrimitivePoleCarrierTail N ell a ε Q U)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hcont.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  exact hcont.norm.pow 2 |>.integrableOn_Ioc

theorem smoothNearPrimitivePoleCarrierTailCircle_memLp
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (smoothNearPrimitivePoleCarrierTailCircle N ell a ε Q U) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp
      (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa using! smoothNearPrimitivePoleCarrierTail_memLp_Ioc
      N ell a ε Q U ha haε
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0
      (smoothNearPrimitivePoleCarrierTail N ell a ε Q U)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

def smoothNearPrimitivePoleCarrierTailL2
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) : UnitCircleL2 :=
  (smoothNearPrimitivePoleCarrierTailCircle_memLp
    N ell a ε Q U ha haε).toLp
      (smoothNearPrimitivePoleCarrierTailCircle N ell a ε Q U)

theorem smoothNearPrimitivePoleCarrierTailL2_coe_ae
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    (smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q U ha haε :
      AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
        smoothNearPrimitivePoleCarrierTailCircle N ell a ε Q U := by
  exact (smoothNearPrimitivePoleCarrierTailCircle_memLp
    N ell a ε Q U ha haε).coeFn_toLp

/-- The physical carrier's Hilbert norm is exactly its interval energy. -/
theorem norm_sq_smoothNearPrimitivePoleCarrierTailL2
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    ‖smoothNearPrimitivePoleCarrierTailL2
        N ell a ε Q U ha haε‖ ^ 2 =
      ∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2 := by
  let F : UnitCircleL2 :=
    smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q U ha haε
  have hinner := congrArg RCLike.re
    (@L2.inner_def (AddCircle (1 : ℝ)) ℂ ℂ _ _ _ _ _ F F)
  rw [← integral_re] at hinner
  · simp only [← norm_sq_eq_re_inner] at hinner
    calc
      ‖smoothNearPrimitivePoleCarrierTailL2
          N ell a ε Q U ha haε‖ ^ 2 =
        ∫ z : AddCircle (1 : ℝ),
          ‖(F : AddCircle (1 : ℝ) → ℂ) z‖ ^ 2
            ∂AddCircle.haarAddCircle := by simpa only [F] using! hinner
      _ = ∫ z : AddCircle (1 : ℝ),
          ‖smoothNearPrimitivePoleCarrierTailCircle
            N ell a ε Q U z‖ ^ 2
            ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        exact (smoothNearPrimitivePoleCarrierTailL2_coe_ae
          N ell a ε Q U ha haε).fun_comp fun w : ℂ ↦ ‖w‖ ^ 2
      _ = ∫ alpha in (0 : ℝ)..1,
          ‖smoothNearPrimitivePoleCarrierTail
            N ell a ε Q U alpha‖ ^ 2 := by
        unfold smoothNearPrimitivePoleCarrierTailCircle
        rw [show
          (fun z : AddCircle (1 : ℝ) ↦
              ‖AddCircle.liftIoc 1 0
                (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) z‖ ^ 2) =
            AddCircle.liftIoc 1 0
              ((fun w : ℂ ↦ ‖w‖ ^ 2) ∘
                smoothNearPrimitivePoleCarrierTail N ell a ε Q U) by
          funext z
          rfl]
        rw [AddCircle.integral_haarAddCircle]
        norm_num
        simpa only [Function.comp_apply, zero_add] using!
          (AddCircle.integral_liftIoc_eq_intervalIntegral
            (T := (1 : ℝ)) (t := (0 : ℝ))
            (f := (fun w : ℂ ↦ ‖w‖ ^ 2) ∘
              smoothNearPrimitivePoleCarrierTail N ell a ε Q U))
  · exact L2.integrable_inner F F

/-- Convert a finite `ENNReal` physical-energy bound into the real
norm-squared estimate consumed by the Hilbert-space carrier summation. -/
theorem norm_sq_smoothNearPrimitivePoleCarrierTailL2_le_of_ennreal
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) (B : ENNReal) (hB : B ≠ ∞)
    (hbound :
      ENNReal.ofReal
          (∫ alpha in (0 : ℝ)..1,
            ‖smoothNearPrimitivePoleCarrierTail
              N ell a ε Q U alpha‖ ^ 2) ≤
        ENNReal.ofReal
            (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) * B) :
    ‖smoothNearPrimitivePoleCarrierTailL2
        N ell a ε Q U ha haε‖ ^ 2 ≤
      ‖bernoulliMarkFourierCoefficient ell‖ ^ 2 * B.toReal := by
  rw [norm_sq_smoothNearPrimitivePoleCarrierTailL2]
  have hintegral : 0 ≤
      ∫ alpha in (0 : ℝ)..1,
        ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ^ 2 := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun alpha _halpha ↦
      sq_nonneg ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖
  have htop :
      ENNReal.ofReal (‖bernoulliMarkFourierCoefficient ell‖ ^ 2) * B ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  have hreal := ENNReal.toReal_mono htop hbound
  simpa only [ENNReal.toReal_ofReal hintegral,
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sq_nonneg
      ‖bernoulliMarkFourierCoefficient ell‖)] using! hreal

theorem fourierCoeff_smoothNearPrimitivePoleCarrierTailL2
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) (n : ℤ) :
    fourierCoeff
        (smoothNearPrimitivePoleCarrierTailL2
          N ell a ε Q U ha haε : AddCircle (1 : ℝ) → ℂ) n =
      unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) n := by
  rw [fourierCoeff_congr_ae
    (smoothNearPrimitivePoleCarrierTailL2_coe_ae
      N ell a ε Q U ha haε)]
  change fourierCoeff
      (AddCircle.liftIoc 1 0
        (smoothNearPrimitivePoleCarrierTail N ell a ε Q U)) n = _
  rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficientInt
  norm_num [fourier_coe_apply, paperExp]
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  have hstar :
      (starRingEnd ℂ)
          (Complex.exp
            (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) =
        Complex.exp
          (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha))) := by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [map_mul, map_ofNat, Complex.conj_I]
    ring
  change
    (starRingEnd ℂ)
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) *
      smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha =
    smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha)))
  rw [hstar]
  ring

/-! ## Complete nonzero-carrier sum in the Hilbert space -/

def smoothNearNonzeroCarrierL2Term
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    (ell : NonzeroFourierIndex) : UnitCircleL2 :=
  smoothNearPrimitivePoleCarrierTailL2
    N (ell : ℤ) a ε Q U ha haε

private theorem norm_smoothNearNonzeroCarrierL2Term_le
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell : NonzeroFourierIndex,
      ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ ^ 2 ≤
        ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ ^ 2 * C)
    (ell : NonzeroFourierIndex) :
    ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ ≤
      bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C := by
  have hcoeff : 0 ≤ ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ :=
    norm_nonneg _
  have hroot :
      ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ ≤
        ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ * Real.sqrt C := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg hcoeff (Real.sqrt_nonneg C))).mp
    rw [mul_pow, Real.sq_sqrt hC]
    exact hbound ell
  exact hroot.trans (mul_le_mul_of_nonneg_right
    (norm_bernoulliMarkFourierCoefficient_le_majorant (ell : ℤ))
    (Real.sqrt_nonneg C))

theorem summable_smoothNearNonzeroCarrierL2Term
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell : NonzeroFourierIndex,
      ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ ^ 2 ≤
        ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ ^ 2 * C) :
    Summable (smoothNearNonzeroCarrierL2Term N a ε Q U ha haε) := by
  have hmajorAll : Summable fun ell : ℤ ↦
      bernoulliCarrierMajorant ell * Real.sqrt C :=
    summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C)
  have hmajor : Summable fun ell : NonzeroFourierIndex ↦
      bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C :=
    hmajorAll.subtype {ell : ℤ | ell ≠ 0}
  exact hmajor.of_norm_bounded fun ell ↦
    norm_smoothNearNonzeroCarrierL2Term_le
      N a ε Q U ha haε hC hbound ell

def smoothNearInfiniteNonzeroCarrierL2
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) : UnitCircleL2 :=
  ∑' ell : NonzeroFourierIndex,
    smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell

theorem norm_smoothNearInfiniteNonzeroCarrierL2_le
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell : NonzeroFourierIndex,
      ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ ^ 2 ≤
        ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ ^ 2 * C) :
    ‖smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε‖ ≤
      windowCarrierMassConstant * Real.sqrt C := by
  have hs := summable_smoothNearNonzeroCarrierL2Term
    N a ε Q U ha haε hC hbound
  have hnorms : Summable fun ell : NonzeroFourierIndex ↦
      ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ := by
    have hmajorAll : Summable fun ell : ℤ ↦
        bernoulliCarrierMajorant ell * Real.sqrt C :=
      summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C)
    have hmajor : Summable fun ell : NonzeroFourierIndex ↦
        bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C :=
      hmajorAll.subtype {ell : ℤ | ell ≠ 0}
    exact hmajor.of_nonneg_of_le (fun _ell ↦ norm_nonneg _)
      (fun ell ↦ norm_smoothNearNonzeroCarrierL2Term_le
        N a ε Q U ha haε hC hbound ell)
  calc
    ‖smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε‖ ≤
        ∑' ell : NonzeroFourierIndex,
          ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ :=
      norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' ell : NonzeroFourierIndex,
        bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C := by
      exact hnorms.tsum_le_tsum
        (fun ell ↦ norm_smoothNearNonzeroCarrierL2Term_le
          N a ε Q U ha haε hC hbound ell)
        ((summable_bernoulliCarrierMajorant.mul_right
          (Real.sqrt C)).subtype {ell : ℤ | ell ≠ 0})
    _ ≤ ∑' ell : ℤ,
        bernoulliCarrierMajorant ell * Real.sqrt C := by
      exact Summable.tsum_subtype_le
        (fun ell : ℤ ↦ bernoulliCarrierMajorant ell * Real.sqrt C)
        {ell : ℤ | ell ≠ 0}
        (fun ell ↦ mul_nonneg (bernoulliCarrierMajorant_nonneg ell)
          (Real.sqrt_nonneg C))
        (summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C))
    _ = windowCarrierMassConstant * Real.sqrt C := by
      rw [tsum_mul_right]
      rfl

theorem fourierCoeff_smoothNearInfiniteNonzeroCarrierL2
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell : NonzeroFourierIndex,
      ‖smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell‖ ^ 2 ≤
        ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ ^ 2 * C)
    (n : ℤ) :
    fourierCoeff
        (smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) n =
      ∑' ell : NonzeroFourierIndex,
        unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTail
            N (ell : ℤ) a ε Q U) n := by
  have hs := summable_smoothNearNonzeroCarrierL2Term
    N a ε Q U ha haε hC hbound
  rw [← fourierCoefficientCLM_apply]
  unfold smoothNearInfiniteNonzeroCarrierL2
  rw [(fourierCoefficientCLM n).map_tsum hs]
  apply tsum_congr
  intro ell
  simpa only [smoothNearNonzeroCarrierL2Term,
    fourierCoefficientCLM_apply] using!
      fourierCoeff_smoothNearPrimitivePoleCarrierTailL2
        N (ell : ℤ) a ε Q U ha haε n

theorem fourierCoeff_smoothNearInfiniteNonzeroCarrierL2_of_summable
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    (hs : Summable
      (smoothNearNonzeroCarrierL2Term N a ε Q U ha haε))
    (n : ℤ) :
    fourierCoeff
        (smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) n =
      ∑' ell : NonzeroFourierIndex,
        unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTail
            N (ell : ℤ) a ε Q U) n := by
  rw [← fourierCoefficientCLM_apply]
  unfold smoothNearInfiniteNonzeroCarrierL2
  rw [(fourierCoefficientCLM n).map_tsum hs]
  apply tsum_congr
  intro ell
  simpa only [smoothNearNonzeroCarrierL2Term,
    fourierCoefficientCLM_apply] using!
      fourierCoeff_smoothNearPrimitivePoleCarrierTailL2
        N (ell : ℤ) a ε Q U ha haε n

/-! ## Exact denominator-range concatenation -/

theorem smoothNearPrimitivePoleCarrierTail_split
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q R U : ℕ)
    (hQR : Q ≤ R) (hRU : R ≤ U) :
    smoothNearPrimitivePoleCarrierTail N ell a ε Q U =
      smoothNearPrimitivePoleCarrierTail N ell a ε Q R +
        smoothNearPrimitivePoleCarrierTail N ell a ε R U := by
  funext alpha
  unfold smoothNearPrimitivePoleCarrierTail
  change (∑ p ∈ Finset.Ioc Q U,
      smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha) =
    (∑ p ∈ Finset.Ioc Q R,
      smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha) +
    ∑ p ∈ Finset.Ioc R U,
      smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha
  have hdisjoint : Disjoint (Finset.Ioc Q R) (Finset.Ioc R U) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  rw [← Finset.sum_union hdisjoint,
    Finset.Ioc_union_Ioc_eq_Ioc hQR hRU]

theorem smoothNearPrimitivePoleCarrierTailL2_split
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q R U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    (hQR : Q ≤ R) (hRU : R ≤ U) :
    smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q U ha haε =
      smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q R ha haε +
        smoothNearPrimitivePoleCarrierTailL2 N ell a ε R U ha haε := by
  apply Lp.ext
  filter_upwards [
      smoothNearPrimitivePoleCarrierTailL2_coe_ae
        N ell a ε Q U ha haε,
      smoothNearPrimitivePoleCarrierTailL2_coe_ae
        N ell a ε Q R ha haε,
      smoothNearPrimitivePoleCarrierTailL2_coe_ae
        N ell a ε R U ha haε,
      Lp.coeFn_add
        (smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q R ha haε)
        (smoothNearPrimitivePoleCarrierTailL2 N ell a ε R U ha haε)] with
      z hfull hleft hright hadd
  rw [hadd, hfull]
  change smoothNearPrimitivePoleCarrierTailCircle N ell a ε Q U z =
    (smoothNearPrimitivePoleCarrierTailL2 N ell a ε Q R ha haε :
      AddCircle (1 : ℝ) → ℂ) z +
    (smoothNearPrimitivePoleCarrierTailL2 N ell a ε R U ha haε :
      AddCircle (1 : ℝ) → ℂ) z
  rw [hleft, hright]
  unfold smoothNearPrimitivePoleCarrierTailCircle AddCircle.liftIoc
  change smoothNearPrimitivePoleCarrierTail N ell a ε Q U
      ((AddCircle.equivIoc 1 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) =
    smoothNearPrimitivePoleCarrierTail N ell a ε Q R
        ((AddCircle.equivIoc 1 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) +
      smoothNearPrimitivePoleCarrierTail N ell a ε R U
        ((AddCircle.equivIoc 1 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)
  exact congrFun
    (smoothNearPrimitivePoleCarrierTail_split N ell a ε Q R U hQR hRU) _

theorem smoothNearNonzeroCarrierL2Term_split
    (N : ℕ) (a ε : ℝ) (Q R U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    (hQR : Q ≤ R) (hRU : R ≤ U)
    (ell : NonzeroFourierIndex) :
    smoothNearNonzeroCarrierL2Term N a ε Q U ha haε ell =
      smoothNearNonzeroCarrierL2Term N a ε Q R ha haε ell +
        smoothNearNonzeroCarrierL2Term N a ε R U ha haε ell := by
  exact smoothNearPrimitivePoleCarrierTailL2_split
    N (ell : ℤ) a ε Q R U ha haε hQR hRU

/-- Exact concatenation of two denominator ranges after summing all
nonzero carriers in the Hilbert space. -/
theorem smoothNearInfiniteNonzeroCarrierL2_split
    (N : ℕ) (a ε : ℝ) (Q R U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4)
    (hQR : Q ≤ R) (hRU : R ≤ U)
    (hleft : Summable
      (smoothNearNonzeroCarrierL2Term N a ε Q R ha haε))
    (hright : Summable
      (smoothNearNonzeroCarrierL2Term N a ε R U ha haε)) :
    smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε =
      smoothNearInfiniteNonzeroCarrierL2 N a ε Q R ha haε +
        smoothNearInfiniteNonzeroCarrierL2 N a ε R U ha haε := by
  unfold smoothNearInfiniteNonzeroCarrierL2
  rw [← hleft.tsum_add hright]
  apply tsum_congr
  exact smoothNearNonzeroCarrierL2Term_split N a ε Q R U ha haε hQR hRU

end

end Erdos1002
