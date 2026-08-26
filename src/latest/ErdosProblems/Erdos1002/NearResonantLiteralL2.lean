import ErdosProblems.Erdos1002.NearResonantNonzeroParameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Literal smooth near tail as a circle `L²` function

This file identifies the Hilbert-space carrier sum with the literal smooth
physical shot.  The carrier Fourier series is exchanged with the interval
integral by an explicit summable majorant, and Fourier uniqueness is then
used to identify the `L²` classes.
-/

open Filter MeasureTheory Set Finset AddCircle
open scoped BigOperators ComplexConjugate ENNReal Real Topology

namespace Erdos1002

noncomputable section

local instance nearLiteralUnitCirclePositive : Fact (0 < (1 : ℝ)) :=
  ⟨by norm_num⟩

/-! ## Measurability and a literal `L²` representative -/

theorem measurable_smoothNearLiteralShotTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    Measurable (smoothNearLiteralShotTail N a ε Q U) := by
  unfold smoothNearLiteralShotTail
  exact Finset.measurable_fun_sum (Finset.Ioc Q U) fun p _hp ↦
    measurable_smoothNearLiteralShotTerm N p a ε ha haε

theorem norm_smoothNearLiteralShotTail_le
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    ‖smoothNearLiteralShotTail N a ε Q U alpha‖ ≤
      ((Finset.Ioc Q U).card : ℝ) * (1 / (4 * a)) := by
  unfold smoothNearLiteralShotTail
  calc
    ‖∑ p ∈ Finset.Ioc Q U, smoothNearLiteralShotTerm N p a ε alpha‖ ≤
        ∑ p ∈ Finset.Ioc Q U,
          ‖smoothNearLiteralShotTerm N p a ε alpha‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.Ioc Q U, (1 / (4 * a) : ℝ) := by
      gcongr with p hp
      exact norm_smoothNearLiteralShotTerm_le N p a ε alpha ha haε
    _ = ((Finset.Ioc Q U).card : ℝ) * (1 / (4 * a)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

private theorem smoothNearLiteralShotTail_memLp_Ioc
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (smoothNearLiteralShotTail N a ε Q U) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound
    (measurable_smoothNearLiteralShotTail N a ε Q U ha haε).aestronglyMeasurable
    (((Finset.Ioc Q U).card : ℝ) * (1 / (4 * a)))
  filter_upwards with alpha
  exact norm_smoothNearLiteralShotTail_le N a ε Q U alpha ha haε

def smoothNearLiteralShotTailCircle
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (smoothNearLiteralShotTail N a ε Q U)

theorem smoothNearLiteralShotTailCircle_memLp
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (smoothNearLiteralShotTailCircle N a ε Q U) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (smoothNearLiteralShotTail N a ε Q U) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa using! smoothNearLiteralShotTail_memLp_Ioc N a ε Q U ha haε
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0 (smoothNearLiteralShotTail N a ε Q U)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

def smoothNearLiteralShotTailL2
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) : UnitCircleL2 :=
  (smoothNearLiteralShotTailCircle_memLp N a ε Q U ha haε).toLp
  (smoothNearLiteralShotTailCircle N a ε Q U)

/-- The Hilbert-space zero carrier is exactly the constant Bernoulli
coefficient `1/12` times the unmodulated primitive-pole tail.  This is the
`L²` counterpart of `smoothNearPrimitivePoleCarrierTail_zero`; recording it
explicitly avoids silently identifying two independently constructed
representatives later in the quantitative argument. -/
theorem smoothNearPrimitivePoleCarrierTailL2_zero
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    smoothNearPrimitivePoleCarrierTailL2 N 0 a ε Q U ha haε =
      (1 / 12 : ℂ) • smoothNearPrimitivePoleTailL2 a ε Q U ha haε := by
  apply Lp.ext
  filter_upwards [
      smoothNearPrimitivePoleCarrierTailL2_coe_ae
        N 0 a ε Q U ha haε,
      Lp.coeFn_smul (1 / 12 : ℂ)
        (smoothNearPrimitivePoleTailL2 a ε Q U ha haε),
      smoothNearPrimitivePoleTailL2_coe_ae a ε Q U ha haε] with
      z hcarrier hsmul hpole
  rw [hcarrier, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hpole]
  unfold smoothNearPrimitivePoleCarrierTailCircle
    smoothNearPrimitivePoleTailCircle AddCircle.liftIoc
  exact smoothNearPrimitivePoleCarrierTail_zero N a ε Q U
    ((AddCircle.equivIoc 1 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ)

theorem smoothNearLiteralShotTailL2_coe_ae
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    (smoothNearLiteralShotTailL2 N a ε Q U ha haε :
      AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
        smoothNearLiteralShotTailCircle N a ε Q U :=
  (smoothNearLiteralShotTailCircle_memLp N a ε Q U ha haε).coeFn_toLp

theorem fourierCoeff_smoothNearLiteralShotTailL2
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) (n : ℤ) :
    fourierCoeff
        (smoothNearLiteralShotTailL2 N a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) n =
      unitFourierCoefficientInt (smoothNearLiteralShotTail N a ε Q U) n := by
  rw [fourierCoeff_congr_ae
    (smoothNearLiteralShotTailL2_coe_ae N a ε Q U ha haε)]
  change fourierCoeff
      (AddCircle.liftIoc 1 0 (smoothNearLiteralShotTail N a ε Q U)) n = _
  rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficientInt
  norm_num [fourier_coe_apply, paperExp]
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  have hstar :
      (starRingEnd ℂ)
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha))) := by
    rw [← Complex.exp_conj]
    congr 1
    push_cast
    simp [map_mul, map_ofNat, Complex.conj_I]
    ring
  change
    (starRingEnd ℂ)
        (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * alpha)) *
      smoothNearLiteralShotTail N a ε Q U alpha =
    smoothNearLiteralShotTail N a ε Q U alpha *
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) * alpha)))
  rw [hstar]
  ring

/-! ## Dominated exchange of the complete carrier series -/

private theorem norm_paperExp_nearLiteral (t : ℝ) :
    ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

theorem norm_smoothNearPrimitivePoleCarrierTerm_le_of_Ioo
    (N p : ℕ) (ell : ℤ) (a ε alpha : ℝ)
    (hp : 2 ≤ p) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ≤
      bernoulliCarrierMajorant ell * (2 / a) := by
  have hpole := norm_nearPrimitivePole_le_two_div a ε p alpha ha haε
  have heq := nearPrimitivePole_eq_smoothNearPrimitivePoleSum
    a ε p hp ha hε haε hεhalf halpha
  unfold smoothNearPrimitivePoleCarrierTerm unitModulate
  rw [norm_mul, norm_mul, norm_paperExp_nearLiteral, one_mul, ← heq]
  exact mul_le_mul
    (norm_bernoulliMarkFourierCoefficient_le_majorant ell) hpole
    (norm_nonneg _) (bernoulliCarrierMajorant_nonneg ell)

theorem norm_smoothNearPrimitivePoleCarrierTail_le_of_Ioo
    (N : ℕ) (ell : ℤ) (a ε : ℝ) (Q U : ℕ) (alpha : ℝ)
    (hQ : 1 ≤ Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    ‖smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha‖ ≤
      bernoulliCarrierMajorant ell *
        (((Finset.Ioc Q U).card : ℝ) * (2 / a)) := by
  unfold smoothNearPrimitivePoleCarrierTail
  calc
    ‖∑ p ∈ Finset.Ioc Q U,
        smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ ≤
      ∑ p ∈ Finset.Ioc Q U,
        ‖smoothNearPrimitivePoleCarrierTerm N ell a ε p alpha‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.Ioc Q U,
        bernoulliCarrierMajorant ell * (2 / a) := by
      gcongr with p hp
      exact norm_smoothNearPrimitivePoleCarrierTerm_le_of_Ioo
        N p ell a ε alpha (by
          have := (Finset.mem_Ioc.mp hp).1
          omega) ha hε haε hεhalf halpha
    _ = bernoulliCarrierMajorant ell *
        (((Finset.Ioc Q U).card : ℝ) * (2 / a)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      norm_num
      ring

theorem hasSum_unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTail
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (n : ℤ)
    (hQ : 1 ≤ Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2) :
    HasSum
      (fun ell : ℤ ↦ unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) n)
      (unitFourierCoefficientInt (smoothNearLiteralShotTail N a ε Q U) n) := by
  let C : ℝ := ((Finset.Ioc Q U).card : ℝ) * (2 / a)
  let F : ℤ → ℝ → ℂ := fun ell alpha ↦
    smoothNearPrimitivePoleCarrierTail N ell a ε Q U alpha *
      paperExp (-(n : ℝ) * alpha)
  let f : ℝ → ℂ := fun alpha ↦
    smoothNearLiteralShotTail N a ε Q U alpha *
      paperExp (-(n : ℝ) * alpha)
  let bound : ℤ → ℝ → ℝ := fun ell _alpha ↦
    bernoulliCarrierMajorant ell * C
  have hFmeas : ∀ ell : ℤ,
      AEStronglyMeasurable (F ell) (volume.restrict (uIoc (0 : ℝ) 1)) := by
    intro ell
    exact ((smoothNearPrimitivePoleCarrierTail_continuous
      N Q U ell a ε ha haε).mul (by
        unfold paperExp
        fun_prop)).aestronglyMeasurable.restrict
  have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
    simp [ae_iff, measure_singleton]
  have hbound : ∀ ell : ℤ, ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 → ‖F ell alpha‖ ≤ bound ell alpha := by
    intro ell
    filter_upwards [hone] with alpha halphaOne
    intro halpha
    have halphaIoo : alpha ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
      exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
    dsimp [F, bound, C]
    rw [norm_mul, norm_paperExp_nearLiteral, mul_one]
    exact norm_smoothNearPrimitivePoleCarrierTail_le_of_Ioo
      N ell a ε Q U alpha hQ ha hε haε hεhalf halphaIoo
  have hboundSum : ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 →
        Summable fun ell : ℤ ↦ bound ell alpha := by
    filter_upwards with alpha
    intro _halpha
    simpa only [bound] using! summable_bernoulliCarrierMajorant.mul_right C
  have hboundInt : IntervalIntegrable
      (fun alpha : ℝ ↦ ∑' ell : ℤ, bound ell alpha) volume 0 1 := by
    have heq : (fun alpha : ℝ ↦ ∑' ell : ℤ, bound ell alpha) =
        fun _alpha : ℝ ↦ windowCarrierMassConstant * C := by
      funext alpha
      dsimp [bound, windowCarrierMassConstant]
      rw [tsum_mul_right]
    rw [heq]
    exact intervalIntegrable_const
  have hlim : ∀ᵐ alpha : ℝ ∂volume,
      alpha ∈ uIoc (0 : ℝ) 1 →
        HasSum (fun ell : ℤ ↦ F ell alpha) (f alpha) := by
    filter_upwards [hone] with alpha halphaOne
    intro halpha
    have halphaIoo : alpha ∈ Ioo (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
      exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
    have hs := hasSum_smoothNearPrimitivePoleCarrierTail N a ε Q U alpha
    rw [smoothNearBernoulliShotTail_eq_literal
      N a ε Q U alpha hQ ha hε haε hεhalf halphaIoo] at hs
    exact hs.mul_right (paperExp (-(n : ℝ) * alpha))
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    bound hFmeas hbound hboundSum hboundInt hlim
  simpa only [unitFourierCoefficientInt, F, f] using! h

private def nearLiteralNonzeroEquivFinsetComplZero :
    NonzeroFourierIndex ≃ {ell : ℤ // ell ∉ ({0} : Finset ℤ)} where
  toFun ell := ⟨ell, by simpa using! ell.property⟩
  invFun ell := ⟨ell, by simpa using! ell.property⟩
  left_inv ell := by rfl
  right_inv ell := by rfl

theorem zero_add_tsum_nonzero_nearCarrierCoefficient_eq_literal
    (N : ℕ) (a ε : ℝ) (Q U : ℕ) (n : ℤ)
    (hQ : 1 ≤ Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficientInt
        (smoothNearPrimitivePoleCarrierTail N 0 a ε Q U) n +
      ∑' ell : NonzeroFourierIndex,
        unitFourierCoefficientInt
          (smoothNearPrimitivePoleCarrierTail N (ell : ℤ) a ε Q U) n =
      unitFourierCoefficientInt (smoothNearLiteralShotTail N a ε Q U) n := by
  let g : ℤ → ℂ := fun ell ↦ unitFourierCoefficientInt
    (smoothNearPrimitivePoleCarrierTail N ell a ε Q U) n
  have hseries :=
    hasSum_unitFourierCoefficientInt_smoothNearPrimitivePoleCarrierTail
      N a ε Q U n hQ ha hε haε hεhalf
  have hreindex :
      (∑' ell : NonzeroFourierIndex, g (ell : ℤ)) =
        ∑' ell : {ell : ℤ // ell ∉ ({0} : Finset ℤ)}, g (ell : ℤ) := by
    simpa [Function.comp_def, nearLiteralNonzeroEquivFinsetComplZero] using!
      (nearLiteralNonzeroEquivFinsetComplZero.tsum_eq
        (fun ell : {ell : ℤ // ell ∉ ({0} : Finset ℤ)} ↦ g (ell : ℤ)))
  have hdecomp := hseries.summable.sum_add_tsum_subtype_compl ({0} : Finset ℤ)
  rw [hseries.tsum_eq, ← hreindex] at hdecomp
  simpa only [Finset.sum_singleton, g] using! hdecomp

/-- The literal smooth shot is exactly its zero carrier plus the actual
Hilbert-space sum of every nonzero carrier. -/
theorem smoothNearLiteralShotTailL2_eq_zero_add_infiniteNonzero
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (hQ : 1 ≤ Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2)
    (hs : Summable
      (smoothNearNonzeroCarrierL2Term N a ε Q U ha haε)) :
    smoothNearLiteralShotTailL2 N a ε Q U ha haε =
      smoothNearPrimitivePoleCarrierTailL2 N 0 a ε Q U ha haε +
        smoothNearInfiniteNonzeroCarrierL2 N a ε Q U ha haε := by
  apply (@fourierBasis 1 nearLiteralUnitCirclePositive).repr.injective
  ext n
  rw [fourierBasis_repr, fourierBasis_repr]
  have hadd (A B : UnitCircleL2) (k : ℤ) :
      fourierCoeff ((A + B : UnitCircleL2) :
          AddCircle (1 : ℝ) → ℂ) k =
        fourierCoeff (A : AddCircle (1 : ℝ) → ℂ) k +
          fourierCoeff (B : AddCircle (1 : ℝ) → ℂ) k := by
    simpa only [fourierCoefficientCLM_apply] using!
      (fourierCoefficientCLM k).map_add A B
  rw [fourierCoeff_smoothNearLiteralShotTailL2]
  rw [hadd]
  rw [fourierCoeff_smoothNearPrimitivePoleCarrierTailL2,
    fourierCoeff_smoothNearInfiniteNonzeroCarrierL2_of_summable
      N a ε Q U ha haε hs n]
  exact (zero_add_tsum_nonzero_nearCarrierCoefficient_eq_literal
    N a ε Q U n hQ ha hε haε hεhalf).symm

end

end Erdos1002
