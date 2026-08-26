import ErdosProblems.Erdos1002.NearResonantUnconditionalBridge
import ErdosProblems.Erdos1002.NearResonantPeriodicSmooth
import ErdosProblems.Erdos1002.PrimitiveShotL2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Physical-space Parseval bridge for the near-resonant pole

This file connects the unconditional reciprocal-Ramanujan vector estimate to
an actual function on the unit circle.  For a finite denominator interval we
form the smooth reduced-cell representative of the near pole, put it in
circle `L²`, compute every positive Fourier coefficient, and identify each
dyadic Fourier projection isometrically with
`finiteNearRamanujanMultiplierVector`.

Thus the constant-carrier part of the near-resonant square function no longer
ends at a formal coefficient vector.  The remaining carrier work is exactly
the modulation/leakage estimate for the nonzero Fourier modes of the
Bernoulli mark.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ComplexConjugate ENNReal

namespace Erdos1002

noncomputable section

/-! ## The finite physical near-pole tail in circle `L²` -/

/-- Smooth physical representative of the denominators `Q < p ≤ U`. -/
def smoothNearPrimitivePoleTail
    (a ε : ℝ) (Q U : ℕ) (alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Ioc Q U, smoothNearPrimitivePoleSum a ε p alpha

theorem smoothNearPrimitivePoleTail_continuous
    (a ε : ℝ) (Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    Continuous (smoothNearPrimitivePoleTail a ε Q U) := by
  unfold smoothNearPrimitivePoleTail
  apply continuous_finset_sum
  intro p _hp
  exact (smoothNearPrimitivePoleSum_contDiff a ε p ha haε).continuous

private theorem smoothNearPrimitivePoleTail_memLp_Ioc
    (a ε : ℝ) (Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (smoothNearPrimitivePoleTail a ε Q U) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hcont := smoothNearPrimitivePoleTail_continuous a ε Q U ha haε
  have hmeas : AEStronglyMeasurable
      (smoothNearPrimitivePoleTail a ε Q U)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hcont.aestronglyMeasurable.restrict
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  exact hcont.norm.pow 2 |>.integrableOn_Ioc

/-- Fundamental-interval representative on the unit additive circle. -/
def smoothNearPrimitivePoleTailCircle
    (a ε : ℝ) (Q U : ℕ) : AddCircle (1 : ℝ) → ℂ :=
  AddCircle.liftIoc 1 0 (smoothNearPrimitivePoleTail a ε Q U)

theorem smoothNearPrimitivePoleTailCircle_memLp
    (a ε : ℝ) (Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    MemLp (smoothNearPrimitivePoleTailCircle a ε Q U) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance) := by
  have hIoc : MemLp (smoothNearPrimitivePoleTail a ε Q U) 2
      (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa using! smoothNearPrimitivePoleTail_memLp_Ioc a ε Q U ha haε
  exact (hIoc.memLp_liftIoc.haarAddCircle :
    MemLp (AddCircle.liftIoc 1 0
      (smoothNearPrimitivePoleTail a ε Q U)) 2
      (@AddCircle.haarAddCircle (1 : ℝ) inferInstance))

/-- The physical finite near-pole tail as a genuine circle `L²` element. -/
def smoothNearPrimitivePoleTailL2
    (a ε : ℝ) (Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    UnitCircleL2 :=
  (smoothNearPrimitivePoleTailCircle_memLp a ε Q U ha haε).toLp
    (smoothNearPrimitivePoleTailCircle a ε Q U)

theorem smoothNearPrimitivePoleTailL2_coe_ae
    (a ε : ℝ) (Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
      AddCircle (1 : ℝ) → ℂ) =ᵐ[AddCircle.haarAddCircle]
      smoothNearPrimitivePoleTailCircle a ε Q U := by
  exact (smoothNearPrimitivePoleTailCircle_memLp
    a ε Q U ha haε).coeFn_toLp

/-! ## Exact positive Fourier coefficients -/

/-- On the unit interval, one smooth cell representative has the already
computed primitive-pole Fourier coefficient. -/
theorem unitFourierCoefficient_smoothNearPrimitivePoleSum_eq
    (a ε : ℝ) (n p : ℕ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient (smoothNearPrimitivePoleSum a ε p) n =
      ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
        ramanujanSum p (n : ℤ) *
          nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  rw [← unitFourierCoefficient_nearPrimitivePole_eq_ramanujan_of_pos
    a ε n p (by omega) ha hε haε hεhalf]
  unfold unitFourierCoefficient
  apply intervalIntegral.integral_congr_ae
  have hone : ∀ᵐ alpha : ℝ ∂volume, alpha ≠ 1 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hone] with alpha halphaOne
  intro halpha
  have hmem : alpha ∈ Ioo (0 : ℝ) 1 := by
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at halpha
    exact ⟨halpha.1, lt_of_le_of_ne halpha.2 halphaOne⟩
  rw [nearPrimitivePole_eq_smoothNearPrimitivePoleSum
    a ε p hp ha hε haε hεhalf hmem]

/-- Exact positive coefficient of the complete finite denominator tail. -/
theorem unitFourierCoefficient_smoothNearPrimitivePoleTail_eq
    (a ε : ℝ) (Q U n : ℕ) (hQ : 0 < Q)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2) :
    unitFourierCoefficient (smoothNearPrimitivePoleTail a ε Q U) n =
      ∑ p ∈ Finset.Ioc Q U,
        ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
          ramanujanSum p (n : ℤ) *
            nearJ a ε ((n : ℝ) / (p : ℝ) ^ 2) := by
  unfold unitFourierCoefficient smoothNearPrimitivePoleTail
  rw [show (fun alpha ↦
      (∑ p ∈ Finset.Ioc Q U, smoothNearPrimitivePoleSum a ε p alpha) *
        paperExp (-(n : ℝ) * alpha)) =
      (fun alpha ↦ ∑ p ∈ Finset.Ioc Q U,
        smoothNearPrimitivePoleSum a ε p alpha *
          paperExp (-(n : ℝ) * alpha)) by
    funext alpha
    rw [Finset.sum_mul]]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    simpa only [unitFourierCoefficient] using!
      unitFourierCoefficient_smoothNearPrimitivePoleSum_eq
        a ε n p (by
          have := (Finset.mem_Ioc.mp hp).1
          omega) ha hε haε hεhalf
  · intro p hp
    have hphase : Continuous
        (fun alpha : ℝ => paperExp (-(n : ℝ) * alpha)) := by
      unfold paperExp
      fun_prop
    exact ((smoothNearPrimitivePoleSum_contDiff a ε p ha haε).continuous.mul
      hphase).intervalIntegrable 0 1

/-- Fourier coefficient of the circle `L²` representative at a nonnegative
integer frequency. -/
theorem fourierCoeff_smoothNearPrimitivePoleTailL2_nat
    (a ε : ℝ) (Q U n : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    fourierCoeff
        (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) (n : ℤ) =
      unitFourierCoefficient (smoothNearPrimitivePoleTail a ε Q U) n := by
  rw [fourierCoeff_congr_ae
    (smoothNearPrimitivePoleTailL2_coe_ae a ε Q U ha haε)]
  change fourierCoeff
      (AddCircle.liftIoc 1 0 (smoothNearPrimitivePoleTail a ε Q U))
        (n : ℤ) = _
  rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral]
  unfold unitFourierCoefficient
  norm_num
  apply intervalIntegral.integral_congr
  intro alpha _halpha
  simp only
  have hphase :
      ((AddCircle.toCircle
          (-(n • (alpha : AddCircle ((0 : ℝ) + 1 - 0)))) : Circle) : ℂ) =
        paperExp (-(n : ℝ) * alpha) := by
    have hsmul :
        -(n • (alpha : AddCircle ((0 : ℝ) + 1 - 0))) =
          (-(n : ℤ)) • (alpha : AddCircle ((0 : ℝ) + 1 - 0)) := by
      simp
    rw [hsmul]
    change fourier (-(n : ℤ))
        (alpha : AddCircle ((0 : ℝ) + 1 - 0)) = _
    rw [fourier_coe_apply]
    unfold paperExp
    norm_num
    congr 1
    ring
  rw [hphase]
  simpa only [neg_mul] using!
    (mul_comm (paperExp (-(n : ℝ) * alpha))
      (smoothNearPrimitivePoleTail a ε Q U alpha))

/-- The physical coefficient on `K < n ≤ 2K` is literally the matching
coordinate of the finite near-Ramanujan multiplier vector. -/
theorem fourierCoeff_smoothNearPrimitivePoleTailL2_eq_vector
    (a ε : ℝ) (K Q U : ℕ) (n : nearDyadicIndex K)
    (hQ : 0 < Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2) :
    fourierCoeff
        (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
          AddCircle (1 : ℝ) → ℂ) ((n : ℕ) : ℤ) =
      finiteNearRamanujanMultiplierVector a ε K (Q + 1) U n := by
  rw [fourierCoeff_smoothNearPrimitivePoleTailL2_nat,
    unitFourierCoefficient_smoothNearPrimitivePoleTail_eq
      a ε Q U (n : ℕ) hQ ha hε haε hεhalf]
  rw [finiteNearRamanujanMultiplierVector_apply]
  have hset : Finset.Icc (Q + 1) U = Finset.Ioc Q U := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ramanujanSum_even]
  change ((1 / (p : ℝ) ^ 2 : ℝ) : ℂ) *
      ramanujanSum p (((n : ℕ) : ℤ)) *
        nearJ a ε (((n : ℕ) : ℝ) / (p : ℝ) ^ 2) =
    (ramanujanSum p (((n : ℕ) : ℤ)) /
        (((p : ℝ) ^ 2 : ℝ) : ℂ)) *
      nearJ a ε (((n : ℕ) : ℝ) / (p : ℝ) ^ 2)
  push_cast
  ring

/-! ## Finite dyadic Parseval and the unconditional physical bound -/

/-- Positive-frequency dyadic projection of the actual circle `L²` near
pole tail. -/
def smoothNearPrimitivePoleTailDyadicProjection
    (a ε : ℝ) (K Q U : ℕ) (ha : 0 < a) (haε : a ≤ ε / 4) :
    UnitCircleL2 :=
  ∑ n ∈ Finset.Ioc K (2 * K),
    fourierCoeff
      (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
        AddCircle (1 : ℝ) → ℂ) (n : ℤ) • fourierLp 2 (n : ℤ)

/-- Exact finite Parseval identity: the physical dyadic projection and the
Ramanujan multiplier vector have identical norms. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
    (a ε : ℝ) (K Q U : ℕ)
    (hQ : 0 < Q) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) (hεhalf : ε ≤ 1 / 2) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K Q U ha haε‖ =
      ‖finiteNearRamanujanMultiplierVector a ε K (Q + 1) U‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq]
  unfold smoothNearPrimitivePoleTailDyadicProjection
  rw [show
      ‖∑ n ∈ Finset.Ioc K (2 * K),
          fourierCoeff
            (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
              AddCircle (1 : ℝ) → ℂ) (n : ℤ) • fourierLp 2 (n : ℤ)‖ ^ 2 =
        ∑ n ∈ Finset.Ioc K (2 * K),
          ‖fourierCoeff
            (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
              AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 by
    simpa using!
      (orthonormal_fourier.orthogonalFamily.norm_sum
        (fun n : ℤ => fourierCoeff
          (smoothNearPrimitivePoleTailL2 a ε Q U ha haε :
            AddCircle (1 : ℝ) → ℂ) n)
        ((Finset.Ioc K (2 * K)).map
          ⟨(fun n : ℕ => (n : ℤ)), fun _ _ h => Int.ofNat_inj.mp h⟩))]
  rw [← Finset.sum_attach, Finset.attach_eq_univ]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [fourierCoeff_smoothNearPrimitivePoleTailL2_eq_vector
    a ε K Q U n hQ ha hε haε hεhalf]

/-- The unconditional cross-square-root Ramanujan estimate now bounds an
actual physical-space Fourier projection, with the same explicit constant. -/
theorem norm_smoothNearPrimitivePoleTailDyadicProjection_le_unconditional
    (a ε : ℝ) (K Q P U : ℕ)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε ≤ 1 / 2)
    (hK : 0 < K) (hQ : 0 < Q) (hP : 2 ≤ P)
    (hQP : Q < P - 1) (hPm1K : (P - 1) ^ 2 ≤ K)
    (hKP : K ≤ P ^ 2) (hPU : P < U) :
    ‖smoothNearPrimitivePoleTailDyadicProjection a ε K Q U ha haε‖ ≤
      (2 * Real.sqrt 42 * Real.sqrt (K : ℝ) / (Q : ℝ)) *
          (64 * Real.pi * nearProfileDecayConstant) +
        (16 * Real.sqrt 54 + 64 * Real.sqrt 42) * Real.pi *
          nearProfileDecayConstant * (ε / 2 + a) *
          (K : ℝ) / (P : ℝ) ^ 2 := by
  rw [norm_smoothNearPrimitivePoleTailDyadicProjection_eq_vector
    a ε K Q U hQ ha hε haε hεhalf]
  exact norm_finiteNearRamanujanMultiplierVector_tail_le_unconditional
    a ε K Q P U ha hε haε hK hQ hP hQP hPm1K hKP hPU

end

end Erdos1002
