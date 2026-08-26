import ErdosProblems.Erdos520.HarperExplicitPrefixWindows
import ErdosProblems.Erdos520.HarperMovingHeightUniformConstants

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem520

/-!
# Restricted recursion with a positive logarithmic prefix barrier

The prefix-local mesh entropy grows logarithmically with the prefix length.
Consequently its natural centered upper boundary is
`x + 8 * log (k+2)`, not the decreasing normalized reverse-log boundary.
This file packages the deterministic containment and the restricted moment
step for that exact shape.  The probability input is kept explicit so that
the sharp positive-log ballot estimate can be plugged in without routing
through a bound containing `log n` in its numerator.
-/

/-- Positive logarithmic upper boundary matched to the prefix entropy. -/
noncomputable def harperPrefixPositiveLogBarrier
    {n : ℕ} (x : ℝ) (k : Fin n) : ℝ :=
  x + 8 * Real.log ((k.val + 2 : ℕ) : ℝ)

/-- Tilted-cube witness event for the positive logarithmic boundary. -/
def harperPrefixGoodPositiveLogWitnessEvent
    (y start n : ℕ) (t x : ℝ) (lower : Fin n → ℝ) :
    Set (HarperPrimeCube y) :=
  (harperScheduledCenteredBlockVectorVarying y start n t
      (harperScheduledVerticalCheckpoint start n t)) ⁻¹'
    harperPartialSumBarrierSet lower (harperPrefixPositiveLogBarrier x)

theorem measurableSet_harperPrefixGoodPositiveLogWitnessEvent
    (y start n : ℕ) (t x : ℝ) (lower : Fin n → ℝ) :
    MeasurableSet
      (harperPrefixGoodPositiveLogWitnessEvent
        y start n t x lower) := by
  unfold harperPrefixGoodPositiveLogWitnessEvent
  exact (measurableSet_harperPartialSumBarrierSet lower
    (harperPrefixPositiveLogBarrier x)).preimage
      (measurable_harperScheduledCenteredBlockVectorVarying
        y start n t (harperScheduledVerticalCheckpoint start n t))

/-- The simultaneous prefix window event forces the positive-log witness
whenever the two displayed deterministic comparisons hold. -/
theorem harperPrefixEnergyWindowGoodSet_subset_positiveLogWitnessEvent
    (y start n M : ℕ) (t x : ℝ)
    (lowerEnergy upperEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (lowerBarrier : Fin n → ℝ)
    (ht : |t| ≤ M)
    (hlowerPos : ∀ k : Fin n,
      0 < lowerEnergy (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k))
    (hlower : ∀ k : Fin n,
      lowerBarrier k +
          harperScheduledVerticalCumulativeDrift y start n t k +
          harperScheduledLogTaylorAllowance start ≤
        Real.log
          (lowerEnergy (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2)
    (hupper : ∀ k : Fin n,
      Real.log
          (upperEnergy (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
        harperPrefixPositiveLogBarrier x k +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start) :
    harperPrefixEnergyWindowGoodSet
        y start n M lowerEnergy upperEnergy ⊆
      harperPrefixGoodPositiveLogWitnessEvent
        y start n t x lowerBarrier := by
  intro eta heta
  have hrelaxed :=
    harperScheduledCenteredBlockVectorVarying_mem_prefixEnergyBarrier_of_good
      y start n M t eta lowerEnergy upperEnergy ht heta hlowerPos
  rw [mem_harperPartialSumBarrierSet] at hrelaxed
  unfold harperPrefixGoodPositiveLogWitnessEvent
  change harperScheduledCenteredBlockVectorVarying y start n t
      (harperScheduledVerticalCheckpoint start n t) eta ∈
    harperPartialSumBarrierSet lowerBarrier
      (harperPrefixPositiveLogBarrier x)
  rw [mem_harperPartialSumBarrierSet]
  intro k
  have hk := hrelaxed k
  constructor
  · unfold harperPrefixEnergyRelaxedLowerBarrier at hk
    linarith [hlower k]
  · unfold harperPrefixEnergyRelaxedUpperBarrier at hk
    linarith [hupper k]

/-- Ambient-sign pullback of the same deterministic containment. -/
theorem harperOmegaPrefixEnergyWindowGoodEvent_subset_preimage_positiveLogWitness
    (y start n M : ℕ) (t x : ℝ)
    (lowerEnergy upperEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (lowerBarrier : Fin n → ℝ)
    (ht : |t| ≤ M)
    (hlowerPos : ∀ k : Fin n,
      0 < lowerEnergy (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k))
    (hlower : ∀ k : Fin n,
      lowerBarrier k +
          harperScheduledVerticalCumulativeDrift y start n t k +
          harperScheduledLogTaylorAllowance start ≤
        Real.log
          (lowerEnergy (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2)
    (hupper : ∀ k : Fin n,
      Real.log
          (upperEnergy (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
        harperPrefixPositiveLogBarrier x k +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start) :
    harperOmegaPrefixEnergyWindowGoodEvent
        y start n M lowerEnergy upperEnergy ⊆
      harperPrimeRestriction y ⁻¹'
        harperPrefixGoodPositiveLogWitnessEvent
          y start n t x lowerBarrier := by
  intro omega homega
  exact harperPrefixEnergyWindowGoodSet_subset_positiveLogWitnessEvent
    y start n M t x lowerEnergy upperEnergy lowerBarrier ht
      hlowerPos hlower hupper homega

/-! ## One-call recursion with a sharp positive-log probability input -/

/-- Complete restricted fractional-moment step for the positive-log witness.
The sole probabilistic premise is the sharp witness estimate `hprob`; all
event containment is instantiated here. -/
theorem integral_harperEulerSetEnergy_rpow_le_of_prefixGoodPositiveLogBridge
    {y : ℕ} (hy : 2 ≤ y)
    {I : Set ℝ} (hI : MeasurableSet I) (hIfinite : volume I ≠ ∞)
    (start n M : ℕ)
    (lowerEnergy upperEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (upperFirstMoment : ℕ → ℝ)
    (inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (x : ℝ) (lowerBarrier : ℝ → Fin n → ℝ)
    (hlowerEnergyPos : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < lowerEnergy m u)
    (hupperEnergyPos : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < upperEnergy m u)
    (hupperMoment : ∀ m, m ∈ Finset.Icc 1 n →
      harperPrefixEulerNormalizer y start m ≤ upperFirstMoment m)
    (hinverseMoment : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        harperPrefixEulerReciprocalFirstMoment y start m u ≤
          inverseFirstMoment m u)
    (htiltUpper : ∀ t ∈ I, |t| ≤ M)
    (hlowerBridge : ∀ t ∈ I, ∀ k : Fin n,
      lowerBarrier t k +
          harperScheduledVerticalCumulativeDrift y start n t k +
          harperScheduledLogTaylorAllowance start ≤
        Real.log
          (lowerEnergy (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2)
    (hupperBridge : ∀ t ∈ I, ∀ k : Fin n,
      Real.log
          (upperEnergy (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
        harperPrefixPositiveLogBarrier x k +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start)
    (H : ℝ) (hH : 0 ≤ H)
    (hprob : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real
          (harperPrefixGoodPositiveLogWitnessEvent
            y start n t x (lowerBarrier t)) ≤ H)
    {q r : ℝ} (hq : 0 < q) (hqr : q < r) (hr1 : r ≤ 1) :
    (∫ omega, harperEulerSetEnergy y I omega ^ q ∂μ) ≤
      (harperExplicitMertensConstant * (volume.real I * H)) ^ q +
        (harperPrefixEnergyWindowFirstMomentBudget start n M
            lowerEnergy upperEnergy upperFirstMoment inverseFirstMoment) ^
            (1 - q / r) *
          (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
            (q / r) := by
  let A : ℝ → Set (HarperPrimeCube y) := fun t ↦
    harperPrefixGoodPositiveLogWitnessEvent
      y start n t x (lowerBarrier t)
  have hcontain : ∀ t ∈ I,
      harperOmegaPrefixEnergyWindowGoodEvent
          y start n M lowerEnergy upperEnergy ⊆
        harperPrimeRestriction y ⁻¹' A t := by
    intro t ht
    have hlowerActual : ∀ k : Fin n,
        0 < lowerEnergy (k.val + 1)
          (harperScheduledVerticalPrefixAt start n t k) := by
      intro k
      apply hlowerEnergyPos (k.val + 1)
      · simp only [Finset.mem_Icc]
        omega
      · exact harperScheduledVerticalPrefixAt_mem_family
          start n M (htiltUpper t ht) k
    exact
      harperOmegaPrefixEnergyWindowGoodEvent_subset_preimage_positiveLogWitness
        y start n M t x lowerEnergy upperEnergy (lowerBarrier t)
          (htiltUpper t ht) hlowerActual
          (hlowerBridge t ht) (hupperBridge t ht)
  have hprobA : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real (A t) ≤ H := by
    intro t ht
    exact hprob t ht
  exact integral_harperEulerSetEnergy_rpow_le_of_prefixGoodEvent
    hy hI hIfinite start n M lowerEnergy upperEnergy upperFirstMoment
      inverseFirstMoment hlowerEnergyPos hupperEnergyPos hupperMoment
      hinverseMoment A H hH hcontain hprobA hq hqr hr1

/-! ## Explicit windows and unconditional arithmetic -/

/-- Fixed centered height used by the positive-log witness after the linear
normalizer and drift cancel. -/
noncomputable def harperExplicitPrefixPositiveLogOffset
    (start M : ℕ) (B E D : ℝ) : ℝ :=
  harperExplicitPrefixEntropyBase start M + B + E / 2 + D +
    harperScheduledLogTaylorAllowance start

/-- Lower barrier paired with the explicit asymmetric lower window and the
uniform upper drift envelope. -/
noncomputable def harperExplicitPrefixPositiveLogLowerBarrier
    (y start n M : ℕ) (B D t : ℝ) (k : Fin n) : ℝ :=
  harperExplicitPrefixLowerBarrier y start n t
    (harperExplicitPrefixEntropyHeight start M B)
    (fun m ↦ (m : ℝ) * Real.log 2 + D) k

/-- Prefix sums over `Fin (k+1)` and over `Iic k` are identical when the
summand depends only on the natural coordinate. -/
theorem sum_fin_prefix_eq_sum_Iic
    {n : ℕ} (f : ℕ → ℝ) (k : Fin n) :
    (∑ i : Fin (k.val + 1), f i.val) =
      ∑ i ∈ Finset.Iic k, f i.val := by
  have h := harperPathPartialSum_eq_sum_prefix
    (v := fun i : Fin n ↦ f i.val) k
  simpa only [harperPathPartialSum, harperPathPrefix] using! h.symm

/-- The explicit prefix windows, their exact first moments, and the sharp
moving-height arithmetic give a complete recursion step.  The only remaining
input is the sharp probability bound for the positive-log witness itself.
In particular, positivity, first-moment, product, drift, mesh, and window
premises no longer appear. -/
theorem
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixPositiveLog
    : ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start → 0 < n →
        harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      (∀ t ∈ I, 1 ≤ |t|) → (∀ t ∈ I, |t| ≤ M) →
      ∀ B H : ℝ, 0 ≤ H →
      (∀ t ∈ I,
        (harperTiltedCubeLaw y t).real
            (harperPrefixGoodPositiveLogWitnessEvent y start n t
              (harperExplicitPrefixPositiveLogOffset start M B E D)
              (harperExplicitPrefixPositiveLogLowerBarrier
                y start n M B D t)) ≤ H) →
      ∀ q r : ℝ, 0 < q → q < r → r ≤ 1 →
        (∫ omega, harperEulerSetEnergy y I omega ^ q ∂μ) ≤
          (harperExplicitMertensConstant * (volume.real I * H)) ^ q +
            Real.exp (-2 * B) ^ (1 - q / r) *
              (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
                (q / r) := by
  obtain ⟨E, hE, D, hD, J, harithmetic⟩ :=
    exists_harperScheduledMovingHeightVerticalCumulativeUniformConstants
  refine ⟨E, hE, D, hD, J, ?_⟩
  intro M start n y hstart hn hyEndpoint hy I hI hIfinite
    htiltLower htiltUpper B H hH hprob q r hq hqr hr1
  let height : ℕ → ℝ := harperExplicitPrefixEntropyHeight start M B
  let lowerEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ :=
    harperExplicitPrefixLowerWindow y start height
  let upperEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ :=
    harperExplicitPrefixUpperWindow y start height
  let lowerBarrier : ℝ → Fin n → ℝ :=
    harperExplicitPrefixPositiveLogLowerBarrier y start n M B D
  let x : ℝ :=
    harperExplicitPrefixPositiveLogOffset start M B E D
  have hbridges : ∀ t ∈ I,
      (∀ k : Fin n,
        lowerBarrier t k +
            harperScheduledVerticalCumulativeDrift y start n t k +
            harperScheduledLogTaylorAllowance start ≤
          Real.log
            (lowerEnergy (k.val + 1)
              (harperScheduledVerticalPrefixAt start n t k)) / 2) ∧
      (∀ k : Fin n,
        Real.log
            (upperEnergy (k.val + 1)
              (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
          harperPrefixPositiveLogBarrier x k +
            harperScheduledVerticalCumulativeDrift y start n t k -
            harperScheduledLogTaylorAllowance start) := by
    intro t ht
    have harith := harithmetic M start n y hstart hyEndpoint t
      (htiltLower t ht) (htiltUpper t ht)
    have hproduct : ∀ k : Fin n,
        Real.log (harperPrefixEulerNormalizer y start (k.val + 1)) ≤
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2 + E := by
      intro k
      apply log_harperPrefixEulerNormalizer_le_of_reciprocal_error
      rw [sum_fin_prefix_eq_sum_Iic
        (fun j ↦ harperScheduledReciprocalMass y (start + j)) k]
      exact (harith k).1
    have hbridge :=
      harperExplicitPrefixWindows_positiveLogBridge_comparisons
        y start n M t B E D hproduct (fun k ↦ (harith k).2)
    simpa only [height, lowerEnergy, upperEnergy, lowerBarrier, x,
      harperExplicitPrefixPositiveLogLowerBarrier,
      harperExplicitPrefixPositiveLogOffset,
      harperPrefixPositiveLogBarrier] using! hbridge
  have hrec :=
    integral_harperEulerSetEnergy_rpow_le_of_prefixGoodPositiveLogBridge
      hy hI hIfinite start n M lowerEnergy upperEnergy
      (harperPrefixEulerNormalizer y start)
      (harperPrefixInverseEulerNormalizer y start) x lowerBarrier
      (fun m hm u hu ↦ harperExplicitPrefixLowerWindow_pos
        y start height m u)
      (fun m hm u hu ↦ harperExplicitPrefixUpperWindow_pos
        y start height m u)
      (fun m hm ↦ le_rfl)
      (fun m hm u hu ↦
        (harperPrefixEulerReciprocalFirstMoment_eq_inverseNormalizer
          y start m u).le)
      htiltUpper
      (fun t ht ↦ (hbridges t ht).1)
      (fun t ht ↦ (hbridges t ht).2)
      H hH (by simpa only [x, lowerBarrier] using! hprob)
      hq hqr hr1
  have hbudget :
      harperPrefixEnergyWindowFirstMomentBudget start n M
          lowerEnergy upperEnergy
          (harperPrefixEulerNormalizer y start)
          (harperPrefixInverseEulerNormalizer y start) ≤
        Real.exp (-2 * B) := by
    simpa only [height, lowerEnergy, upperEnergy] using!
      harperPrefixEnergyWindowFirstMomentBudget_entropyHeight_le
        y start n M B
  have hbudget0 : 0 ≤
      harperPrefixEnergyWindowFirstMomentBudget start n M
        lowerEnergy upperEnergy
        (harperPrefixEulerNormalizer y start)
        (harperPrefixInverseEulerNormalizer y start) := by
    unfold harperPrefixEnergyWindowFirstMomentBudget
    apply Finset.sum_nonneg
    intro m hm
    apply Finset.sum_nonneg
    intro u hu
    exact add_nonneg
      (div_nonneg (harperPrefixEulerNormalizer_pos y start m).le
        (harperExplicitPrefixUpperWindow_pos y start height m u).le)
      (mul_nonneg
        (harperPrefixInverseEulerNormalizer_pos y start m u).le
        (harperExplicitPrefixLowerWindow_pos y start height m u).le)
  have hr : 0 < r := hq.trans hqr
  have halpha : 0 ≤ 1 - q / r := by
    rw [sub_nonneg, div_le_one hr]
    exact hqr.le
  have hbudgetPow := Real.rpow_le_rpow hbudget0 hbudget halpha
  have hmoment0 : 0 ≤
      ∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ := by
    exact integral_nonneg fun omega ↦ Real.rpow_nonneg
      (harperEulerSetEnergy_nonneg (by omega) hI omega) r
  have hmomentPow0 : 0 ≤
      (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^ (q / r) :=
    Real.rpow_nonneg hmoment0 _
  exact hrec.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hbudgetPow hmomentPow0))

/-- Central-shell analogue of the explicit positive-log recursion.  The mesh
uses the fixed band `[-1,1]`, while the sharp arithmetic input is uniform on
the dyadic shell
`2^(-(d+1)) < |t| ≤ 2^(-d)` after the scale shift `J+d`. -/
theorem
    exists_integral_harperEulerSetEnergy_rpow_le_of_explicitPrefixCentralPositiveLog
    : ∃ E ≥ 0, ∃ D ≥ 0, ∃ J : ℕ,
      ∀ d start n y : ℕ,
        J + d ≤ start → 0 < n →
        harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      (∀ t ∈ I, (1 / 2 : ℝ) ^ (d + 1) < |t|) →
      (∀ t ∈ I, |t| ≤ (1 / 2 : ℝ) ^ d) →
      ∀ B H : ℝ, 0 ≤ H →
      (∀ t ∈ I,
        (harperTiltedCubeLaw y t).real
            (harperPrefixGoodPositiveLogWitnessEvent y start n t
              (harperExplicitPrefixPositiveLogOffset start 1 B E D)
              (harperExplicitPrefixPositiveLogLowerBarrier
                y start n 1 B D t)) ≤ H) →
      ∀ q r : ℝ, 0 < q → q < r → r ≤ 1 →
        (∫ omega, harperEulerSetEnergy y I omega ^ q ∂μ) ≤
          (harperExplicitMertensConstant * (volume.real I * H)) ^ q +
            Real.exp (-2 * B) ^ (1 - q / r) *
              (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
                (q / r) := by
  obtain ⟨E, hE, D, hD, J, _hnoncentral, harithmetic⟩ :=
    exists_harperScheduledMovingAndCentralVerticalCumulativeUniformConstants
  refine ⟨E, hE, D, hD, J, ?_⟩
  intro d start n y hstart hn hyEndpoint hy I hI hIfinite
    htiltLower htiltUpper B H hH hprob q r hq hqr hr1
  let height : ℕ → ℝ := harperExplicitPrefixEntropyHeight start 1 B
  let lowerEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ :=
    harperExplicitPrefixLowerWindow y start height
  let upperEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ :=
    harperExplicitPrefixUpperWindow y start height
  let lowerBarrier : ℝ → Fin n → ℝ :=
    harperExplicitPrefixPositiveLogLowerBarrier y start n 1 B D
  let x : ℝ :=
    harperExplicitPrefixPositiveLogOffset start 1 B E D
  have htiltUpperOne : ∀ t ∈ I, |t| ≤ (1 : ℝ) := by
    intro t ht
    exact (htiltUpper t ht).trans
      (show (1 / 2 : ℝ) ^ d ≤ 1 from
        pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have hbridges : ∀ t ∈ I,
      (∀ k : Fin n,
        lowerBarrier t k +
            harperScheduledVerticalCumulativeDrift y start n t k +
            harperScheduledLogTaylorAllowance start ≤
          Real.log
            (lowerEnergy (k.val + 1)
              (harperScheduledVerticalPrefixAt start n t k)) / 2) ∧
      (∀ k : Fin n,
        Real.log
            (upperEnergy (k.val + 1)
              (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
          harperPrefixPositiveLogBarrier x k +
            harperScheduledVerticalCumulativeDrift y start n t k -
            harperScheduledLogTaylorAllowance start) := by
    intro t ht
    have harith := harithmetic d start n y hstart hyEndpoint t
      (htiltLower t ht) (htiltUpper t ht)
    have hproduct : ∀ k : Fin n,
        Real.log (harperPrefixEulerNormalizer y start (k.val + 1)) ≤
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2 + E := by
      intro k
      apply log_harperPrefixEulerNormalizer_le_of_reciprocal_error
      rw [sum_fin_prefix_eq_sum_Iic
        (fun j ↦ harperScheduledReciprocalMass y (start + j)) k]
      exact (harith k).1
    have hbridge :=
      harperExplicitPrefixWindows_positiveLogBridge_comparisons
        y start n 1 t B E D hproduct (fun k ↦ (harith k).2)
    simpa only [height, lowerEnergy, upperEnergy, lowerBarrier, x,
      harperExplicitPrefixPositiveLogLowerBarrier,
      harperExplicitPrefixPositiveLogOffset,
      harperPrefixPositiveLogBarrier] using! hbridge
  have hrec :=
    integral_harperEulerSetEnergy_rpow_le_of_prefixGoodPositiveLogBridge
      hy hI hIfinite start n 1 lowerEnergy upperEnergy
      (harperPrefixEulerNormalizer y start)
      (harperPrefixInverseEulerNormalizer y start) x lowerBarrier
      (fun m hm u hu ↦ harperExplicitPrefixLowerWindow_pos
        y start height m u)
      (fun m hm u hu ↦ harperExplicitPrefixUpperWindow_pos
        y start height m u)
      (fun m hm ↦ le_rfl)
      (fun m hm u hu ↦
        (harperPrefixEulerReciprocalFirstMoment_eq_inverseNormalizer
          y start m u).le)
      (fun t ht ↦ by
        simpa only [Nat.cast_one] using! htiltUpperOne t ht)
      (fun t ht ↦ (hbridges t ht).1)
      (fun t ht ↦ (hbridges t ht).2)
      H hH (by simpa only [x, lowerBarrier] using! hprob)
      hq hqr hr1
  have hbudget :
      harperPrefixEnergyWindowFirstMomentBudget start n 1
          lowerEnergy upperEnergy
          (harperPrefixEulerNormalizer y start)
          (harperPrefixInverseEulerNormalizer y start) ≤
        Real.exp (-2 * B) := by
    simpa only [height, lowerEnergy, upperEnergy] using!
      harperPrefixEnergyWindowFirstMomentBudget_entropyHeight_le
        y start n 1 B
  have hbudget0 : 0 ≤
      harperPrefixEnergyWindowFirstMomentBudget start n 1
        lowerEnergy upperEnergy
        (harperPrefixEulerNormalizer y start)
        (harperPrefixInverseEulerNormalizer y start) := by
    unfold harperPrefixEnergyWindowFirstMomentBudget
    apply Finset.sum_nonneg
    intro m hm
    apply Finset.sum_nonneg
    intro u hu
    exact add_nonneg
      (div_nonneg (harperPrefixEulerNormalizer_pos y start m).le
        (harperExplicitPrefixUpperWindow_pos y start height m u).le)
      (mul_nonneg
        (harperPrefixInverseEulerNormalizer_pos y start m u).le
        (harperExplicitPrefixLowerWindow_pos y start height m u).le)
  have hr : 0 < r := hq.trans hqr
  have halpha : 0 ≤ 1 - q / r := by
    rw [sub_nonneg, div_le_one hr]
    exact hqr.le
  have hbudgetPow := Real.rpow_le_rpow hbudget0 hbudget halpha
  have hmoment0 : 0 ≤
      ∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ := by
    exact integral_nonneg fun omega ↦ Real.rpow_nonneg
      (harperEulerSetEnergy_nonneg (by omega) hI omega) r
  have hmomentPow0 : 0 ≤
      (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^ (q / r) :=
    Real.rpow_nonneg hmoment0 _
  exact hrec.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hbudgetPow hmomentPow0))

end Erdos.Problem520
