import ErdosProblems.Erdos520.HarperPrefixGoodEvent
import ErdosProblems.Erdos520.HarperTiltedVaryingBarrier

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Erdos.Problem520

/-!
# From prefix Euler-energy windows to the centered reverse-log barrier

The finite prefix good event is multiplicative: it bounds every scheduled
prefix Euler energy at every relevant vertical checkpoint.  The tilted
barrier estimate is additive: it bounds partial sums of centered linear
block increments.  This file gives the deterministic conversion.

The logarithm of a prefix energy is exactly twice its true logarithmic path
sum.  `HarperVaryingLogPath` then compares that true path with the centered
path plus its cumulative deterministic drift, with one start-scale Taylor
remainder.  The final API leaves the comparisons between the chosen energy
windows, cumulative drift, and target barriers as explicit hypotheses.
-/

/-! ## Prefix products are path partial sums -/

/-- A partial sum through `k` is the sum of the restriction to the first
`k+1` coordinates. -/
theorem harperPathPartialSum_eq_sum_prefix
    {n : ℕ} (v : Fin n → ℝ) (k : Fin n) :
    harperPathPartialSum v k =
      ∑ i : Fin (k.val + 1),
        harperPathPrefix (show k.val + 1 ≤ n by omega) v i := by
  let toPrefix : {i : Fin n // i ∈ Finset.Iic k} → Fin (k.val + 1) := fun i ↦
    ⟨i.1.val, by
      have hi : i.1 ≤ k := Finset.mem_Iic.mp i.2
      omega⟩
  let fromPrefix : Fin (k.val + 1) → {i : Fin n // i ∈ Finset.Iic k} := fun j ↦
    ⟨⟨j.val, by omega⟩, by
      rw [Finset.mem_Iic]
      exact Fin.mk_le_mk.mpr (by omega)⟩
  let e : {i : Fin n // i ∈ Finset.Iic k} ≃ Fin (k.val + 1) :=
    ⟨toPrefix, fromPrefix, by
      intro i
      apply Subtype.ext
      apply Fin.ext
      rfl, by
      intro j
      apply Fin.ext
      rfl⟩
  unfold harperPathPartialSum
  calc
    (∑ i ∈ Finset.Iic k, v i) =
        ∑ i : {i : Fin n // i ∈ Finset.Iic k}, v i :=
      (Finset.sum_coe_sort (Finset.Iic k) v).symm
    _ = ∑ i : Fin (k.val + 1),
        harperPathPrefix (show k.val + 1 ≤ n by omega) v i := by
      apply Fintype.sum_equiv e
      intro i
      rfl

/-- The logarithm of the varying-height prefix energy is exactly twice the
corresponding partial sum of the full true logarithmic path. -/
theorem log_harperPrefixScheduledVaryingEulerEnergy_eq_two_mul_partialSum
    (y start n : ℕ) (u : Fin n → ℝ) (eta : HarperPrimeCube y)
    (k : Fin n) :
    Real.log
        (harperPrefixScheduledVaryingEulerEnergy y start (k.val + 1)
          (harperPathPrefix (show k.val + 1 ≤ n by omega) u) eta) =
      2 * harperPathPartialSum
        (harperScheduledLogBlockVectorVarying y start n u eta) k := by
  rw [harperPrefixScheduledVaryingEulerEnergy,
    log_harperScheduledVaryingEulerEnergy_eq_two_mul_sum_logBlockVector]
  congr 1
  rw [harperPathPartialSum_eq_sum_prefix]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-! ## The actual scheduled vertical prefixes -/

/-- The vertical prefix attached to the checkpoint through coordinate `k`. -/
noncomputable def harperScheduledVerticalPrefixAt
    (start n : ℕ) (t : ℝ) (k : Fin n) : Fin (k.val + 1) → ℝ :=
  harperScheduledVerticalPrefixPath start n (k.val + 1) t

theorem harperScheduledVerticalPrefixAt_eq_pathPrefix
    (start n : ℕ) (t : ℝ) (k : Fin n) :
    harperScheduledVerticalPrefixAt start n t k =
      harperPathPrefix (show k.val + 1 ≤ n by omega)
        (harperScheduledVerticalCheckpoint start n t) := by
  symm
  exact harperPathPrefix_scheduledVerticalCheckpoint
    start n (k.val + 1) (by omega) t

theorem harperScheduledVerticalPrefixAt_mem_family
    (start n M : ℕ) {t : ℝ} (ht : |t| ≤ M) (k : Fin n) :
    harperScheduledVerticalPrefixAt start n t k ∈
      harperScheduledVerticalPrefixFamily start n (k.val + 1) M := by
  exact harperScheduledVerticalPrefixPath_mem_family
    start n (k.val + 1) M (by omega) ht

/-! ## Drift, Taylor allowance, and the barriers supplied by energy windows -/

/-- Deterministic tilted drift accumulated through the checkpoint `k`, along
the actual scheduled vertical path. -/
noncomputable def harperScheduledVerticalCumulativeDrift
    (y start n : ℕ) (t : ℝ) (k : Fin n) : ℝ :=
  ∑ i ∈ Finset.Iic k,
    harperScheduledMainMeanVectorVarying y start n t
      (harperScheduledVerticalCheckpoint start n t) i

/-- The uniform cubic Taylor allowance for every prefix of a scheduled path. -/
noncomputable def harperScheduledLogTaylorAllowance (start : ℕ) : ℝ :=
  (4 / 3 : ℝ) *
    (Real.sqrt (harperBlockEndpoint start : ℝ))⁻¹

/-- Lower centered partial-sum barrier furnished by a lower prefix-energy
window after subtracting drift and the Taylor allowance. -/
noncomputable def harperPrefixEnergyRelaxedLowerBarrier
    (y start n : ℕ) (t : ℝ)
    (lower : (m : ℕ) → (Fin m → ℝ) → ℝ) (k : Fin n) : ℝ :=
  Real.log
      (lower (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k)) / 2 -
    harperScheduledVerticalCumulativeDrift y start n t k -
    harperScheduledLogTaylorAllowance start

/-- Upper centered partial-sum barrier furnished by an upper prefix-energy
window after subtracting drift and adding the Taylor allowance. -/
noncomputable def harperPrefixEnergyRelaxedUpperBarrier
    (y start n : ℕ) (t : ℝ)
    (upper : (m : ℕ) → (Fin m → ℝ) → ℝ) (k : Fin n) : ℝ :=
  Real.log
      (upper (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k)) / 2 -
    harperScheduledVerticalCumulativeDrift y start n t k +
    harperScheduledLogTaylorAllowance start

/-! ## The deterministic good-event-to-barrier bridge -/

/-- Membership in the simultaneous prefix-energy good event forces the
centered varying-height path between the two relaxed logarithmic barriers.

Only positivity of the lower window is an extra hypothesis.  The Euler
energy itself is strictly positive, and the good event consequently makes
the upper endpoint positive whenever needed. -/
theorem harperScheduledCenteredBlockVectorVarying_mem_prefixEnergyBarrier_of_good
    (y start n M : ℕ) (t : ℝ) (eta : HarperPrimeCube y)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (ht : |t| ≤ M)
    (hgood : eta ∈
      harperPrefixEnergyWindowGoodSet y start n M lower upper)
    (hlowerPos : ∀ k : Fin n,
      0 < lower (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k)) :
    harperScheduledCenteredBlockVectorVarying y start n t
        (harperScheduledVerticalCheckpoint start n t) eta ∈
      harperPartialSumBarrierSet
        (harperPrefixEnergyRelaxedLowerBarrier y start n t lower)
        (harperPrefixEnergyRelaxedUpperBarrier y start n t upper) := by
  rw [mem_harperPartialSumBarrierSet]
  intro k
  have hm : k.val + 1 ∈ Finset.Icc 1 n := by
    simp only [Finset.mem_Icc]
    omega
  have hprefix : harperScheduledVerticalPrefixAt start n t k ∈
      harperScheduledVerticalPrefixFamily start n (k.val + 1) M :=
    harperScheduledVerticalPrefixAt_mem_family start n M ht k
  have hwindow :=
    (mem_harperPrefixEnergyWindowGoodSet
      y start n M lower upper eta).mp hgood
      (k.val + 1) hm
      (harperScheduledVerticalPrefixAt start n t k) hprefix
  have henergyPos : 0 <
      harperPrefixScheduledVaryingEulerEnergy y start (k.val + 1)
        (harperScheduledVerticalPrefixAt start n t k) eta :=
    harperPrefixScheduledVaryingEulerEnergy_pos y start (k.val + 1)
      (harperScheduledVerticalPrefixAt start n t k) eta
  have hlogLower :
      Real.log
          (lower (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) ≤
        Real.log
          (harperPrefixScheduledVaryingEulerEnergy y start (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k) eta) :=
    Real.log_le_log (hlowerPos k) hwindow.1
  have hlogUpper :
      Real.log
          (harperPrefixScheduledVaryingEulerEnergy y start (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k) eta) ≤
        Real.log
          (upper (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k)) :=
    Real.log_le_log henergyPos hwindow.2
  have hlogEnergy :
      Real.log
          (harperPrefixScheduledVaryingEulerEnergy y start (k.val + 1)
            (harperScheduledVerticalPrefixAt start n t k) eta) =
        2 * harperPathPartialSum
          (harperScheduledLogBlockVectorVarying y start n
            (harperScheduledVerticalCheckpoint start n t) eta) k := by
    rw [harperScheduledVerticalPrefixAt_eq_pathPrefix]
    exact
      log_harperPrefixScheduledVaryingEulerEnergy_eq_two_mul_partialSum
        y start n (harperScheduledVerticalCheckpoint start n t) eta k
  rw [hlogEnergy] at hlogLower hlogUpper
  have hTaylor :=
    abs_harperScheduledLogPathPartialSum_sub_centered_add_mean_le
      y start n t (harperScheduledVerticalCheckpoint start n t) eta k
  change
    |harperPathPartialSum
        (harperScheduledLogBlockVectorVarying y start n
          (harperScheduledVerticalCheckpoint start n t) eta) k -
      (harperPathPartialSum
          (harperScheduledCenteredBlockVectorVarying y start n t
            (harperScheduledVerticalCheckpoint start n t) eta) k +
        harperScheduledVerticalCumulativeDrift y start n t k)| ≤
      harperScheduledLogTaylorAllowance start at hTaylor
  have hTaylorLower := neg_le_of_abs_le hTaylor
  have hTaylorUpper := le_of_abs_le hTaylor
  constructor
  · unfold harperPrefixEnergyRelaxedLowerBarrier
    linarith
  · unfold harperPrefixEnergyRelaxedUpperBarrier
    linarith

/-- A directly consumable version of the bridge.  The two displayed
hypotheses are precisely the remaining analytic comparisons: they compare
the chosen prefix-energy windows, cumulative tilted drift, and the desired
barriers.  No probabilistic or mesh argument is hidden in them. -/
theorem harperScheduledCenteredBlockVectorVarying_mem_barrier_of_prefixGood
    (y start n M : ℕ) (t x c : ℝ) (eta : HarperPrimeCube y)
    (lowerEnergy upperEnergy : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (lowerBarrier : Fin n → ℝ)
    (ht : |t| ≤ M)
    (hgood : eta ∈ harperPrefixEnergyWindowGoodSet
      y start n M lowerEnergy upperEnergy)
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
        harperNormalizedReverseLogBarrier n x c k +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start) :
    harperScheduledCenteredBlockVectorVarying y start n t
        (harperScheduledVerticalCheckpoint start n t) eta ∈
      harperPartialSumBarrierSet lowerBarrier
        (harperNormalizedReverseLogBarrier n x c) := by
  have hrelaxed :=
    harperScheduledCenteredBlockVectorVarying_mem_prefixEnergyBarrier_of_good
      y start n M t eta lowerEnergy upperEnergy ht hgood hlowerPos
  rw [mem_harperPartialSumBarrierSet] at hrelaxed ⊢
  intro k
  have hk := hrelaxed k
  constructor
  · unfold harperPrefixEnergyRelaxedLowerBarrier at hk
    linarith [hlower k]
  · unfold harperPrefixEnergyRelaxedUpperBarrier at hk
    linarith [hupper k]

/-- After intersecting with the literal moderate-coordinate box, the prefix
good event is contained in the tilted varying-height event used by the
restricted first-moment estimate. -/
theorem inter_harperPrefixGood_moderateBox_subset_tiltedVaryingEvent
    (y start n M : ℕ) (t x c : ℝ)
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
        harperNormalizedReverseLogBarrier n x c k +
          harperScheduledVerticalCumulativeDrift y start n t k -
          harperScheduledLogTaylorAllowance start) :
    harperPrefixEnergyWindowGoodSet
          y start n M lowerEnergy upperEnergy ∩
        (harperScheduledCenteredBlockVectorVarying y start n t
          (harperScheduledVerticalCheckpoint start n t)) ⁻¹'
            harperCoordinateBox (harperScheduledModerateRadius start n) ⊆
      harperTiltedVaryingModerateReverseLogBarrierEvent y start n t
        (harperScheduledVerticalCheckpoint start n t) x c lowerBarrier := by
  intro eta heta
  unfold harperTiltedVaryingModerateReverseLogBarrierEvent
  exact ⟨harperScheduledCenteredBlockVectorVarying_mem_barrier_of_prefixGood
    y start n M t x c eta lowerEnergy upperEnergy lowerBarrier ht heta.1
      hlowerPos hlower hupper, heta.2⟩

end Erdos.Problem520
