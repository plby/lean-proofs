import ErdosProblems.Erdos520.HarperScheduledOffDiagonalBarrier
import ErdosProblems.Erdos520.HarperVaryingLogPath

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Measure ProbabilityTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Tilted-cube law of the varying-height block path

Disjoint scheduled prime blocks remain independent when each block is
evaluated at its own height.  This identifies the exact pushforward of the
tilted prime-cube law and transports the off-diagonal reverse-log barrier
estimate back to a literal tilted-cube event.
-/

/-- Centered sums over disjoint scheduled blocks are mutually independent
even when the evaluation height varies with the block. -/
theorem iIndepFun_harperScheduledCenteredBlockSumsVarying
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ) :
    iIndepFun
      (fun i : Fin n ↦
        harperCenteredLinearPrimeBlockSum y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i))
      (harperTiltedCubeLaw y t) := by
  let κ : Fin n → Type := fun i ↦
    {p : HarperPrimeIndex y //
      p ∈ harperScheduledPrimeBlock y (start + (i : ℕ))}
  let embed : (p : (i : Fin n) × κ i) → HarperPrimeIndex y :=
    fun p ↦ p.2.1
  have hblocks : Pairwise fun i j : Fin n ↦
      Disjoint
        (harperScheduledPrimeBlock y (start + (i : ℕ)))
        (harperScheduledPrimeBlock y (start + (j : ℕ))) := by
    intro i j hij
    apply disjoint_harperScheduledPrimeBlock y
    intro hs
    apply hij
    apply Fin.ext
    omega
  have hembed : Function.Injective embed := by
    rintro ⟨i, p⟩ ⟨j, q⟩ hpq
    change p.1 = q.1 at hpq
    by_cases hij : i = j
    · subst j
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext hpq))
    · exfalso
      apply (Finset.disjoint_left.mp (hblocks hij)) p.2
      rw [hpq]
      exact q.2
  have hflat : iIndepFun
      (fun p : (i : Fin n) × κ i ↦
        fun eta : HarperPrimeCube y ↦ eta (embed p))
      (harperTiltedCubeLaw y t) :=
    iIndepFun.precomp hembed
      (iIndepFun_harperTiltedCube_coordinates y t)
  have hgroup : iIndepFun
      (fun i : Fin n ↦ fun eta : HarperPrimeCube y ↦
        fun p : κ i ↦ eta p.1)
      (harperTiltedCubeLaw y t) := by
    simpa only [embed] using!
      iIndepFun_piCurry_of_iIndepFun
        (fun p : (i : Fin n) × κ i ↦
          fun eta : HarperPrimeCube y ↦ eta (embed p))
        (fun _p ↦ measurable_of_finite _) hflat
  let blockSum : (i : Fin n) → (κ i → Bool) → ℝ :=
    fun i z ↦ ∑ p : κ i,
      harperCenteredLinearPrimeIncrement p.1.1 t (u i) (z p)
  have hsum := hgroup.comp blockSum
    (fun _i ↦ measurable_of_finite _)
  apply hsum.congr
  intro i
  exact ae_of_all (harperTiltedCubeLaw y t) fun eta ↦ by
    change blockSum i (fun p : κ i ↦ eta p.1) =
      harperCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i) eta
    unfold blockSum harperCenteredLinearPrimeBlockSum
    exact Finset.sum_coe_sort
      (harperScheduledPrimeBlock y (start + (i : ℕ)))
      (fun p ↦ harperCenteredLinearPrimeIncrement p.1 t (u i) (eta p))

/-- Exact pushforward law of the varying-height centered block vector. -/
theorem map_harperScheduledCenteredBlockVectorVarying_eq_pi
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ) :
    Measure.map
        (harperScheduledCenteredBlockVectorVarying y start n t u)
        (harperTiltedCubeLaw y t) =
      Measure.pi (fun i : Fin n ↦
        harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)) := by
  have hmeas : ∀ i : Fin n, Measurable
      (harperCenteredLinearPrimeBlockSum y
        (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)) :=
    fun _i ↦ measurable_of_finite _
  have h := (iIndepFun_iff_map_fun_eq_pi_map
    (fun i ↦ (hmeas i).aemeasurable)).mp
      (iIndepFun_harperScheduledCenteredBlockSumsVarying
        y start n t u)
  simpa only [harperScheduledCenteredBlockVectorVarying,
    harperCenteredLinearBlockLaw] using! h

theorem measurable_harperScheduledCenteredBlockVectorVarying
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ) :
    Measurable
      (harperScheduledCenteredBlockVectorVarying y start n t u) := by
  exact measurable_of_finite _

/-- Measurability of the two-sided finite partial-sum barrier. -/
theorem measurableSet_harperPartialSumBarrierSet
    {n : ℕ} (lower upper : Fin n → ℝ) :
    MeasurableSet (harperPartialSumBarrierSet lower upper) := by
  have hsum (k : Fin n) : Measurable
      (fun omega : Fin n → ℝ ↦ harperPathPartialSum omega k) := by
    unfold harperPathPartialSum
    exact Finset.measurable_sum _ fun i _hi ↦ measurable_pi_apply i
  rw [show harperPartialSumBarrierSet lower upper =
      ⋂ k : Fin n,
        {omega : Fin n → ℝ |
          lower k ≤ harperPathPartialSum omega k ∧
            harperPathPartialSum omega k ≤ upper k} by
    ext omega
    simp only [mem_harperPartialSumBarrierSet, mem_iInter, mem_setOf_eq]]
  exact MeasurableSet.iInter fun k ↦
    (measurableSet_le measurable_const (hsum k)).inter
      (measurableSet_le (hsum k) measurable_const)

/-- Any measurable path event can be evaluated exactly either under the
tilted cube or under the product of its varying-height block marginals. -/
theorem harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (harperTiltedCubeLaw y t).real
        ((harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹' A) =
      (Measure.pi (fun i : Fin n ↦
        harperCenteredLinearBlockLaw y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i))).real A := by
  have hmap := map_measureReal_apply
    (μ := harperTiltedCubeLaw y t)
    (measurable_harperScheduledCenteredBlockVectorVarying
      y start n t u) hA
  rw [map_harperScheduledCenteredBlockVectorVarying_eq_pi] at hmap
  exact hmap.symm

/-- Literal tilted-cube event corresponding to a centered varying-height
path in the moderate box and below the normalized reverse-log barrier. -/
def harperTiltedVaryingModerateReverseLogBarrierEvent
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ)
    (x c : ℝ) (lower : Fin n → ℝ) : Set (HarperPrimeCube y) :=
  (harperScheduledCenteredBlockVectorVarying y start n t u) ⁻¹'
    (harperPartialSumBarrierSet lower
        (harperNormalizedReverseLogBarrier n x c) ∩
      harperCoordinateBox (harperScheduledModerateRadius start n))

theorem measurableSet_harperTiltedVaryingModerateReverseLogBarrierEvent
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ)
    (x c : ℝ) (lower : Fin n → ℝ) :
    MeasurableSet
      (harperTiltedVaryingModerateReverseLogBarrierEvent
        y start n t u x c lower) := by
  unfold harperTiltedVaryingModerateReverseLogBarrierEvent
  exact ((measurableSet_harperPartialSumBarrierSet lower
    (harperNormalizedReverseLogBarrier n x c)).inter
      (measurableSet_harperCoordinateBox
        (harperScheduledModerateRadius start n))).preimage
          (measurable_harperScheduledCenteredBlockVectorVarying
            y start n t u)

/-- Literal tilted-event probability endpoint consumed by the restricted
first moment: the varying-height centered path, restricted to the moderate
box and a normalized reverse-log barrier, has probability
`exp 2 * 64 (x+4) / sqrt n`. -/
theorem exists_eventually_harperTiltedCubeVaryingModerateReverseLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
              (harperTiltedCubeLaw y t).real
                  (harperTiltedVaryingModerateReverseLogBarrierEvent
                    y start n t u x c lower) ≤
                Real.exp 2 *
                  (64 * (x + 4) / Real.sqrt (n : ℝ)) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalModerateBoxReverseLogBarrier_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower
  have heq :=
    harperTiltedCubeLaw_real_preimage_centeredBlockVectorVarying_eq_pi
      y start n t u
      (harperPartialSumBarrierSet lower
          (harperNormalizedReverseLogBarrier n x c) ∩
        harperCoordinateBox (harperScheduledModerateRadius start n))
      ((measurableSet_harperPartialSumBarrierSet lower
        (harperNormalizedReverseLogBarrier n x c)).inter
          (measurableSet_harperCoordinateBox
            (harperScheduledModerateRadius start n)))
  rw [harperTiltedVaryingModerateReverseLogBarrierEvent, heq]
  exact hJ start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower

end Problem520
end Erdos
