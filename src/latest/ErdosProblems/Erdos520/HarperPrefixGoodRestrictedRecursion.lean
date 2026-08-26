import ErdosProblems.Erdos520.HarperGoodEventBarrierBridge
import ErdosProblems.Erdos520.HarperOmegaGoodEvent
import ErdosProblems.Erdos520.HarperTiltedModerateTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem520

/-!
# From the finite prefix good event to the restricted fractional recursion

The deterministic bridge controls a good cube point when its centered path
lies in the moderate coordinate box.  For the first-moment argument we use
one finite-cube witness event: the moderate reverse-log event, union the
complement of that box.  Thus every good cube point belongs to the witness,
without imposing a coordinate cutoff on the good event itself.

The witness probability is the sum of the established moderate-barrier and
moderate-tail bounds.  The final theorem instantiates the exact `hcontain`
and `hprob` interface of `HarperOmegaGoodEvent` and exposes only the prefix
window, drift, and first-moment comparisons still needed from arithmetic.
-/

/-! ## The finite-cube witness event -/

/-- The event used in the restricted first moment: either the centered path
obeys the reverse-log barrier inside the moderate box, or it leaves that box.
The varying evaluation path is the actual scheduled vertical checkpoint. -/
def harperPrefixGoodTiltedWitnessEvent
    (y start n : ℕ) (t x c : ℝ) (lower : Fin n → ℝ) :
    Set (HarperPrimeCube y) :=
  harperTiltedVaryingModerateReverseLogBarrierEvent y start n t
      (harperScheduledVerticalCheckpoint start n t) x c lower ∪
    (harperScheduledCenteredBlockVectorVarying y start n t
      (harperScheduledVerticalCheckpoint start n t)) ⁻¹'
        (harperCoordinateBox
          (harperScheduledModerateRadius start n))ᶜ

theorem measurableSet_harperPrefixGoodTiltedWitnessEvent
    (y start n : ℕ) (t x c : ℝ) (lower : Fin n → ℝ) :
    MeasurableSet
      (harperPrefixGoodTiltedWitnessEvent y start n t x c lower) := by
  exact
    (measurableSet_harperTiltedVaryingModerateReverseLogBarrierEvent
      y start n t (harperScheduledVerticalCheckpoint start n t)
        x c lower).union
      ((measurableSet_harperCoordinateBox
          (harperScheduledModerateRadius start n)).compl.preimage
        (measurable_harperScheduledCenteredBlockVectorVarying y start n t
          (harperScheduledVerticalCheckpoint start n t)))

/-- The finite-cube containment required by the tilted first moment.  The
arithmetic comparisons between energy windows, drift, Taylor allowance, and
the target barriers remain explicit. -/
theorem harperPrefixEnergyWindowGoodSet_subset_tiltedWitnessEvent
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
        y start n M lowerEnergy upperEnergy ⊆
      harperPrefixGoodTiltedWitnessEvent y start n t x c lowerBarrier := by
  intro eta heta
  let path := harperScheduledCenteredBlockVectorVarying y start n t
    (harperScheduledVerticalCheckpoint start n t)
  let box := harperCoordinateBox (harperScheduledModerateRadius start n)
  by_cases hbox : path eta ∈ box
  · apply Or.inl
    exact
      inter_harperPrefixGood_moderateBox_subset_tiltedVaryingEvent
        y start n M t x c lowerEnergy upperEnergy lowerBarrier ht
          hlowerPos hlower hupper ⟨heta, hbox⟩
  · apply Or.inr
    exact hbox

/-- The same containment after pulling the good event back to the ambient
sign space.  This has exactly the shape of the `hcontain` argument consumed
by `integral_harperEulerSetEnergy_rpow_le_of_prefixGoodEvent`. -/
theorem harperOmegaPrefixEnergyWindowGoodEvent_subset_preimage_tiltedWitness
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
    harperOmegaPrefixEnergyWindowGoodEvent
        y start n M lowerEnergy upperEnergy ⊆
      harperPrimeRestriction y ⁻¹'
        harperPrefixGoodTiltedWitnessEvent y start n t x c lowerBarrier := by
  intro omega homega
  exact harperPrefixEnergyWindowGoodSet_subset_tiltedWitnessEvent
    y start n M t x c lowerEnergy upperEnergy lowerBarrier ht
      hlowerPos hlower hupper homega

/-! ## Uniform tilted probability of the witness -/

/-- The explicit uniform witness-probability bound. -/
noncomputable def harperPrefixGoodTiltedWitnessProbabilityBound
    (start n : ℕ) (x : ℝ) : ℝ :=
  Real.exp 2 * (64 * (x + 4) / Real.sqrt (n : ℝ)) +
    64 * (1 / 2 : ℝ) ^ start

/-- Eventually in the starting scale, the witness event has the same bound
as the unrestricted reverse-log estimate.  The checkpoint scale condition
is discharged by the scheduled vertical mesh. -/
theorem exists_eventually_harperPrefixGoodTiltedWitness_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x c : ℝ,
          0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
            (harperTiltedCubeLaw y t).real
                (harperPrefixGoodTiltedWitnessEvent
                  y start n t x c lower) ≤
              harperPrefixGoodTiltedWitnessProbabilityBound start n x := by
  obtain ⟨Jbarrier, hJbarrier⟩ :=
    exists_eventually_harperTiltedCubeVaryingModerateReverseLogBarrier_probability_le M
  obtain ⟨Jtail, hJtail⟩ :=
    exists_eventually_harperTiltedCubeVaryingModerateBox_compl_probability_le M
  refine ⟨max Jbarrier Jtail, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x c hx hc lower
  have hstartBarrier : Jbarrier ≤ start :=
    (le_max_left Jbarrier Jtail).trans hstart
  have hstartTail : Jtail ≤ start :=
    (le_max_right Jbarrier Jtail).trans hstart
  have hscale : ∀ i : Fin n,
      |harperScheduledVerticalCheckpoint start n t i - t| *
          Real.log (harperBlockEndpoint
            (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ) :=
    harperScheduledVerticalCheckpoint_offDiagonalCondition start n t
  unfold harperPrefixGoodTiltedWitnessEvent
    harperPrefixGoodTiltedWitnessProbabilityBound
  exact (measureReal_union_le _ _).trans (add_le_add
    (hJbarrier start hstartBarrier n hn y hy t htLower htUpper
      (harperScheduledVerticalCheckpoint start n t) hscale
        x c hx hc lower)
    (hJtail start hstartTail n y hy t htLower htUpper
      (harperScheduledVerticalCheckpoint start n t) hscale))

/-! ## One-call restricted fractional recursion -/

/-- Eventually in the starting scale, the prefix energy windows and their
explicit drift comparisons imply one complete restricted fractional-moment
recursion step on an arbitrary measurable vertical set of finite volume.

There is no residual event parameter: the witness event, its containment,
and its tilted probability estimate are all instantiated internally. -/
theorem exists_eventually_integral_harperEulerSetEnergy_rpow_le_of_prefixGoodBridge
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y → 2 ≤ y →
      ∀ I : Set ℝ, MeasurableSet I → volume I ≠ ∞ →
      ∀ x c : ℝ, 0 ≤ x → 0 ≤ c →
      ∀ lowerEnergy upperEnergy :
          (m : ℕ) → (Fin m → ℝ) → ℝ,
      ∀ upperFirstMoment : ℕ → ℝ,
      ∀ inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ,
      ∀ lowerBarrier : ℝ → Fin n → ℝ,
      (∀ m, m ∈ Finset.Icc 1 n →
        ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
          0 < lowerEnergy m u) →
      (∀ m, m ∈ Finset.Icc 1 n →
        ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
          0 < upperEnergy m u) →
      (∀ m, m ∈ Finset.Icc 1 n →
        harperPrefixEulerNormalizer y start m ≤ upperFirstMoment m) →
      (∀ m, m ∈ Finset.Icc 1 n →
        ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
          harperPrefixEulerReciprocalFirstMoment y start m u ≤
            inverseFirstMoment m u) →
      (∀ t ∈ I, 1 ≤ |t|) →
      (∀ t ∈ I, |t| ≤ M) →
      (∀ t ∈ I, ∀ k : Fin n,
        lowerBarrier t k +
            harperScheduledVerticalCumulativeDrift y start n t k +
            harperScheduledLogTaylorAllowance start ≤
          Real.log
            (lowerEnergy (k.val + 1)
              (harperScheduledVerticalPrefixAt start n t k)) / 2) →
      (∀ t ∈ I, ∀ k : Fin n,
        Real.log
            (upperEnergy (k.val + 1)
              (harperScheduledVerticalPrefixAt start n t k)) / 2 ≤
          harperNormalizedReverseLogBarrier n x c k +
            harperScheduledVerticalCumulativeDrift y start n t k -
            harperScheduledLogTaylorAllowance start) →
      ∀ q r : ℝ, 0 < q → q < r → r ≤ 1 →
        (∫ omega, harperEulerSetEnergy y I omega ^ q ∂μ) ≤
          (harperExplicitMertensConstant *
              (volume.real I *
                harperPrefixGoodTiltedWitnessProbabilityBound
                  start n x)) ^ q +
            (harperPrefixEnergyWindowFirstMomentBudget start n M
                lowerEnergy upperEnergy upperFirstMoment
                  inverseFirstMoment) ^ (1 - q / r) *
              (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
                (q / r) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperPrefixGoodTiltedWitness_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hyEndpoint hy I hI hIfinite x c hx hc
    lowerEnergy upperEnergy upperFirstMoment inverseFirstMoment lowerBarrier
    hlowerEnergyPos hupperEnergyPos hupperMoment hinverseMoment
    htiltLower htiltUpper hlowerBridge hupperBridge q r hq hqr hr1
  let A : ℝ → Set (HarperPrimeCube y) := fun t ↦
    harperPrefixGoodTiltedWitnessEvent
      y start n t x c (lowerBarrier t)
  let H : ℝ :=
    harperPrefixGoodTiltedWitnessProbabilityBound start n x
  have hH : 0 ≤ H := by
    unfold H harperPrefixGoodTiltedWitnessProbabilityBound
    positivity
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
    exact harperOmegaPrefixEnergyWindowGoodEvent_subset_preimage_tiltedWitness
      y start n M t x c lowerEnergy upperEnergy (lowerBarrier t)
        (htiltUpper t ht) hlowerActual (hlowerBridge t ht)
          (hupperBridge t ht)
  have hprob : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real (A t) ≤ H := by
    intro t ht
    simpa only [A, H] using!
      hJ start hstart n hn y hyEndpoint t (htiltLower t ht)
        (htiltUpper t ht) x c hx hc (lowerBarrier t)
  simpa only [H] using!
    integral_harperEulerSetEnergy_rpow_le_of_prefixGoodEvent
      hy hI hIfinite start n M lowerEnergy upperEnergy upperFirstMoment
        inverseFirstMoment hlowerEnergyPos hupperEnergyPos hupperMoment
          hinverseMoment A H hH hcontain hprob hq hqr hr1

end Erdos.Problem520
