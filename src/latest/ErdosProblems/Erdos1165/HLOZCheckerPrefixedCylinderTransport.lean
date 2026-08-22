/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.CappedCoordinateMassCertificate
import ErdosProblems.Erdos1165.StrongMarkovFullTail
import ErdosProblems.Erdos1165.WalkOneStepShift

/-!
# The fixed first-step factor in checker recentering

A shifted checker stopped fibre contains a physical one-step prefix.  Deleting
that prefix and recentering produces the even target fibre, but fixing the
deleted direction costs exactly `1 / 4`.  This file records the corresponding
full-tail identity.  In a conditional broad/narrow ratio the same factor is
present in numerator and denominator, so it cancels exactly.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.HLOZCheckerPrefixedCylinderTransport

open CappedCoordinateMassCertificate

noncomputable section

/-- The cylinder fixing the first increment of the increment path. -/
def firstDirectionSteps (d : Direction) : Set StepPath :=
  {omega | omega 0 = d}

/-- The corresponding cylinder on walk paths. -/
def firstDirectionWalk (d : Direction) : Set WalkPath :=
  {s | s 1 = directionVector d}

/-- Pull a target event back by checker recentering while retaining the
physical first-step cylinder. -/
def checkerPrefixedPreimage (d : Direction) (A : Set WalkPath) : Set WalkPath :=
  firstDirectionWalk d ∩ oneStepRecenter ⁻¹' A

theorem measurableSet_firstDirectionWalk (d : Direction) :
    MeasurableSet (firstDirectionWalk d) := by
  exact measurableSet_eq_fun (measurable_pi_apply 1) measurable_const

theorem measurableSet_checkerPrefixedPreimage
    {A : Set WalkPath} (hA : MeasurableSet A) (d : Direction) :
    MeasurableSet (checkerPrefixedPreimage d A) :=
  (measurableSet_firstDirectionWalk d).inter
    (hA.preimage measurable_oneStepRecenter)

private theorem isMeasurableAtWithTopStopping_firstDirection
    (d : Direction) :
    IsMeasurableAtWithTopStopping (fun _ : StepPath => (1 : WithTop Nat))
      (firstDirectionSteps d) := by
  intro n
  by_cases hn : n = 1
  · subst n
    rw [incrementFiltration_apply]
    refine ⟨{u : Fin 1 → Direction | u 0 = d},
      (Set.to_countable _).measurableSet, ?_⟩
    ext omega
    simp [firstDirectionSteps, stepPrefix]
  · have hempty : firstDirectionSteps d ∩
        {omega | (1 : WithTop Nat) = (n : WithTop Nat)} = ∅ := by
      ext omega
      constructor
      · rintro ⟨_homega, hcoe⟩
        exact (hn (WithTop.coe_eq_coe.mp hcoe.symm)).elim
      · intro h
        exact h.elim
    rw [hempty]
    exact (incrementFiltration n).measurableSet_empty

theorem fairSteps_firstDirectionSteps (d : Direction) :
    fairSteps (firstDirectionSteps d) = 1 / 4 := by
  change fairSteps ((fun omega : StepPath => omega 0) ⁻¹' {d}) = 1 / 4
  rw [← Measure.map_apply (measurable_pi_apply 0) (MeasurableSet.singleton d),
    fairSteps_eval, fairStep_singleton]

/-- A fixed physical first increment is independent of an arbitrary
measurable full tail. -/
theorem fairSteps_firstDirection_inter_shiftSteps_preimage
    (d : Direction) {A : Set StepPath} (hA : MeasurableSet A) :
    fairSteps (firstDirectionSteps d ∩ shiftSteps 1 ⁻¹' A) =
      (1 / 4 : ENNReal) * fairSteps A := by
  have hmarkov := strongMarkov_withTop_fullTail_finiteEvent
    (isStoppingTime_const incrementFiltration 1)
    (isMeasurableAtWithTopStopping_firstDirection d) hA
  change fairSteps
      ((firstDirectionSteps d ∩ {omega | (1 : WithTop Nat) < ⊤}) ∩
        shiftSteps 1 ⁻¹' A) =
    fairSteps (firstDirectionSteps d ∩
      {omega | (1 : WithTop Nat) < ⊤}) * fairSteps A at hmarkov
  have hfinite : firstDirectionSteps d ∩
      {omega | (1 : WithTop Nat) < ⊤} = firstDirectionSteps d := by
    ext omega
    simp
  rw [hfinite, fairSteps_firstDirectionSteps] at hmarkov
  exact hmarkov

theorem trajectory_preimage_firstDirectionWalk (d : Direction) :
    trajectory ⁻¹' firstDirectionWalk d = firstDirectionSteps d := by
  ext omega
  simp only [Set.mem_preimage, firstDirectionWalk, Set.mem_ofPred_eq,
    firstDirectionSteps]
  rw [show (1 : Nat) = 0 + 1 by omega, trajectory_succ, trajectory_zero]
  have hzero : (0, 0) + directionVector (omega 0) =
      directionVector (omega 0) := by
    ext <;> simp
  rw [hzero]
  exact directionVector_injective.eq_iff

/-- The exact fixed-prefix version of checker recentering.  Unlike the
unconditional law-preserving pullback, this retains the physical first-step
cylinder and displays its common `1 / 4` factor. -/
theorem simpleRandomWalk_firstDirection_inter_oneStepRecenter_preimage
    (d : Direction) {A : Set WalkPath} (hA : MeasurableSet A) :
    simpleRandomWalk
        (firstDirectionWalk d ∩ oneStepRecenter ⁻¹' A) =
      (1 / 4 : ENNReal) * simpleRandomWalk A := by
  have hleft : MeasurableSet
      (firstDirectionWalk d ∩ oneStepRecenter ⁻¹' A) :=
    (measurableSet_firstDirectionWalk d).inter
      (hA.preimage measurable_oneStepRecenter)
  rw [simpleRandomWalk,
    Measure.map_apply measurable_trajectory hleft,
    Measure.map_apply measurable_trajectory hA]
  have hpre : trajectory ⁻¹'
        (firstDirectionWalk d ∩ oneStepRecenter ⁻¹' A) =
      firstDirectionSteps d ∩ shiftSteps 1 ⁻¹' (trajectory ⁻¹' A) := by
    ext omega
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    rw [oneStepRecenter_trajectory]
    change (trajectory omega ∈ firstDirectionWalk d ∧
      trajectory (shiftSteps 1 omega) ∈ A) ↔
      (omega ∈ firstDirectionSteps d ∧
        trajectory (shiftSteps 1 omega) ∈ A)
    rw [show trajectory omega ∈ firstDirectionWalk d ↔
        omega ∈ firstDirectionSteps d by
      exact Set.ext_iff.mp (trajectory_preimage_firstDirectionWalk d) omega]
  rw [hpre]
  exact fairSteps_firstDirection_inter_shiftSteps_preimage d
    (hA.preimage measurable_trajectory)

theorem simpleRandomWalk_checkerPrefixedPreimage
    (d : Direction) {A : Set WalkPath} (hA : MeasurableSet A) :
    simpleRandomWalk (checkerPrefixedPreimage d A) =
      (1 / 4 : ENNReal) * simpleRandomWalk A :=
  simpleRandomWalk_firstDirection_inter_oneStepRecenter_preimage d hA

/-! ## Exact coordinate-mass transport -/

/-- Pull a coordinate-mass specification through the checker recentering
while fixing the deleted physical direction.  The coordinate law and product
probability are unchanged; only the common cylinder factor is multiplied by
`1 / 4`. -/
noncomputable def coordinateMassSpecCheckerPrefixedTransport
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ENNReal}
    (d : Direction) (spec : CoordinateMassSpec piece next cost) :
    CoordinateMassSpec
      (fun z ↦ checkerPrefixedPreimage d (piece z))
      (oneStepRecenter ⁻¹' next) cost where
  screened := fun z cap ↦ checkerPrefixedPreimage d (spec.screened z cap)
  fiber := fun z cap ↦ checkerPrefixedPreimage d (spec.fiber z cap)
  measurable_screened := fun z cap ↦
    measurableSet_checkerPrefixedPreimage (spec.measurable_screened z cap) d
  measurable_fiber := fun z cap ↦
    measurableSet_checkerPrefixedPreimage (spec.measurable_fiber z cap) d
  screened_subset_piece := by
    intro z cap s hs
    exact ⟨hs.1, spec.screened_subset_piece z cap hs.2⟩
  fiber_subset_piece := by
    intro z cap s hs
    exact ⟨hs.1, spec.fiber_subset_piece z cap hs.2⟩
  monotone_screened := by
    intro z a b hab s hs
    exact ⟨hs.1, spec.monotone_screened z hab hs.2⟩
  transition_covered := by
    intro z s hs
    have htarget : oneStepRecenter s ∈ piece z ∩ next := ⟨hs.1.2, hs.2⟩
    rcases Set.mem_iUnion.mp (spec.transition_covered z htarget) with
      ⟨cap, hcap⟩
    exact Set.mem_iUnion.mpr ⟨cap, hs.1.1, hcap⟩
  commonFactor := fun z cap ↦
    (1 / 4 : ENNReal).toReal * spec.commonFactor z cap
  screenedCoordinateMass := spec.screenedCoordinateMass
  fiberCoordinateMass := spec.fiberCoordinateMass
  productProbability := spec.productProbability
  coordinate_identity := spec.coordinate_identity
  screened_event_mass := by
    intro z cap
    have hmass := simpleRandomWalk_checkerPrefixedPreimage d
      (spec.measurable_screened z cap)
    have hold := spec.screened_event_mass z cap
    change (simpleRandomWalk (spec.screened z cap)).toReal =
      spec.commonFactor z cap * spec.screenedCoordinateMass z cap at hold
    change (simpleRandomWalk
      (checkerPrefixedPreimage d (spec.screened z cap))).toReal = _
    rw [hmass, ENNReal.toReal_mul, hold]
    ring
  fiber_event_mass := by
    intro z cap
    have hmass := simpleRandomWalk_checkerPrefixedPreimage d
      (spec.measurable_fiber z cap)
    have hold := spec.fiber_event_mass z cap
    change (simpleRandomWalk (spec.fiber z cap)).toReal =
      spec.commonFactor z cap * spec.fiberCoordinateMass z cap at hold
    change (simpleRandomWalk
      (checkerPrefixedPreimage d (spec.fiber z cap))).toReal = _
    rw [hmass, ENNReal.toReal_mul, hold]
    ring
  product_bound := spec.product_bound

@[simp] theorem coordinateMassSpecCheckerPrefixedTransport_productProbability
    {index : Type*} {piece : index → Set WalkPath}
    {next : Set WalkPath} {cost : ENNReal}
    (d : Direction) (spec : CoordinateMassSpec piece next cost)
    (z : index) (cap : Nat) :
    (coordinateMassSpecCheckerPrefixedTransport d spec).productProbability
        z cap = spec.productProbability z cap := rfl

end

end Erdos1165.HLOZCheckerPrefixedCylinderTransport
