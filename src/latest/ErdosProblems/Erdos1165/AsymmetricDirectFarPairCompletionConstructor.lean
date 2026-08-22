/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialCompletionFamily
import ErdosProblems.Erdos1165.AsymmetricLiteralPairEndpoint
import ErdosProblems.Erdos1165.SharedPrefixPairExtraction

/-!
# Direct far-pair construction from genuine pair-success completion atoms

The stopped thick-pair event is already a subevent of stopped success at
both centres.  Once a genuine asymmetric completion family covers that
pair-success event, no terminal replacement of the right branch is needed.
This file packages the resulting stronger estimate in the existing
`ActualMarkedFarPairData` interface using its legitimate zero-coordinate
stopped-data decomposition.

The radial comparison is still obtained from literal retained/tail atoms and
their exact conditional masses; no scalar pair comparison is an input.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricDirectFarPairCompletionConstructor

open AnnularProfileSequentialUpper AppendixPair AppendixPairCrossingTail
open AppendixPairCrossingTailLiteral AppendixPairMoment
open AsymmetricActualFarPairData
open AsymmetricCompatibleRadialCompletionFamily
open MarkedBoundaryVisitKernel MarkedTerminalDisintegration
open Proposition13Assembly
open Proposition13LiteralAssembly Proposition13Scales
open SharedPrefixPairExtraction

noncomputable section

/-- The zero-coordinate stopped-data decomposition of a pair-success event.
Its marked upper statement is simply monotonicity from stopped thick-pair
success to stopped pair success. -/
theorem zeroCoordinatePairDecomposition
    {delta : ℝ} {n : ℕ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (skeletonKernel : Fin 0 → Unit → Unit → ℝ≥0∞)
    (markedKernel : Fin 0 → Unit → ℕ → Unit → ℝ≥0∞) :
    MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x ∩
        stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) y)
      (stoppedSuccessfulPairEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x y)
      (fun _ : Unit ↦ fun _ : Fin 0 → Unit ↦ fun _ : Fin 0 → Unit ↦
        fairSteps (stoppedSuccessfulPairEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x y))
      skeletonKernel markedKernel
      Set.univ := by
  constructor
  · simp [successfulSkeletonMass, skeletonProduct]
  · have hsubset :
        stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) x ∩
          stoppedThickPointEvent
            ((i : ℕ) * chosenBlockLength delta n)
            (scaleIndex delta n) chosenProfileDelta
            (chosenThickDelta delta) y ⊆
        stoppedSuccessfulPairEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x y := by
      rintro omega ⟨hx, hy⟩
      exact
        ⟨stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent _ _ _ _ _ hx,
          stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent _ _ _ _ _ hy⟩
    refine (measure_mono hsubset).trans_eq ?_
    simp [markedVisitEventMass, restrictedMarkedProduct, markedProduct]

/-- A genuine completion family covering stopped success at both centres
constructs the existing far-pair record directly once its retained event has
the one-point-scale mass bound.  The retained event need not itself be the
full successful event at the left centre; this is the form used by the
buffered separation construction. -/
def of_pairSuccessfulCompletion_with_retainedUpper
    {delta : ℝ} {n : ℕ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (radialCertificate : ProfileRadialTailCertificate delta n x y)
    (retained gammaX : Set StepPath)
    (radialFamily : CompatibleRadialCompletionFamily
      (stoppedSuccessfulPairEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x y)
      retained
      gammaX
      radialCertificate.radialTail)
    (hretainedUpper : fairSteps.real retained ≤ pairPointEnvelope delta n) :
    ActualMarkedFarPairData delta n (Real.exp (1 / 4)) i x y := by
  let successful := stoppedSuccessfulPairEvent
    ((i : ℕ) * chosenBlockLength delta n)
    (scaleIndex delta n) chosenProfileDelta x y
  have hsuccessful : fairSteps.real successful ≤
      radialCertificate.radialTail * fairSteps.real retained :=
    radialFamily.successful_le radialCertificate.radial_nonneg
  refine
    { Data := Unit
      Entrance := Unit
      Exit := Unit
      coordinateCount := 0
      successful := successful
      retained := retained
      radialTail := radialCertificate.radialTail
      boundary := Fin.elim0
      target := Fin.elim0
      entrance := Fin.elim0
      endpoint := Fin.elim0
      hitProbability := Fin.elim0
      escapeProbability := Fin.elim0
      hitError := Fin.elim0
      exitError := Fin.elim0
      target_not_boundary := fun j ↦ Fin.elim0 j
      escape_nonneg := fun j ↦ Fin.elim0 j
      escape_le_one := fun j ↦ Fin.elim0 j
      escape_eq := fun j ↦ Fin.elim0 j
      hit_nonneg := fun j ↦ Fin.elim0 j
      hit_lt_one := fun j ↦ Fin.elim0 j
      hitError_nonneg := fun j ↦ Fin.elim0 j
      exitError_nonneg := fun j ↦ Fin.elim0 j
      hitFactor_nonneg := fun j ↦ Fin.elim0 j
      exitFactor_nonneg := fun j ↦ Fin.elim0 j
      hitLower := fun j ↦ Fin.elim0 j
      hitUpper := fun j ↦ Fin.elim0 j
      exitLower := fun j ↦ Fin.elim0 j
      exitUpper := fun j ↦ Fin.elim0 j
      visitEvent := Set.univ
      skeletonWeight := fun _ _ _ ↦ fairSteps successful
      decomposition := by
        constructor
        · simp [successfulSkeletonMass, skeletonProduct]
        · have hsubset :
              stoppedThickPointEvent
                  ((i : ℕ) * chosenBlockLength delta n)
                  (scaleIndex delta n) chosenProfileDelta
                  (chosenThickDelta delta) x ∩
                stoppedThickPointEvent
                  ((i : ℕ) * chosenBlockLength delta n)
                  (scaleIndex delta n) chosenProfileDelta
                  (chosenThickDelta delta) y ⊆ successful := by
            rintro omega ⟨hx, hy⟩
            exact
              ⟨stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent
                  _ _ _ _ _ hx,
                stoppedThickPointEvent_subset_stoppedSuccessfulPointEvent
                  _ _ _ _ _ hy⟩
          refine (measure_mono hsubset).trans_eq ?_
          simp [markedVisitEventMass, restrictedMarkedProduct,
            markedProduct]
      referenceMass_le_one := by
        simp [referenceEventMass, restrictedReferenceProduct,
          referenceProduct]
      accumulatedLoss_le := by
        simp
      radialTail_nonneg := radialCertificate.radial_nonneg
      successful_le := hsuccessful
      retained_le := hretainedUpper
      radialTail_le := radialCertificate.le_pairEnvelope_div_prefix }

/-- Specialization in which the retained completion is contained in the full
left successful event and its mass is bounded by the existing sequential
one-point family. -/
def of_pairSuccessfulCompletion
    {delta : ℝ} {n : ℕ} {historyGain : ℝ}
    {i : Fin (chosenBlockCount delta n)} {x y : Point}
    (radialCertificate : ProfileRadialTailCertificate delta n x y)
    (retained : Set StepPath)
    (radialFamily : CompatibleRadialCompletionFamily
      (stoppedSuccessfulPairEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x y)
      retained
      (stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x)
      radialCertificate.radialTail)
    (onePointFamily : SequentialProfileUpperFamily
      ((i : ℕ) * chosenBlockLength delta n) (scaleIndex delta n)
      chosenProfileDelta historyGain x)
    (hprofileTail : ProfileWeightUpper.profileUpperTailStart ≤
      scaleIndex delta n)
    (hhistoryGain : historyGain ≤ Real.exp prefixProfileCostDeficit) :
    ActualMarkedFarPairData delta n (Real.exp (1 / 4)) i x y := by
  have hretainedUpper : fairSteps.real retained ≤ pairPointEnvelope delta n :=
    successful_le_pairPointEnvelope_of_sequentialUpperFamily retained
      onePointFamily radialFamily.retained_subset hprofileTail hhistoryGain
  exact of_pairSuccessfulCompletion_with_retainedUpper radialCertificate
    retained
    (stoppedSuccessfulPointEvent
      ((i : ℕ) * chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta x)
    radialFamily hretainedUpper

end

end Erdos1165.AsymmetricDirectFarPairCompletionConstructor
