/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricLiteralPairEndpoint
import ErdosProblems.Erdos1165.AsymmetricTerminalCompletionFarPair

/-!
# Source endpoint for genuine asymmetric completion atoms

This is the source-facing endpoint matching
`CompatibleRadialCompletionFamily`.  The retained one-point inclusion is a
field of the completion family itself, so no cylinder identification or
separate probability comparison is exposed.
-/

open Filter MeasureTheory Set

namespace Erdos1165.AsymmetricCompletionRadialSourceEndpoint

open AnnularProfileSequentialUpper AppendixPair AppendixPairCrossingTail
open AppendixPairMoment AsymmetricActualFarPairData
open AsymmetricCompatibleRadialCompletionFamily
open AsymmetricLiteralPairEndpoint AsymmetricPairPartitionUpper
open AsymmetricTerminalCompletionFarPair
open AsymmetricTerminalPartitionAdapter
open Proposition13Assembly Proposition13LiteralAssembly Proposition13Scales

noncomputable section

/-- Concrete completion-atom data at one selected scale. -/
structure AsymmetricCompletionRadialSourceData
    (delta : ℝ) (n : ℕ) : Type 2 where
  onePointFamily : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      SequentialProfileUpperFamily
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta
        (Real.exp prefixProfileCostDeficit) x
  retained : ∀ (_i : Fin (chosenBlockCount delta n)) (x : Point),
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    ∀ (y : Point), y ∈ ThickPoint.candidateBox (scaleIndex delta n) →
      separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n) →
      GaussianGeometricCutoff.geometricCutoff ≤
        pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y) → Set StepPath
  radialFamily : ∀ (i : Fin (chosenBlockCount delta n)) (x : Point)
      (hx : x ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (y : Point) (hy : y ∈ ThickPoint.candidateBox (scaleIndex delta n))
      (hlevel : separationLevel (scaleIndex delta n) x y ≤
        decorrelationCutoff (scaleIndex delta n))
      (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
        pairPrefixScale (scaleIndex delta n)
          (separationLevel (scaleIndex delta n) x y)),
    CompatibleRadialCompletionFamily
      (asymmetricSuccessful
        (skeletonAtom
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta y))
      (retained i x hx y hy hlevel hcutoff)
      (stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x)
      (ProfileRadialTailCertificate.expOne hcutoff).radialTail

/-- Convert a concrete completion source to the final fixed-scale source
record. -/
def AsymmetricCompletionRadialSourceData.toPairSourceData
    {delta : ℝ} {n : ℕ}
    (source : AsymmetricCompletionRadialSourceData delta n)
    (htail : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n) :
    AsymmetricPairSourceData delta n where
  onePointFamily := source.onePointFamily
  farPairData := by
    intro terminal i x hx y hy hlevel radial
    let canonical := ProfileRadialTailCertificate.expOne radial.cutoff
    exact of_terminalPartition_compatibleRadialCompletion terminal canonical
      (source.retained i x hx y hy hlevel radial.cutoff)
      (source.radialFamily i x hx y hy hlevel radial.cutoff)
      (source.onePointFamily i x hx) htail le_rfl

/-- Eventual genuine completion sources imply the requested literal pair
data without any scalar pair-comparison premise. -/
theorem eventually_nonempty_literalPairData_of_completionRadialSource
    {delta : ℝ} (hdelta : 0 < delta)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (AsymmetricCompletionRadialSourceData delta n)) :
    ∀ᶠ n : ℕ in atTop, Nonempty (LiteralPairData delta n) := by
  have htail : ∀ᶠ n : ℕ in atTop,
      ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n := by
    have hreal := (tendsto_scaleIndex_atTop delta).eventually
      (eventually_ge_atTop
        (ProfileWeightUpper.profileUpperTailStart : ℝ))
    filter_upwards [hreal] with n hn
    exact_mod_cast hn
  apply eventually_nonempty_literalPairData_of_source hdelta
  filter_upwards [hsource, htail] with n hsourceN htailN
  exact ⟨(AsymmetricCompletionRadialSourceData.toPairSourceData
    (Classical.choice hsourceN) htailN)⟩

end

end Erdos1165.AsymmetricCompletionRadialSourceEndpoint
