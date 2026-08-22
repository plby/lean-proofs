/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricDirectFarPairCompletionConstructor

/-!
# Source endpoint for direct pair-success completion families

This is the sound source-facing endpoint for the coarse asymmetric
completion.  Its radial family covers stopped success at both centres, not
the unrestricted right-success event.  The zero-coordinate direct far-pair
constructor then supplies the existing final literal interface.
-/

open Filter MeasureTheory Set

namespace Erdos1165.AsymmetricDirectCompletionSourceEndpoint

open AnnularProfileSequentialUpper AppendixPair AppendixPairCrossingTail
open AppendixPairMoment
open AsymmetricActualFarPairData AsymmetricCompatibleRadialCompletionFamily
open AsymmetricDirectFarPairCompletionConstructor
open AsymmetricLiteralPairEndpoint Proposition13Assembly
open Proposition13LiteralAssembly Proposition13Scales
open SharedPrefixPairExtraction

noncomputable section

/-- Concrete pair-success completion data at one selected scale. -/
structure AsymmetricDirectCompletionSourceData
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
      (stoppedSuccessfulPairEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x y)
      (retained i x hx y hy hlevel hcutoff)
      (stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x)
      (ProfileRadialTailCertificate.expOne hcutoff).radialTail

/-- Convert a direct pair-success completion source to the final fixed-scale
source record.  The terminal certificate argument of the legacy interface
is intentionally unused. -/
def AsymmetricDirectCompletionSourceData.toPairSourceData
    {delta : ℝ} {n : ℕ}
    (source : AsymmetricDirectCompletionSourceData delta n)
    (htail : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n) :
    AsymmetricPairSourceData delta n where
  onePointFamily := source.onePointFamily
  farPairData := by
    intro _terminal i x hx y hy hlevel radial
    let canonical := ProfileRadialTailCertificate.expOne radial.cutoff
    exact of_pairSuccessfulCompletion canonical
      (source.retained i x hx y hy hlevel radial.cutoff)
      (source.radialFamily i x hx y hy hlevel radial.cutoff)
      (source.onePointFamily i x hx) htail le_rfl

/-- Eventual direct completion sources give the requested literal pair data
without a terminal replacement or scalar pair-comparison premise. -/
theorem eventually_nonempty_literalPairData_of_directCompletionSource
    {delta : ℝ} (hdelta : 0 < delta)
    (hsource : ∀ᶠ n : ℕ in atTop,
      Nonempty (AsymmetricDirectCompletionSourceData delta n)) :
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
  exact ⟨(AsymmetricDirectCompletionSourceData.toPairSourceData
    (Classical.choice hsourceN) htailN)⟩

end

end Erdos1165.AsymmetricDirectCompletionSourceEndpoint
