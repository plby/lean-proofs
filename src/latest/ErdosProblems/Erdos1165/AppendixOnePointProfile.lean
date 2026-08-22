/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.Proposition13Assembly

/-!
# One-point Appendix-A profile input for the Proposition 1.3 certificate

`AppendixSmallBallAssembly` supplies the explicit positive finite quantity
`onePointProfileLower scale profileDelta` and proves that it is below the
exact constrained negative-binomial profile weight.  This file specializes
that result to the stopped successful-point events used by
`Proposition13Assembly.ScaleCertificate`.

The sole remaining input is `AnnularOnePointDisintegration`: the
random-walk-specific annular Harnack/disintegration comparison saying that
the ideal constrained profile weight is below the probability of the actual
stopped excursion event.  From it we produce an inequality whose type is
definitionally the `ScaleCertificate.onePointProfile` field.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AppendixOnePointProfile

noncomputable section

open AppendixFirstMoment AppendixSmallBallAssembly Proposition13Assembly

/-- The remaining walk-specific one-point input.  It contains exactly the
annular Harnack and conditional disintegration comparison, uniformly over
deterministic block starts and candidate sites. -/
structure AnnularOnePointDisintegration (blockCount scale : ℕ)
    (blockStart : Fin blockCount → ℕ) (profileDelta : ℝ) : Prop where
  profileDelta_le_one : profileDelta ≤ 1
  constrainedProfile_le : ∀ i x, x ∈ ThickPoint.candidateBox scale →
    constrainedProfileWeight scale profileDelta ≤ fairSteps.real
      (stoppedSuccessfulPointEvent (blockStart i) scale profileDelta x)

/-- The explicit checked choice for `ScaleCertificate.onePoint`. -/
def certificateOnePoint (scale : ℕ) (profileDelta : ℝ) : ℝ :=
  onePointProfileLower scale profileDelta

lemma certificateOnePoint_pos (scale : ℕ) (profileDelta : ℝ) :
    0 < certificateOnePoint scale profileDelta :=
  onePointProfileLower_pos scale profileDelta

lemma certificateOnePoint_nonneg (scale : ℕ) (profileDelta : ℝ) :
    0 ≤ certificateOnePoint scale profileDelta :=
  (certificateOnePoint_pos scale profileDelta).le

/-- **The `ScaleCertificate.onePointProfile` field.**

All finite profile, Stirling, Taylor, Brownian-density, and lattice spectral
calculations have already been discharged.  Given only the annular
Harnack/disintegration comparison, the checked positive constant has the
uniform event-probability lower bound required by Proposition 1.3. -/
theorem scaleCertificate_onePointProfile
    {blockCount scale : ℕ} {blockStart : Fin blockCount → ℕ}
    {profileDelta : ℝ}
    (hAnnular : AnnularOnePointDisintegration blockCount scale blockStart profileDelta) :
    ∀ i x, x ∈ ThickPoint.candidateBox scale →
      certificateOnePoint scale profileDelta ≤ fairSteps.real
        (stoppedSuccessfulPointEvent (blockStart i) scale profileDelta x) := by
  intro i x hx
  exact onePointProfileLower_le_measureReal_of_annularHarnackDisintegration
    fairSteps scale hAnnular.profileDelta_le_one
    (stoppedSuccessfulPointEvent (blockStart i) scale profileDelta x)
    (hAnnular.constrainedProfile_le i x hx)

/-- Bundled pair of certificate fields obtained from the one-point annular
comparison: positivity/nonnegativity of `onePoint`, and its uniform profile
lower bound. -/
theorem scaleCertificate_onePoint_fields
    {blockCount scale : ℕ} {blockStart : Fin blockCount → ℕ}
    {profileDelta : ℝ}
    (hAnnular : AnnularOnePointDisintegration blockCount scale blockStart profileDelta) :
    0 ≤ certificateOnePoint scale profileDelta ∧
      (∀ i x, x ∈ ThickPoint.candidateBox scale →
        certificateOnePoint scale profileDelta ≤ fairSteps.real
          (stoppedSuccessfulPointEvent (blockStart i) scale profileDelta x)) :=
  ⟨certificateOnePoint_nonneg scale profileDelta,
    scaleCertificate_onePointProfile hAnnular⟩

end

end Erdos1165.AppendixOnePointProfile
