/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixA8OnePoint
import ErdosProblems.Erdos1165.AppendixOnePointProfile

/-!
# Quantitative A.8 input for the Proposition 1.3 scale certificate

This is the walk-facing specialization of `AppendixA8OnePoint`.  The only
remaining input is the annular Harnack/disintegration comparison.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AppendixA8ScaleCertificate

noncomputable section

open AppendixFirstMoment AppendixA8OnePoint AppendixOnePointProfile
  Proposition13Assembly

/-- **Exact `ScaleCertificate.onePointProfile` field from checked A.8.**

The block starts are the literal consecutive starts used by
`ScaleCertificate`; the only walk-specific input is `hAnnular`. -/
theorem scaleCertificate_onePointProfile_of_quantitativeA8
    {blockCount blockLength start steps n R : ℕ} (hstart : 2 ≤ start)
    (hbound : start + steps ≤ n)
    (hscale : (2560 : ℝ) * (n : ℝ) ^ 2 ≤ (R : ℝ) ^ 2)
    {profileDelta : ℝ}
    (hcenter : ∀ l ∈ Finset.Icc start (start + steps),
      R ≤ profileCenter l)
    (hwidth : ∀ l ∈ Finset.Icc start (start + steps),
      (R : ℝ) ≤ (l : ℝ) ^ (1 + profileDelta))
    (hAnnular : AnnularOnePointDisintegration blockCount (start + steps)
      (fun i ↦ (i : ℕ) * blockLength) profileDelta) :
    ∀ (i : Fin blockCount) x,
      x ∈ ThickPoint.candidateBox (start + steps) →
      quantitativeA8OnePoint (steps := steps) (n := n) (R := R) hstart ≤
        fairSteps.real
          (stoppedSuccessfulPointEvent ((i : ℕ) * blockLength)
            (start + steps) profileDelta x) := by
  intro i x hx
  exact (quantitativeA8OnePoint_le_constrainedProfileWeight
      hstart hbound hscale hAnnular.profileDelta_le_one hcenter hwidth).trans
    (hAnnular.constrainedProfile_le i x hx)

end

end Erdos1165.AppendixA8ScaleCertificate
