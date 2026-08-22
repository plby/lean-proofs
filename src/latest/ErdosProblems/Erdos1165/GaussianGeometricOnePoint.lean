/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianGeometricCutoff
import ErdosProblems.Erdos1165.GaussianGeometricNumerical

/-!
# Closed Appendix A.8--A.12 one-point estimate

The explicit cutoff, geometric small-ball schedule, shifted A.11 estimate,
and asymptotic cost absorption are combined here.  The resulting theorem is
in the exact `AnnularComparisons` interface; only the genuinely walk-specific
annular transfer, terminal refinement, and pair comparison remain as inputs.
-/

open Filter MeasureTheory Set

namespace Erdos1165.GaussianGeometricOnePoint

noncomputable section

open AppendixFirstMoment AppendixA11A12OnePoint
  AppendixA11A12ScaleCertificate Proposition13Assembly Proposition13Scales
  GaussianGeometricSchedule GaussianGeometricCutoff
  GaussianGeometricNumerical

/-- The complete analytic Appendix profile lower bound at the canonical
rounded scale, retaining the half-budget reserved for the literal annular
history. -/
theorem eventually_onePointBound_le_annularHistoryLoss_mul_constrainedProfileWeight
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      onePointBound delta n ≤
        annularHistoryLoss delta n *
          constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta := by
  filter_upwards
      [eventually_onePointBound_le_annularHistoryLoss_mul_canonicalGeometricProfileLower
        hdelta
        geometricCutoff_ge_thirty_two,
       (tendsto_scaleIndex_atTop delta).eventually
        (eventually_ge_atTop (geometricCutoff : ℝ))]
      with n hnumerical hq
  have hcutoff : geometricCutoff ≤ scaleIndex delta n := by exact_mod_cast hq
  exact hnumerical.trans (mul_le_mul_of_nonneg_left (by
    simpa only [chosenProfileDelta] using
      cutoff_canonicalGeometricSchedule_profileLower_le hcutoff)
    (annularHistoryLoss_pos delta n).le)

/-- Compatibility form with the annular reserve discarded. -/
theorem eventually_onePointBound_le_constrainedProfileWeight
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      onePointBound delta n ≤
        constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta := by
  filter_upwards
      [eventually_onePointBound_le_annularHistoryLoss_mul_constrainedProfileWeight
        hdelta]
      with n hprofile
  have hcost : 0 ≤ scaleCost delta n := by
    unfold scaleCost
    positivity
  have hloss : annularHistoryLoss delta n ≤ 1 := by
    unfold annularHistoryLoss
    rw [Real.exp_le_one_iff]
    nlinarith
  exact hprofile.trans (by
    have hweight := constrainedProfileWeight_nonneg
      (scaleIndex delta n) chosenProfileDelta
    nlinarith)

/-- Eventually, the one-point field of `AnnularComparisons` follows solely
from the annular profile-to-walk transfer. -/
theorem eventually_annularComparisons_onePointProfile_of_transfer
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      AnnularOnePointProfileTransfer delta n →
        ∀ (i : Fin (chosenBlockCount delta n)) x,
          x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
          onePointBound delta n ≤ fairSteps.real
            (stoppedSuccessfulPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta x) := by
  filter_upwards
      [eventually_onePointBound_le_annularHistoryLoss_mul_constrainedProfileWeight
        hdelta]
      with n hprofile
  intro htransfer i x hx
  exact hprofile.trans
    (htransfer.historyLoss_mul_constrainedProfile_le i x hx)

/-- **Final analytic Appendix adapter.**  All A.8--A.12 small-ball,
Taylor, reindexing, and numerical work is discharged. -/
theorem eventually_annularComparisons_of_geometricProfile
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      AnnularOnePointProfileTransfer delta n →
      TerminalPairComparisons delta n →
      AnnularComparisons delta n := by
  filter_upwards
      [eventually_annularComparisons_onePointProfile_of_transfer hdelta]
      with n honePoint
  intro htransfer hterminalPair
  exact {
    onePointProfile := honePoint htransfer
    terminalThick := hterminalPair.terminalThick
    pairMoment := hterminalPair.pairMoment }

/-- Pointwise-tail form of the final adapter, convenient for constructing
`HasAnnularComparisons`. -/
theorem annularComparisons_of_geometricProfile_of_eventually
    {delta : ℝ} (hdelta : 0 < delta)
    (htransfer : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (AnnularOnePointProfileTransfer delta n))
    (hterminalPair : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Nonempty (TerminalPairComparisons delta n)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nonempty (AnnularComparisons delta n) := by
  have haEv := eventually_annularComparisons_of_geometricProfile hdelta
  rw [Filter.eventually_atTop] at haEv
  obtain ⟨Na, ha⟩ := haEv
  obtain ⟨Nt, ht⟩ := htransfer
  obtain ⟨Np, hp⟩ := hterminalPair
  refine ⟨max Na (max Nt Np), ?_⟩
  intro n hn
  have hna : Na ≤ n := le_trans (le_max_left _ _) hn
  have hnt : Nt ≤ n := le_trans (le_max_left _ _)
    (le_trans (le_max_right Na (max Nt Np)) hn)
  have hnp : Np ≤ n := le_trans (le_max_right _ _)
    (le_trans (le_max_right Na (max Nt Np)) hn)
  obtain ⟨transfer⟩ := ht n hnt
  obtain ⟨terminalPair⟩ := hp n hnp
  exact ⟨ha n hna transfer terminalPair⟩

/-- Global packaging: the checked analytic work reduces
`HasAnnularComparisons` exactly to the remaining annular transfer and
terminal/pair inputs. -/
theorem hasAnnularComparisons_of_geometricProfile
    (htransfer : ∀ delta : ℝ, 0 < delta →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Nonempty (AnnularOnePointProfileTransfer delta n))
    (hterminalPair : ∀ delta : ℝ, 0 < delta →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Nonempty (TerminalPairComparisons delta n)) :
    HasAnnularComparisons := by
  intro delta hdelta
  exact annularComparisons_of_geometricProfile_of_eventually hdelta
    (htransfer delta hdelta) (hterminalPair delta hdelta)

end

end Erdos1165.GaussianGeometricOnePoint
