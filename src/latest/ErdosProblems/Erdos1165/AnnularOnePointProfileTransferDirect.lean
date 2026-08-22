/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialContourMass
import ErdosProblems.Erdos1165.AnnularRadialSplicedFamily
import ErdosProblems.Erdos1165.AnnularRadialHistoryBudget
import ErdosProblems.Erdos1165.AnnularShiftedStoppedEvent
import ErdosProblems.Erdos1165.AppendixA11A12ScaleCertificate

/-!
# Literal annular one-point profile transfer

This module sums the selected spatially-spliced radial-word atoms and
transports their zero-block lower bound to every deterministic block start.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AnnularOnePointProfileTransferDirect

open AppendixFirstMoment AppendixA11A12OnePoint
  AppendixA11A12ScaleCertificate Proposition13Assembly Proposition13Scales
  AnnularRadialLabelWord AnnularRadialProfileWords
  AnnularRadialChainLower AnnularRadialReferenceEdge
  AnnularRadialContourMass AnnularRadialSplicedFamily
  AnnularRadialHistoryBudget AnnularShiftedStoppedEvent
  TerminalNegativeBinomialWindow ExcursionTransition ThickPoint

noncomputable section

private theorem radialBudget_le_fixedProfileSplicedFamily_real_of_reference
    {n : ℕ} (hn : 5 ≤ n) {delta : ℝ} {x : Point} {m : Profile n}
    (hfamily :
      (1 / 128 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) *
          (∑ word : {word : BoundedRadialLabelWord n
              (profileRadialWordMaxTransitions n) //
              IsFixedProfileRadialWord n delta m word},
            radialChainReference (annularIdealEdge n)
              (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) *
          (1 / 128 : ℝ≥0∞) ≤
        fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m))
    (hreference :
      ENNReal.ofReal
          (firstProfileTransitionMass (by omega) m *
            terminalWindowMass n delta (terminalProfileCount (by omega) m) *
            profileWeight m) ≤
        ∑ word : {word : BoundedRadialLabelWord n
            (profileRadialWordMaxTransitions n) //
            IsFixedProfileRadialWord n delta m word},
          radialChainReference (annularIdealEdge n)
            (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) :
    (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
        firstProfileTransitionMass (by omega) m *
        terminalWindowMass n delta (terminalProfileCount (by omega) m) *
        profileWeight m ≤
      fairSteps.real (fixedProfileSplicedRadialFamilyAtom n delta x m) := by
  let radialMass : ℝ :=
    firstProfileTransitionMass (by omega) m *
      terminalWindowMass n delta (terminalProfileCount (by omega) m) *
      profileWeight m
  have hterminal :
      0 ≤ terminalWindowMass n delta (terminalProfileCount (by omega) m) :=
    terminalWindowMass_nonneg _ _ _
      (terminalSuccess_pos (by omega)).le
      (terminalSuccess_le_one (by omega))
  have hradialMass : 0 ≤ radialMass := by
    dsimp only [radialMass]
    exact mul_nonneg
      (mul_nonneg (transitionMass_nonneg _ _) hterminal)
      (profileWeight_nonneg m)
  have henn :
      (1 / 128 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) *
          ENNReal.ofReal radialMass * (1 / 128 : ℝ≥0∞) ≤
        fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m) := by
    calc
      _ ≤ (1 / 128 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) *
            (∑ word : {word : BoundedRadialLabelWord n
                (profileRadialWordMaxTransitions n) //
                IsFixedProfileRadialWord n delta m word},
              radialChainReference (annularIdealEdge n)
                (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail) *
            (1 / 128 : ℝ≥0∞) := by
        simpa only [radialMass] using
          mul_le_mul (mul_le_mul le_rfl hreference bot_le bot_le)
            le_rfl bot_le bot_le
      _ ≤ _ := hfamily
  have hreal := ENNReal.toReal_mono
    (measure_ne_top fairSteps
      (fixedProfileSplicedRadialFamilyAtom n delta x m)) henn
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hradialMass] at hreal
  norm_num at hreal
  dsimp only [radialMass] at hreal
  simpa only [Measure.real] using (show
    (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
        firstProfileTransitionMass (by omega) m *
        terminalWindowMass n delta (terminalProfileCount (by omega) m) *
        profileWeight m ≤
      ENNReal.toReal
        (fairSteps (fixedProfileSplicedRadialFamilyAtom n delta x m)) by
    nlinarith [hreal])

private theorem nonempty_annularOnePointProfileTransfer_of_fixedProfile_lower
    {delta : ℝ} {N : ℕ}
    (hq : 5 ≤ scaleIndex delta N)
    (hhistory : ∀ m : Profile (scaleIndex delta N),
      IsConstrainedProfile chosenProfileDelta m →
        annularHistoryLoss delta N * profileWeight m ≤
          (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
            firstProfileTransitionMass (by omega) m *
            terminalWindowMass (scaleIndex delta N) chosenProfileDelta
              (terminalProfileCount (by omega) m) * profileWeight m)
    (hprofile : ∀ x, x ∈ candidateBox (scaleIndex delta N) →
      ∀ m : Profile (scaleIndex delta N),
        IsConstrainedProfile chosenProfileDelta m →
          (1 / 128 : ℝ) * (1 / 128 : ℝ) * (1 / 2 : ℝ) *
              firstProfileTransitionMass (by omega) m *
              terminalWindowMass (scaleIndex delta N) chosenProfileDelta
                (terminalProfileCount (by omega) m) * profileWeight m ≤
            fairSteps.real
              (fixedProfileSplicedRadialFamilyAtom
                (scaleIndex delta N) chosenProfileDelta x m)) :
    Nonempty (AnnularOnePointProfileTransfer delta N) := by
  refine ⟨⟨?_⟩⟩
  intro i x hx
  rw [fairStepsReal_stoppedSuccessfulPointEvent_eq_zero]
  have hsum :
      annularHistoryLoss delta N *
          constrainedProfileWeight (scaleIndex delta N) chosenProfileDelta ≤
        ∑ m : {m : Profile (scaleIndex delta N) //
            m ∈ constrainedProfiles (scaleIndex delta N) chosenProfileDelta},
          fairSteps.real
            (fixedProfileSplicedRadialFamilyAtom
              (scaleIndex delta N) chosenProfileDelta x m.1) := by
    unfold constrainedProfileWeight
    rw [← Finset.sum_attach, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _hm ↦
      (hhistory m.1 (mem_constrainedProfiles.mp m.2)).trans
        (hprofile x hx m.1 (mem_constrainedProfiles.mp m.2))
  have hunion :
      (∑ m : {m : Profile (scaleIndex delta N) //
          m ∈ constrainedProfiles (scaleIndex delta N) chosenProfileDelta},
        fairSteps.real
          (fixedProfileSplicedRadialFamilyAtom
            (scaleIndex delta N) chosenProfileDelta x m.1)) =
        fairSteps.real
          (constrainedProfileSplicedRadialFamilyAtom
            (scaleIndex delta N) chosenProfileDelta x) := by
    rw [Measure.real,
      fairSteps_constrainedProfileSplicedRadialFamilyAtom_eq_sum
        (by omega) chosenProfileDelta hx,
      ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top fairSteps _)]
    rfl
  rw [hunion] at hsum
  exact hsum.trans (measureReal_mono
    (constrainedProfileSplicedRadialFamilyAtom_subset_stoppedSuccess
      (by omega) hx))

private theorem eventually_nonempty_annularOnePointProfileTransfer_of_reference
    (hreference : ∀ {n : ℕ} (hn : 2 ≤ n) {profileDelta : ℝ},
      profileDelta ≤ 1 → ∀ {m : Profile n},
      IsConstrainedProfile profileDelta m →
        ENNReal.ofReal
            (firstProfileTransitionMass hn m *
              terminalWindowMass n profileDelta (terminalProfileCount hn m) *
              profileWeight m) ≤
          ∑ word : {word : BoundedRadialLabelWord n
              (profileRadialWordMaxTransitions n) //
              IsFixedProfileRadialWord n profileDelta m word},
            radialChainReference (annularIdealEdge n)
              (word.1.2.level ⟨0, by omega⟩) word.1.2.toList.tail)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      Nonempty (AnnularOnePointProfileTransfer delta N) := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  filter_upwards
      [eventually_annularHistoryLoss_mul_profileWeight_le_radial_budget hdelta,
        hscaleNat.eventually
          eventually_fixedProfile_reference_sum_le_spliced_family,
        hscaleNat.eventually (eventually_ge_atTop 5)]
      with N hhistory hfamily hq
  apply nonempty_annularOnePointProfileTransfer_of_fixedProfile_lower hq
  · intro m hm
    exact hhistory (by omega) m hm
  · intro x hx m hm
    exact radialBudget_le_fixedProfileSplicedFamily_real_of_reference
      hq (hfamily hq chosenProfileDelta x hx m)
        (hreference (by omega) (by norm_num [chosenProfileDelta]) hm)

/-- The literal walk-facing A.6 transfer: for every positive target
parameter and all sufficiently large target scales, the exact one-point
profile comparison is inhabited.  The proof uses only the selected
initial/radial/final splice atoms and their pathwise inclusion in the
successful stopped event. -/
theorem eventually_nonempty_annularOnePointProfileTransfer
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      Nonempty (AnnularOnePointProfileTransfer delta N) := by
  apply eventually_nonempty_annularOnePointProfileTransfer_of_reference
    (hdelta := hdelta)
  intro n hn profileDelta hprofileDelta m hm
  exact ofReal_profile_terminal_mass_le_fixedProfileRadialWord_reference_sum
    hn hprofileDelta hm

end

end Erdos1165.AnnularOnePointProfileTransferDirect
