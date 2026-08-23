import ErdosProblems.Erdos1166.Erdos1166HLOZProp47SourceAssembly

/-!
# The direct high-distance stage in HLOZ Proposition 4.7

This file replaces the bundled high-branch `StageBound` by the literal
sequential escape-before-return estimate used in (4.36).  The deterministic
history inclusion and the grid arithmetic are proved here; the sole remaining
probabilistic premise is the strong-Markov escape estimate on the preceding
history.
-/

namespace Erdos1166.HLOZProp47HighStageConnector

open Filter MeasureTheory Set
open scoped ENNReal
open HLOZScreeningAssembly HLOZPairing.ScreeningBridge
open HLOZProp47Parameters HLOZProp47SourceObjects HLOZProp47SourceAssembly

/-- On the chosen `delta`-grid, the first exponent strictly above `kappaTwo`
is already at least `kappaTwo + delta`. -/
theorem kappaTwo_le_alphaValue_sub_delta (a : AlphaIndex)
    (h : kappaTwo < alphaValue a) :
    kappaTwo ≤ alphaValue a - delta := by
  have hreal : (324 : ℝ) < (a.1 : ℝ) + 1 := by
    norm_num [kappaTwo, alphaValue, delta] at h
    linarith
  have hnat : 324 ≤ a.1 := by
    have : 324 < a.1 + 1 := by exact_mod_cast hreal
    omega
  have hnatReal : (324 : ℝ) ≤ (a.1 : ℝ) := by exact_mod_cast hnat
  norm_num [kappaTwo, alphaValue, delta]
  linarith

/-- The next high-distance history is contained in the preceding sequential
history intersected with the source exit-before-return event. -/
theorem highHistory_succ_subset_exitHistory
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (m : ℕ) (i : Fin 6) (a : AlphaTriple) (r : StageIndex)
    (hm : 1 ≤ m)
    (hhigh : kappaTwo < alphaValue (tripleAlphaIndex a r)) :
    prop47History profiles cStar m i a (r.1 + 1) ⊆
      prop47History profiles cStar m i a r.1 ∩
        exitBeforeReturnAtNextCreation m (stageNumber r)
          (Real.exp ((m : ℝ) ^ kappaTwo) / 3) := by
  intro s hs
  rw [prop47History, screeningHistory_succ] at hs
  simp only [r.isLt, dite_true] at hs
  refine ⟨hs.1, ?_⟩
  rw [prop47StageEvent, if_neg (not_le.mpr hhigh)] at hs
  exact highScale_bin_subset_exitBeforeReturn m (stageNumber r)
    (alphaValue (tripleAlphaIndex a r)) hm
    (kappaTwo_le_alphaValue_sub_delta _ hhigh) hs.2.2

/-- The sole probabilistic input in the high-distance branch of (4.36):
after the sequential prefix history, escaping the displayed ball before
returning to the preceding creation site costs one source stage rate. -/
def Prop47HighEscapeEstimate
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff : ℕ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ i a (r : StageIndex),
    kappaTwo < alphaValue (tripleAlphaIndex a r) →
    simpleRandomWalkLaw
        (prop47History profiles cStar m i a r.1 ∩
          exitBeforeReturnAtNextCreation m (stageNumber r)
            (Real.exp ((m : ℝ) ^ kappaTwo) / 3)) ≤
      sourceStageRate m stageCoeff kappa *
        simpleRandomWalkLaw (prop47History profiles cStar m i a r.1)

/-- The literal high-distance escape estimate implies the abstract high-stage
interface used by the final three-stage assembly. -/
theorem prop47HighStageEstimate_of_highEscape
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff errorCoeff : ℕ)
    (hEscape : Prop47HighEscapeEstimate profiles cStar stageCoeff) :
    Prop47HighStageEstimate profiles cStar stageCoeff errorCoeff := by
  filter_upwards [hEscape, eventually_atTop.2 ⟨1, fun _ hm ↦ hm⟩] with
    m hEscapeM hm
  intro i a r hhigh
  refine ⟨?_, ?_⟩
  · exact fun s hs ↦ (highHistory_succ_subset_exitHistory
      profiles cStar m i a r hm hhigh hs).1
  · calc
      simpleRandomWalkLaw (prop47History profiles cStar m i a (r.1 + 1)) ≤
          simpleRandomWalkLaw
            (prop47History profiles cStar m i a r.1 ∩
              exitBeforeReturnAtNextCreation m (stageNumber r)
                (Real.exp ((m : ℝ) ^ kappaTwo) / 3)) :=
        measure_mono (highHistory_succ_subset_exitHistory
          profiles cStar m i a r hm hhigh)
      _ ≤ sourceStageRate m stageCoeff kappa *
          simpleRandomWalkLaw (prop47History profiles cStar m i a r.1) :=
        hEscapeM i a r hhigh
      _ ≤ sourceStageRate m stageCoeff kappa *
          simpleRandomWalkLaw (prop47History profiles cStar m i a r.1) +
            sourceExceptionalRateWithPrefactor m errorCoeff kappa :=
        le_add_right (le_refl _)

/-- Source-decomposed Proposition 4.7 with the abstract high-stage predicate
replaced by its literal escape-before-return estimate. -/
theorem hlozPlanarConclusion_of_named_estimates_and_highEscape
    (profiles : Fin 6 → ExternalProfilePair) (cStar : Fin 6 → ℝ)
    (stageCoeff farCoeff lemma410Coeff prop45Coeff lemma411412Coeff : ℕ)
    (hFar : Prop47FarGapEstimate farCoeff)
    (hLemma410 : Prop47Lemma410Estimate lemma410Coeff)
    (hProp45 : Prop47Prop45Estimate profiles cStar prop45Coeff)
    (hLemma411412 : Prop47Lemma411412Estimate lemma411412Coeff)
    (hLow : Prop47LowStageEstimate profiles cStar stageCoeff
      (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
        lemma411412Coeff))
    (hHighEscape : Prop47HighEscapeEstimate profiles cStar stageCoeff) :
    HLOZPlanarConclusion := by
  exact hlozPlanarConclusion_of_prop47_named_source_estimates
    profiles cStar stageCoeff farCoeff lemma410Coeff prop45Coeff
      lemma411412Coeff hFar hLemma410 hProp45 hLemma411412 hLow
      (prop47HighStageEstimate_of_highEscape profiles cStar stageCoeff
        (prop47FailurePrefactor farCoeff lemma410Coeff prop45Coeff
          lemma411412Coeff) hHighEscape)

end Erdos1166.HLOZProp47HighStageConnector
