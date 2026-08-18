/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.CandidateEligibility
import ErdosProblems.Erdos186.PZ.Reduction.TerminalAbsorption

/-!
# Closing the strong-scale selector at the terminal state

This is the exact composition of the canonical-scale, dense-population, and
power-absorption estimates.  Once the controlled trace supplies a terminal
rank cap, population lower bound, and coarse progression-volume bound, one
uniform input threshold makes every dense coordinate candidate analytically
eligible.  Thus bounded irreducibility is nonvacuous at the terminal state.
-/

namespace Erdos186.PZ.Reduction

open Filter
open scoped Topology

noncomputable section

/-- Terminal rank, population, and coarse volume control imply local
candidate closure for the selector at scale exponent `1-ε`. -/
theorem exists_terminalCandidateClosure_threshold
    {β η : ℝ} (C : HigherDimensionalContext (2 * (β + 1)) η)
    (R : ℕ) (ε selectorExponent δ constant : ℝ)
    (hβ : 1 < β) (hη0 : 0 < η) (hη1 : η < 1)
    (hε0 : 0 < ε) (hε1 : ε < (1 / 3 : ℝ))
    (hselector0 : 0 < selectorExponent) (hselector1 : selectorExponent < 1)
    (hδ : 0 < δ) (hconstant : 0 < constant) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ (m : ℕ)
        (S : CoordinateReplacementState (C.scaleSelector selectorExponent)),
        threshold ≤ m → S.selected.dimension ≤ R →
        Real.rpow (m : ℝ) (1 - ε) < (S.points.card : ℝ) →
        (S.selected.progression.volume : ℝ) ≤
          constant * Real.rpow (m : ℝ) β →
        (C.scaleSelector selectorExponent).CandidateClosedAt
          S.points S.eligible δ := by
  obtain ⟨scaleThreshold, hscaleTwo, hscale⟩ :=
    exists_canonicalScale_threshold_boundedDimension C R hη0 hη1
      (ε := 1 - selectorExponent) (sub_pos.mpr hselector1)
      (by linarith)
  obtain ⟨absorbThreshold, habsorbTwo, habsorb⟩ :=
    exists_terminalAbsorption_threshold β ε δ constant R
      hβ hε0 hε1 hδ hconstant
  have hgrowth := (nat_rpow_tendsto_atTop (sub_pos.mpr
    (hε1.trans (by norm_num : (1 / 3 : ℝ) < 1)))).eventually_ge_atTop
      ((scaleThreshold : ℝ) / δ)
  obtain ⟨growthThreshold, hgrowth⟩ := eventually_atTop.1 hgrowth
  let threshold := max absorbThreshold (max 2 growthThreshold)
  refine ⟨threshold, le_max_of_le_right (le_max_left _ _), ?_⟩
  intro m S hm hrank hpopulation hvolume
  have habsorbM : absorbThreshold ≤ m :=
    (le_max_left _ _).trans hm
  have hgrowthM : growthThreshold ≤ m :=
    (le_max_right 2 growthThreshold).trans
      ((le_max_right absorbThreshold (max 2 growthThreshold)).trans hm)
  have hscaleCandidate : ∀ (X : Finset (BoxPoint S.selected.dimension)),
      X ⊆ S.selected.identifiedCore → X.Nonempty →
      δ * (S.points.card : ℝ) ≤ (X.card : ℝ) →
      scaleThreshold ≤ X.card := by
    intro X _hX _hXne hdense
    have hbase := hgrowth m hgrowthM
    have hscaleReal : (scaleThreshold : ℝ) ≤
        δ * Real.rpow (m : ℝ) (1 - ε) := by
      apply (div_le_iff₀ hδ).mp at hbase
      simpa [mul_comm] using hbase
    have hcandidateReal : (scaleThreshold : ℝ) ≤ (X.card : ℝ) :=
      hscaleReal.trans <|
        (mul_le_mul_of_nonneg_left hpopulation.le hδ.le).trans hdense
    exact_mod_cast hcandidateReal
  apply scaleSelector_candidateClosedAt_of_threshold
    (threshold := scaleThreshold)
  · intro q hq
    have hs := hscale S.selected.dimension hrank q hq
    have hexponent : (1 : ℝ) - (1 - selectorExponent) = selectorExponent := by
      ring
    rw [hexponent] at hs
    exact hs
  · exact hscaleCandidate
  · intro X _hX _hXne hdense
    exact habsorb m S.points.card X.card S.selected.progression.volume
      S.selected.dimension habsorbM hrank hpopulation hdense hvolume

end

end Erdos186.PZ.Reduction
