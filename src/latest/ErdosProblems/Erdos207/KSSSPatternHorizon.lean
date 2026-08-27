/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternStoppedLaw

/-! # One actual full-horizon state with degree and relative extension regularity -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem KSSSPowerParameters.exists_good_horizon_with_pattern_bands
    {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (sets : I → Finset V) (patterns : J → SimpleGraph V) (i₀ : I) (houter : sets i₀ = univ)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (H : SimpleGraph V)
    (bank : TripleSystemOn V) (X : Finset V) (c bankPower aPower r : ℕ) (eta : ℝ)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
    (hsep : ∀ i, i ≠ i₀ → AbsorberSeparatedLevel H X bank (sets i))
    (hrootLocal : HasPaddedAbsorberRootLocalization q X bank)
    (hInv₀ : GreedyInvariant F S₀) (hchosen₀ : S₀.chosen = ∅)
    (hEcard : (Q₀.card : ℝ) = E) (hQ₀ : ∀ Q ∈ Q₀, Q.card = 2)
    (hcover : ∀ T ∈ S₀.available, ∀ Q : Finset V, Q.card = 2 → Q ⊆ T.1 → Q ∈ Q₀)
    (hregular : KSSSInitialRegularity F S₀ q Q₀ a E A eta)
    (hfamily : ∀ C ∈ F, C ⊆ S₀.available) (heta : 0 ≤ eta)
    (hetaSmall : eta ≤ 1 / (6 * (t : ℝ) ^ ksssPowerErrorExponent b B))
    (hconst : 2 * (2 * q + 1) ^ (2 * q + 1) ≤ t)
    (hbank : bank.card + 1 ≤ c * t ^ bankPower)
    (hcoeff : absorberCrudeBankCoefficient q * c ^ (2 * q) ≤ t)
    (hgap : bankPower * (2 * q) + 1 ≤ aPower)
    (hk : k = dyadicCrudeExponent q aPower (5 * b + 2))
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hdegreeCoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t)
    (hdegreeSize : ∀ i, (t : ℝ) ^ (2 * ksssPowerErrorExponent b B + 2 * b + 3) ≤ ((sets i).card : ℝ))
    (hdegreeInitial : ∀ i v, |((uncoveredNeighbors Q₀ (sets i) v S₀).card : ℝ) - (sets i).card| ≤
      8 * ((sets i).card : ℝ) * t / (t : ℝ) ^ ksssPowerErrorExponent b B)
    (hU : ∀ i, (sets i).Nonempty) (hpattern₀ : ∀ j, PatternUncovered (patterns j) S₀)
    (req : ∀ j, KSSSPatternPowerRequirements q b B k Rmin
      (graphSupportFinset (patterns j)).card (graphEdges (patterns j)).card t coeff)
    (hpatternExponent : ∀ j, 2 * ksssPowerErrorExponent b B +
      (b * (graphSupportFinset (patterns j)).card + (graphEdges (patterns j)).card) + 2 * b + 1 ≤ r)
    (hpatternSize : ∀ i, (t : ℝ) ^ (r + 2) ≤ ((sets i).card : ℝ))
    (hpatternInitial : ∀ i j, |((properPatternExtensions S₀.available (patterns j) (sets i)).card : ℝ) - (sets i).card| ≤
      (sets i).card * (8 * (t : ℝ) ^ 2 / (t : ℝ) ^ ksssPowerErrorExponent b B))
    (hpatternCoefficient : ∀ j, 3 + ((graphEdges (patterns j)).card : ℝ) ≤ t)
    (houterBudget : (t : ℝ) ^ (r + k + 1) ≤ (Fintype.card V : ℝ))
    (hlocalSize : ∀ i, i ≠ i₀ → (45 * (q + 1) + 28 : ℕ) *
      (t : ℝ≥0) ^ ((r + 2) + q * (5 * b + 3) + 1) ≤ ((sets i).card : ℝ≥0))
    (hlocalBank : pairExactBankExtensionCoefficient q bank *
      (t : ℝ≥0) ^ ((r + 2) + q * (5 * b + 3) + 1) ≤ (Fintype.card V + 1 : ℝ≥0))
    (hlocalConst : 4 * (q + 1) ^ (q + 2) ≤ t)
    (hsmall : (2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) +
      2 * (Fintype.card I : ℝ) * Fintype.card V + 2 * (Fintype.card I : ℝ) * Fintype.card J +
      4 * (q + 1 : ℝ) ^ 2 * (Fintype.card V + 1 : ℝ) ^ 6 +
      (Fintype.card {i : I // i ≠ i₀} : ℝ) * (Fintype.card V : ℝ) ^ 5) * (1 / 2 : ℝ) ^ t < 1) :
    ∃ S : GreedyStateOn V, GreedyInvariant F S ∧ GreedyContainedIn S₀.available S ∧ S.chosen.card = n ∧
      KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B n ∧
      CrudeStateBounds F S q (dyadicCrudeThresholds V t k) ∧
      AllUncoveredNeighborBands sets Q₀ E t (ksssPowerErrorExponent b B) B n S ∧
      AllProperPatternBands sets patterns q a E t (ksssPowerErrorExponent b B) B n S := by
  obtain ⟨D⟩ := P.exists_pattern_stopped_law sets patterns i₀ houter Q₀ S₀ H bank X c bankPower aPower r eta
    hF hsep hrootLocal hInv₀ hchosen₀ hEcard hQ₀ hcover hregular hfamily heta hetaSmall hconst hbank hcoeff
    hgap hk hratio hdegreeCoefficient hdegreeSize hdegreeInitial hU hpattern₀ req hpatternExponent hpatternSize
    hpatternInitial hpatternCoefficient houterBudget hlocalSize hlocalBank hlocalConst
  let law := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) D.active S₀
  obtain ⟨w, hw, htime, ha, _⟩ := FiniteLaw.exists_timedStopped_horizon_of_two_failure_bounds n
    (fun _ ↦ greedyKernel F) D.active D.active (fun _ _ ↦ True) S₀ _ 0 D.failure
    (by simp only [not_true_eq_false, FiniteLaw.probability_false, NNReal.coe_zero, le_refl])
    (by simpa only [add_zero, ksssPatternFailureCoefficient] using hsmall)
    (fun _ _ ha _ ↦ ha)
  have hs := D.support w hw
  have hc := D.coupled w.1.1 w.2 ha
  refine ⟨w.2, hs.1.1, hs.1.2, hs.2.trans htime, ?_, hc.2.2.1, ?_, ?_⟩
  · simpa only [htime] using hc.2.1
  · simpa only [htime] using D.degree w.1.1 w.2 ha
  · simpa only [htime] using D.pattern w.1.1 w.2 ha

end

end Erdos207
