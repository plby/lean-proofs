/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSDegreeHorizon
import ErdosProblems.Erdos207.KSSSPatternBandsFailure
import ErdosProblems.Erdos207.KSSSLocalizedTwoAwayTail
import ErdosProblems.Erdos207.CombinedPatternLossSchedule
import ErdosProblems.Erdos207.FiniteFailureCombination

/-! # The common stopped law carrying coupled, degree, and relative pattern events -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def ksssPatternFailureCoefficient (q N levels patterns inner : ℕ) : ℝ :=
  2 * ((N : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (N : ℝ) ^ 3) +
    2 * (levels : ℝ) * N + 2 * (levels : ℝ) * patterns +
    4 * (q + 1 : ℝ) ^ 2 * (N + 1 : ℝ) ^ 6 + (inner : ℝ) * (N : ℝ) ^ 5

structure KSSSPatternStoppedLawData
    {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (Q₀ : Finset (Finset V)) (q n b B k t : ℕ)
    (a : ℕ → ℝ) (E A : ℝ) (S₀ : GreedyStateOn V)
    (sets : I → Finset V) (patterns : J → SimpleGraph V) (i₀ : I) where
  active : ℕ → GreedyStateOn V → Prop
  coupled : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S
  degree : ∀ i S, active i S → AllUncoveredNeighborBands sets Q₀ E t (ksssPowerErrorExponent b B) B i S
  pattern : ∀ i S, active i S →
    AllProperPatternBands sets patterns q a E t (ksssPowerErrorExponent b B) B i S
  support : (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
    (fun w ↦ (GreedyInvariant F w.2 ∧ GreedyContainedIn S₀.available w.2) ∧ w.2.chosen.card = w.1.1)
  failure : ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
    (fun w ↦ ¬ active w.1.1 w.2) : ℝ) ≤
    ksssPatternFailureCoefficient q (Fintype.card V) (Fintype.card I) (Fintype.card J)
      (Fintype.card {i : I // i ≠ i₀}) * (1 / 2 : ℝ) ^ t

theorem KSSSPowerParameters.exists_pattern_stopped_law
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
    : Nonempty (KSSSPatternStoppedLawData F Q₀ q n b B k t a E A S₀ sets patterns i₀) := by
  classical
  let s := ksssPowerErrorExponent b B
  let trajectory := fun i : ℕ ↦ fun S : GreedyStateOn V ↦
    KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A ((Fintype.card V : ℝ) / (t : ℝ) ^ s) B i
  let degree := fun i : ℕ ↦ AllUncoveredNeighborBands sets Q₀ E t s B (i : ℝ)
  let pattern := fun i : ℕ ↦ AllProperPatternBands sets patterns q a E t s B (i : ℝ)
  let localSets := fun j : {i : I // i ≠ i₀} ↦ sets j.1
  let localized := fun S ↦ AllLocalizedTwoAwayBounds F localSets
    (fun j ↦ ((localSets j).card : ℝ≥0) / (t : ℝ≥0) ^ (r + 2)) S
  let active := fun i S ↦ KSSSPowerActive F Q₀ q b B k t a E A i S ∧ degree i S ∧ pattern i S ∧ localized S
  let band := fun i S ↦ trajectory i S ∧ degree i S ∧ pattern i S
  let crude := fun _ : ℕ ↦ fun S ↦ CrudeStateBounds F S q (dyadicCrudeThresholds V t k) ∧ localized S
  let law := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let cutoff := fun i ↦ ((sets i).card : ℝ) / (t : ℝ) ^ r
  let eps := (1 / 2 : ℝ) ^ t
  have hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S := fun _ _ h ↦ h.1
  have ht : 1 ≤ t := by linarith [P.scale_large]
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hsizeR : ∀ i, (t : ℝ) ^ r ≤ ((sets i).card : ℝ) := fun i ↦
    (pow_le_pow_right₀ htR (by omega : r ≤ r + 2)).trans (hpatternSize i)
  have hcutoff : ∀ i, 1 ≤ cutoff i := fun i ↦
    (relative_cutoff_concentration_size (sets i).card t r r htR (Nat.cast_nonneg _) (hsizeR i) le_rfl).1
  have hconcentrationSize : ∀ i j, cutoff i * (t : ℝ) ^ (2 * s +
      (b * (graphSupportFinset (patterns j)).card + (graphEdges (patterns j)).card) + 2 * b + 1) ≤ ((sets i).card : ℝ) :=
    fun i j ↦ (relative_cutoff_concentration_size (sets i).card t r _ htR (Nat.cast_nonneg _)
      (hsizeR i) (hpatternExponent j)).2
  have hLoss : ∀ time, time < n → ∀ S, GreedyInvariant F S → active time S →
      ∀ i j, PatternUncovered (patterns j) S → ∀ T ∈ patternSurvivalSelectors (patterns j) S,
        ((patternExtensionLoss F (patterns j) (sets i) S T).card : ℝ) ≤ cutoff i := by
    intro time _ S hS ha i j _ T hT
    exact combined_pattern_loss_relative_schedule hS P.packing ha.1.2.2.1 sets i₀ houter r ha.2.2.2
      ht hpatternSize houterBudget (patterns j) (hpatternCoefficient j) i T hT
  have havailable := (P.kernelBounds Q₀ 1 (by norm_num)).available
  have havailable' : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty :=
    fun i hi S hS ha ↦ havailable i hi S hS ha.1
  have hgeometry := timedStoppedGreedy_supported_residualGeometry n F active S₀ Q₀ E
    hInv₀ hchosen₀ P.edge_pos hEcard hQ₀ hcover havailable'
  have hcounter := timedStoppedGreedy_supported_contained_counter n F active S₀ hInv₀ hchosen₀ havailable'
  have htrajectory := P.trajectory_failure_of_active_le Q₀ S₀ eta active hactive
    hInv₀ hchosen₀ hQ₀ hregular hfamily heta hetaSmall
  have hdegree := P.uncovered_neighbor_bands_failure sets Q₀ S₀ active hactive hInv₀ hratio
    hdegreeCoefficient hdegreeSize hdegreeInitial (fun _ _ _ _ ha ↦ ha.2.1)
  have hpattern := P.pattern_relative_bands_failure Q₀ S₀ sets patterns cutoff active hactive hInv₀ hpattern₀ hU hcutoff
    req hratio hconcentrationSize hpatternInitial (fun _ _ _ _ ha ↦ ha.2.2.1) hLoss
  have hcrude := P.crude_failure_of_active_le Q₀ S₀ bank active hactive c bankPower aPower
    hF hInv₀ hchosen₀ hconst hbank hcoeff hgap hk
  have hlocal := P.localized_twoAway_failure Q₀ S₀ active hactive H bank X localSets (r + 2) hF
    (fun j ↦ hsep j.1 j.2) hrootLocal hInv₀ hchosen₀ (fun j ↦ hU j.1)
    (fun j ↦ hlocalSize j.1 j.2) hlocalBank hlocalConst
  have hband : (law.probability (fun w ↦ ¬ band w.1.1 w.2) : ℝ) ≤
      (2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) +
        2 * (Fintype.card I : ℝ) * Fintype.card V + 2 * (Fintype.card I : ℝ) * Fintype.card J) * eps := by
    have hdp := finiteLaw_failure_and_le law (fun w ↦ degree w.1.1 w.2) (fun w ↦ pattern w.1.1 w.2)
      _ _ hdegree hpattern
    have hall := finiteLaw_failure_and_le law (fun w ↦ trajectory w.1.1 w.2)
      (fun w ↦ degree w.1.1 w.2 ∧ pattern w.1.1 w.2) _ _ htrajectory hdp
    exact hall.trans_eq (by dsimp only [eps]; ring)
  have hcrudes : (law.probability (fun w ↦ ¬ crude w.1.1 w.2) : ℝ) ≤
      (4 * (q + 1 : ℝ) ^ 2 * (Fintype.card V + 1 : ℝ) ^ 6 +
        (Fintype.card {i : I // i ≠ i₀} : ℝ) * (Fintype.card V : ℝ) ^ 5) * eps := by
    have hall := finiteLaw_failure_and_le law (fun w ↦ CrudeStateBounds F w.2 q (dyadicCrudeThresholds V t k))
      (fun w ↦ localized w.2) _ _ hcrude hlocal
    exact hall.trans_eq (by dsimp only [eps]; ring)
  refine ⟨⟨active, hactive, (fun _ _ ha ↦ ha.2.1), (fun _ _ ha ↦ ha.2.2.1), hcounter, ?_⟩⟩
  have hcompare : law.probability (fun w ↦ ¬ active w.1.1 w.2) ≤
      law.probability (fun w ↦ ¬ (band w.1.1 w.2 ∧ crude w.1.1 w.2)) := by
    apply law.probability_mono_of_supported hgeometry
    intro w hg hnot hgood
    exact hnot ⟨⟨hg, hgood.1.1, hgood.2.1,
      P.density_floor w.1.1 (Nat.le_of_lt_succ w.1.isLt)⟩,
      hgood.1.2.1, hgood.1.2.2, hgood.2.2⟩
  have hcompareR : (law.probability (fun w ↦ ¬ active w.1.1 w.2) : ℝ) ≤
      (law.probability (fun w ↦ ¬ (band w.1.1 w.2 ∧ crude w.1.1 w.2)) : ℝ) := by exact_mod_cast hcompare
  have hcombined := finiteLaw_failure_and_le law (fun w ↦ band w.1.1 w.2)
    (fun w ↦ crude w.1.1 w.2) _ _ hband hcrudes
  exact (hcompareR.trans hcombined).trans_eq (by dsimp only [ksssPatternFailureCoefficient, eps]; ring)

end

end Erdos207
