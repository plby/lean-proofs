/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborBandFailure
import ErdosProblems.Erdos207.KSSSRefinedStopping
import ErdosProblems.Erdos207.TimedStoppedTwoEventSuccess

/-! # Reaching the coupled horizon while preserving all prescribed degree bands -/

namespace Erdos207

open Finset

noncomputable section

theorem KSSSPowerParameters.exists_good_horizon_with_neighbor_bands
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (sets : I → Finset V) (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V) (bank : TripleSystemOn V)
    (c bankPower aPower : ℕ) (eta : ℝ)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q bank)
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
    (hsize : ∀ j, (t : ℝ) ^ (2 * ksssPowerErrorExponent b B + 2 * b + 3) ≤ ((sets j).card : ℝ))
    (hinitial : ∀ j v, |((uncoveredNeighbors Q₀ (sets j) v S₀).card : ℝ) - (sets j).card| ≤
      8 * ((sets j).card : ℝ) * t / (t : ℝ) ^ ksssPowerErrorExponent b B)
    (hsmall : (2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) +
      2 * (Fintype.card I : ℝ) * Fintype.card V +
      4 * (q + 1 : ℝ) ^ 2 * (Fintype.card V + 1 : ℝ) ^ 6) * (1 / 2 : ℝ) ^ t < 1) :
    ∃ S : GreedyStateOn V, GreedyInvariant F S ∧ GreedyContainedIn S₀.available S ∧
      S.chosen.card = n ∧
      KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
        ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B n ∧
      CrudeStateBounds F S q (dyadicCrudeThresholds V t k) ∧
      AllUncoveredNeighborBands sets Q₀ E t (ksssPowerErrorExponent b B) B n S := by
  classical
  let degree := fun i : ℕ ↦ AllUncoveredNeighborBands sets Q₀ E t (ksssPowerErrorExponent b B) B (i : ℝ)
  let trajectory := fun i : ℕ ↦ fun S : GreedyStateOn V ↦
    KSSSOnTrajectories F S q (ksssResidualPairs Q₀ S) a E A
      ((Fintype.card V : ℝ) / (t : ℝ) ^ ksssPowerErrorExponent b B) B i
  let active := fun i S ↦ KSSSPowerActive F Q₀ q b B k t a E A i S ∧ degree i S
  let band := fun i S ↦ trajectory i S ∧ degree i S
  let crude := fun _ : ℕ ↦ fun S : GreedyStateOn V ↦ CrudeStateBounds F S q (dyadicCrudeThresholds V t k)
  let law := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  have hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S := fun _ _ h ↦ h.1
  have havailable := (P.kernelBounds Q₀ 1 (by norm_num)).available
  have havailable' : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S → S.available.Nonempty :=
    fun i hi S hS ha ↦ havailable i hi S hS ha.1
  have hgeometry := timedStoppedGreedy_supported_residualGeometry n F active S₀ Q₀ E
    hInv₀ hchosen₀ P.edge_pos hEcard hQ₀ hcover havailable'
  have hcounter := timedStoppedGreedy_supported_contained_counter n F active S₀ hInv₀ hchosen₀ havailable'
  have htrajectory := P.trajectory_failure_of_active_le Q₀ S₀ eta active hactive
    hInv₀ hchosen₀ hQ₀ hregular hfamily heta hetaSmall
  have hdegree := P.uncovered_neighbor_bands_failure sets Q₀ S₀ active hactive hInv₀ hratio
    hdegreeCoefficient hsize hinitial (fun _ _ _ _ ha ↦ ha.2)
  have hcrude := P.crude_failure_of_active_le Q₀ S₀ bank active hactive c bankPower aPower
    hF hInv₀ hchosen₀ hconst hbank hcoeff hgap hk
  have hband : (law.probability (fun w ↦ ¬ band w.1.1 w.2) : ℝ) ≤
      (2 * ((Fintype.card V : ℝ) ^ 2 + (q + 1 : ℝ) ^ 2 * (Fintype.card V : ℝ) ^ 3) +
        2 * (Fintype.card I : ℝ) * Fintype.card V) * (1 / 2 : ℝ) ^ t := by
    have hor := law.probability_or_le (fun w ↦ ¬ trajectory w.1.1 w.2) (fun w ↦ ¬ degree w.1.1 w.2)
    have hmono := law.probability_mono (P := fun w ↦ ¬ band w.1.1 w.2)
      (Q := fun w ↦ (¬ trajectory w.1.1 w.2) ∨ (¬ degree w.1.1 w.2))
      (fun _ h ↦ not_and_or.mp h)
    have hsum : (law.probability (fun w ↦ ¬ band w.1.1 w.2) : ℝ) ≤
        (law.probability (fun w ↦ ¬ trajectory w.1.1 w.2) : ℝ) +
        (law.probability (fun w ↦ ¬ degree w.1.1 w.2) : ℝ) := by
      exact_mod_cast hmono.trans hor
    exact hsum.trans ((add_le_add htrajectory hdegree).trans_eq (by ring))
  obtain ⟨w, hw, htime, hbands, hcrudes⟩ :=
    FiniteLaw.exists_timedStopped_horizon_of_two_failure_bounds n (fun _ ↦ greedyKernel F)
      active band crude S₀ _ _ hband hcrude (by simpa only [add_mul] using hsmall)
      (fun w hw hb hc ↦ ⟨⟨hgeometry w hw, hb.1, hc,
        P.density_floor w.1.1 (Nat.le_of_lt_succ w.1.isLt)⟩, hb.2⟩)
  have hs := hcounter w hw
  refine ⟨w.2, hs.1.1, hs.1.2, hs.2.trans htime, ?_, hcrudes, ?_⟩
  · simpa only [trajectory, htime] using hbands.1
  · simpa only [degree, htime] using hbands.2

end

end Erdos207
