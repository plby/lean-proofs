/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternPowerTail
import ErdosProblems.Erdos207.InitialPatternMargins
import ErdosProblems.Erdos207.IndexedBandFailure

/-! # Simultaneous two-sided relative extension bands for fixed sets and patterns -/

namespace Erdos207

open Finset

noncomputable section

def AllProperPatternBands
    {I J V : Type*} [Fintype V] [DecidableEq V]
    (sets : I → Finset V) (patterns : J → SimpleGraph V)
    (q : ℕ) (a : ℕ → ℝ) (E t : ℝ) (s B : ℕ) (time : ℝ) (S : GreedyStateOn V) : Prop :=
  ∀ i j, PatternUncovered (patterns j) S →
    |properPatternRelativeCount (patterns j) (sets i)
        (ksssPatternTrajectory (ksssOrders q) a E (sets i).card
          (graphSupportFinset (patterns j)).card (graphEdges (patterns j)).card time) S - 1| ≤
      relativePatternEnvelope E t s B time

theorem relative_pattern_band_count_upper
    (Y f z : ℝ) (hf : 0 < f) (hband : |Y / f - 1| ≤ z) (hz : z ≤ 1) : Y ≤ 2 * f := by
  apply (div_le_iff₀ hf).mp
  have h := (abs_le.mp hband).2
  linarith only [h, hz]

theorem relativePatternEnvelope_le_one
    (E t time : ℝ) (b B : ℕ) (ht : 16 ≤ t) (hb : 1 ≤ b)
    (hfloor : 1 / t ^ b ≤ ksssEdgeDensity E time) :
    relativePatternEnvelope E t (ksssPowerErrorExponent b B) B time ≤ 1 := by
  have htpos : 0 < t := by linarith
  have hpower : t ≤ t ^ b := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ t) hb
  calc
    _ ≤ 16 / t ^ b := relativePatternEnvelope_terminal_bound E t time b B htpos hfloor
    _ ≤ 1 := (div_le_one (pow_pos htpos b)).mpr (ht.trans hpower)

theorem KSSSPowerParameters.pattern_relative_bands_failure
    {I J V : Type*} [Fintype I] [Fintype J] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V)
    (sets : I → Finset V) (patterns : J → SimpleGraph V) (cutoff : I → ℝ)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀) (hQ₀ : ∀ j, PatternUncovered (patterns j) S₀)
    (hU : ∀ i, (sets i).Nonempty) (hcutoff : ∀ i, 1 ≤ cutoff i)
    (req : ∀ j, KSSSPatternPowerRequirements q b B k Rmin
      (graphSupportFinset (patterns j)).card (graphEdges (patterns j)).card t coeff)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hsize : ∀ i j, cutoff i * (t : ℝ) ^ (2 * ksssPowerErrorExponent b B +
      (b * (graphSupportFinset (patterns j)).card + (graphEdges (patterns j)).card) + 2 * b + 1) ≤ ((sets i).card : ℝ))
    (hinitial : ∀ i j, |((properPatternExtensions S₀.available (patterns j) (sets i)).card : ℝ) - (sets i).card| ≤
      (sets i).card * (8 * (t : ℝ) ^ 2 / (t : ℝ) ^ ksssPowerErrorExponent b B))
    (hband : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      AllProperPatternBands sets patterns q a E t (ksssPowerErrorExponent b B) B i S)
    (hLoss : ∀ time, time < n → ∀ S, GreedyInvariant F S → active time S →
      ∀ i j, PatternUncovered (patterns j) S → ∀ T ∈ patternSurvivalSelectors (patterns j) S,
        ((patternExtensionLoss F (patterns j) (sets i) S T).card : ℝ) ≤ cutoff i) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ ¬ AllProperPatternBands sets patterns q a E t (ksssPowerErrorExponent b B) B z.1.1 z.2) : ℝ) ≤
      2 * (Fintype.card I : ℝ) * Fintype.card J * (1 / 2 : ℝ) ^ t := by
  classical
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let s := ksssPowerErrorExponent b B
  let tracked := fun j : I × J ↦ fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦ PatternUncovered (patterns j.2) z.2
  let y := fun j : I × J ↦ fun z : FiniteLaw.TimedState (GreedyStateOn V) n ↦
    properPatternRelativeCount (patterns j.2) (sets j.1)
      (ksssPatternTrajectory (ksssOrders q) a E (sets j.1).card
        (graphSupportFinset (patterns j.2)).card (graphEdges (patterns j.2)).card z.1.1) z.2 - 1
  let z := fun _j : I × J ↦ fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦ relativePatternEnvelope E t s B w.1.1
  let y₀ := fun j : I × J ↦ properPatternRelativeCount (patterns j.2) (sets j.1)
    (ksssPatternTrajectory (ksssOrders q) a E (sets j.1).card
      (graphSupportFinset (patterns j.2)).card (graphEdges (patterns j.2)).card 0) S₀ - 1
  let z₀ := fun _j : I × J ↦ relativePatternEnvelope E t s B 0
  let margin := fun _j : I × J ↦ 8 * (t : ℝ) ^ 2 / (t : ℝ) ^ s
  let epsilon : ℝ := (1 / 2 : ℝ) ^ t
  have hupper : ∀ j : I × J, ∀ time, time < n → ∀ S, GreedyInvariant F S → active time S →
      PatternUncovered (patterns j.2) S →
      ((properPatternExtensions S.available (patterns j.2) (sets j.1)).card : ℝ) ≤
        2 * ksssPatternTrajectory (ksssOrders q) a E (sets j.1).card
          (graphSupportFinset (patterns j.2)).card (graphEdges (patterns j.2)).card time := by
    intro j time htime S hS ha hQ
    have hs := hactive time S ha
    have hscalar := P.scalar_bounds time (Nat.cast_nonneg _) hs.2.2.2
    have hM : (0 : ℝ) < (sets j.1).card := by exact_mod_cast card_pos.mpr (hU j.1)
    have hf := ksssPatternTrajectory_pos (ksssOrders q) a E (sets j.1).card time
      (graphSupportFinset (patterns j.2)).card (graphEdges (patterns j.2)).card hM
      (ksssEdgeDensity_pos P.edge_pos hscalar.clock_strict)
    exact relative_pattern_band_count_upper _ _ _ hf (hband time htime S hS ha j.1 j.2 hQ)
      (relativePatternEnvelope_le_one E t time b B (by exact_mod_cast (show 16 ≤ t by linarith [P.scale_large]))
        (req j.2).density_exponent hs.2.2.2)
  have hmargin : ∀ j w, 0 < L.mass w → tracked j w → |y₀ j| + margin j ≤ z₀ j := by
    intro j _ _ _
    exact initial_relative_pattern_margin q a E t s B (patterns j.2) (sets j.1) S₀ P.edge_pos.ne'
      (hU j.1) (hinitial j.1 j.2)
  have hplus : ∀ j, (L.probability (fun w ↦ tracked j w ∧ margin j ≤
      (y j w - z j w) - (y₀ j - z₀ j)) : ℝ) ≤ epsilon := by
    intro j
    have hp := P.pattern_relative_power_tail Q₀ S₀ (patterns j.2) (sets j.1) (hU j.1) active hactive
      hInv₀ (hQ₀ j.2) (req j.2) hratio 1 (cutoff j.1) (by norm_num) (hcutoff j.1) (hsize j.1 j.2)
      (hupper j) (fun time hi S hS ha hQ ↦ hLoss time hi S hS ha j.1 j.2 hQ)
    simpa only [L, y, z, y₀, z₀, tracked, margin, epsilon, patternRelativeCenteredObservable, one_mul] using hp
  have hminus : ∀ j, (L.probability (fun w ↦ tracked j w ∧ margin j ≤
      (-y j w - z j w) - (-y₀ j - z₀ j)) : ℝ) ≤ epsilon := by
    intro j
    have hm := P.pattern_relative_power_tail Q₀ S₀ (patterns j.2) (sets j.1) (hU j.1) active hactive
      hInv₀ (hQ₀ j.2) (req j.2) hratio (-1) (cutoff j.1) (by norm_num) (hcutoff j.1) (hsize j.1 j.2)
      (hupper j) (fun time hi S hS ha hQ ↦ hLoss time hi S hS ha j.1 j.2 hQ)
    simpa only [L, y, z, y₀, z₀, tracked, margin, epsilon, patternRelativeCenteredObservable, neg_one_mul] using hm
  have heq : (fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      ¬ AllProperPatternBands sets patterns q a E t s B w.1.1 w.2) =
      (fun w ↦ ∃ j : I × J, tracked j w ∧ z j w < |y j w|) := by
    funext w
    simp only [AllProperPatternBands, not_forall, not_le, Prod.exists, exists_prop, tracked, y, z]
  rw [heq]
  calc
    _ ≤ ∑ _j : I × J, (epsilon + epsilon) := probability_indexed_band_failure_le_two_tails L
      tracked y z y₀ z₀ margin (fun _ ↦ epsilon) (fun _ ↦ epsilon) hmargin hplus hminus
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod, Nat.cast_mul, epsilon]; ring

end

end Erdos207
