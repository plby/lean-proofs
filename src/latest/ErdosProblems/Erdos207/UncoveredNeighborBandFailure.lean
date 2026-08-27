/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UncoveredNeighborPowerTail
import ErdosProblems.Erdos207.IndexedBandFailure

/-! # Simultaneous degree bands for a prescribed finite family of vertex sets -/

namespace Erdos207

open Finset

noncomputable section

def AllUncoveredNeighborBands
    {I V : Type*} [Fintype V] [DecidableEq V]
    (sets : I → Finset V) (Q : Finset (Finset V)) (E t : ℝ) (s B : ℕ)
    (time : ℝ) (S : GreedyStateOn V) : Prop :=
  ∀ i v, |((uncoveredNeighbors Q (sets i) v S).card : ℝ) - uncoveredNeighborTarget E (sets i).card time| ≤
    uncoveredNeighborErrorEnvelope E (sets i).card t s B time

theorem uncoveredNeighbor_initial_margin
    {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset (Finset V)) (U : Finset V) (v : V) (S₀ : GreedyStateOn V)
    (E t : ℝ) (s B : ℕ) (hE : E ≠ 0)
    (hinitial : |((uncoveredNeighbors Q U v S₀).card : ℝ) - U.card| ≤ 8 * (U.card : ℝ) * t / t ^ s) :
    |((uncoveredNeighbors Q U v S₀).card : ℝ) - uncoveredNeighborTarget E U.card 0| +
      8 * (U.card : ℝ) * t / t ^ s ≤ uncoveredNeighborErrorEnvelope E U.card t s B 0 := by
  simp only [uncoveredNeighborTarget, uncoveredNeighborErrorEnvelope,
    ksssEdgeDensity_zero E hE, mul_one, ksssErrorEnvelope_zero E _ _ hE]
  calc
    _ ≤ 8 * (U.card : ℝ) * t / t ^ s + 8 * (U.card : ℝ) * t / t ^ s := add_le_add hinitial le_rfl
    _ = _ := by ring

theorem KSSSPowerParameters.uncovered_neighbor_bands_failure
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q n b B k t Rmin : ℕ} {a coeff : ℕ → ℝ} {E A : ℝ}
    (P : KSSSPowerParameters F q n b B k t Rmin a coeff E A)
    (sets : I → Finset V) (Q₀ : Finset (Finset V)) (S₀ : GreedyStateOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (hactive : ∀ i S, active i S → KSSSPowerActive F Q₀ q b B k t a E A i S)
    (hInv₀ : GreedyInvariant F S₀)
    (hratio : (Fintype.card V : ℝ) / 6 ≤ A / E)
    (hcoefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t)
    (hsize : ∀ j, (t : ℝ) ^ (2 * ksssPowerErrorExponent b B + 2 * b + 3) ≤ ((sets j).card : ℝ))
    (hinitial : ∀ j v, |((uncoveredNeighbors Q₀ (sets j) v S₀).card : ℝ) - (sets j).card| ≤
      8 * ((sets j).card : ℝ) * t / (t : ℝ) ^ ksssPowerErrorExponent b B)
    (hband : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      AllUncoveredNeighborBands sets Q₀ E t (ksssPowerErrorExponent b B) B i S) :
    ((FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).probability
      (fun w ↦ ¬ AllUncoveredNeighborBands sets Q₀ E t (ksssPowerErrorExponent b B) B w.1.1 w.2) : ℝ) ≤
      2 * (Fintype.card I : ℝ) * Fintype.card V * (1 / 2 : ℝ) ^ t := by
  classical
  let L := FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀
  let s := ksssPowerErrorExponent b B
  let y := fun j : I × V ↦ fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦
    ((uncoveredNeighbors Q₀ (sets j.1) j.2 w.2).card : ℝ) - uncoveredNeighborTarget E (sets j.1).card w.1.1
  let z := fun j : I × V ↦ fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦
    uncoveredNeighborErrorEnvelope E (sets j.1).card t s B w.1.1
  let y₀ := fun j : I × V ↦ ((uncoveredNeighbors Q₀ (sets j.1) j.2 S₀).card : ℝ) -
    uncoveredNeighborTarget E (sets j.1).card 0
  let z₀ := fun j : I × V ↦ uncoveredNeighborErrorEnvelope E (sets j.1).card t s B 0
  let margin := fun j : I × V ↦ 8 * ((sets j.1).card : ℝ) * t / (t : ℝ) ^ s
  let epsilon : ℝ := (1 / 2 : ℝ) ^ t
  have hmargin : ∀ j w, 0 < L.mass w → True → |y₀ j| + margin j ≤ z₀ j := by
    intro j _ _ _
    exact uncoveredNeighbor_initial_margin Q₀ (sets j.1) j.2 S₀ E t s B P.edge_pos.ne' (hinitial j.1 j.2)
  have hplus : ∀ j, (L.probability (fun w ↦ True ∧ margin j ≤ (y j w - z j w) - (y₀ j - z₀ j)) : ℝ) ≤ epsilon := by
    intro j
    have hp := P.uncovered_neighbor_power_tail Q₀ S₀ active hactive hInv₀ hratio hcoefficient
      (sets j.1) j.2 1 (by norm_num) (hsize j.1) (fun i hi S hS ha ↦ hband i hi S hS ha j.1 j.2)
    simpa only [L, y, z, y₀, z₀, margin, epsilon, true_and, uncoveredNeighborCenteredObservable, one_mul] using hp
  have hminus : ∀ j, (L.probability (fun w ↦ True ∧ margin j ≤ (-y j w - z j w) - (-y₀ j - z₀ j)) : ℝ) ≤ epsilon := by
    intro j
    have hm := P.uncovered_neighbor_power_tail Q₀ S₀ active hactive hInv₀ hratio hcoefficient
      (sets j.1) j.2 (-1) (by norm_num) (hsize j.1) (fun i hi S hS ha ↦ hband i hi S hS ha j.1 j.2)
    simpa only [L, y, z, y₀, z₀, margin, epsilon, true_and, uncoveredNeighborCenteredObservable, neg_one_mul] using hm
  have heq : (fun w : FiniteLaw.TimedState (GreedyStateOn V) n ↦
      ¬ AllUncoveredNeighborBands sets Q₀ E t s B w.1.1 w.2) =
      (fun w ↦ ∃ j : I × V, True ∧ z j w < |y j w|) := by
    funext w
    simp only [AllUncoveredNeighborBands, not_forall, not_le, Prod.exists, true_and, y, z]
  rw [heq]
  calc
    _ ≤ ∑ _j : I × V, (epsilon + epsilon) :=
      probability_indexed_band_failure_le_two_tails L (fun _ _ ↦ True) y z y₀ z₀ margin
        (fun _ ↦ epsilon) (fun _ ↦ epsilon) hmargin hplus hminus
    _ = _ := by simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod, Nat.cast_mul, epsilon]; ring

end

end Erdos207
