/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexScheduledGreedy
import ErdosProblems.Erdos207.VortexSweep

/-!
# Cyclic scheduling of all vortex levels

The cyclic schedule visits each of the `ell + 1` levels once per cycle.  Its
cumulative point hazard therefore has an exact closed form at every triangle.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Visit vortex levels periodically in their `Fin (ell+1)` order. -/
def vortexCyclicSchedule (ell : ℕ) (i : ℕ) : Fin (ell + 1) :=
  ⟨i % (ell + 1), Nat.mod_lt _ (Nat.succ_pos ell)⟩

@[simp]
theorem vortexCyclicSchedule_val (ell i : ℕ) :
    (vortexCyclicSchedule ell i).val = i % (ell + 1) := rfl

/-- The `k`th position in every complete cycle schedules level `k`. -/
theorem vortexCyclicSchedule_cycle_add
    {ell : ℕ} (a : ℕ) (k : Fin (ell + 1)) :
    vortexCyclicSchedule ell (a * (ell + 1) + k.val) = k := by
  apply Fin.ext
  simp only [vortexCyclicSchedule_val]
  rw [Nat.add_mod, Nat.mul_mod]
  simp [Nat.mod_eq_of_lt k.isLt]

/-- The total point hazard accumulated during one complete cycle. -/
theorem sum_cycle_scheduledVortexPointHazard
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (D : Fin (ell + 1) → ℕ)
    (a : ℕ) (T : TripleOn V) :
    ∑ i ∈ range (ell + 1),
        scheduledVortexPointHazard W (vortexCyclicSchedule ell) D
          (a * (ell + 1) + i) T =
      (D (W.level T) : ℝ≥0)⁻¹ := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [scheduledVortexPointHazard,
    vortexCyclicSchedule_cycle_add]
  simp

/-- Exact cumulative hazard after an integral number of cycles. -/
theorem cumulativePointHazard_vortexCyclicSchedule
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (D : Fin (ell + 1) → ℕ)
    (cycles : ℕ) (T : TripleOn V) :
    cumulativePointHazard
        (scheduledVortexPointHazard W (vortexCyclicSchedule ell) D)
        (cycles * (ell + 1)) T =
      (cycles : ℝ≥0) * (D (W.level T) : ℝ≥0)⁻¹ := by
  induction cycles with
  | zero => simp [cumulativePointHazard]
  | succ cycles ih =>
      unfold cumulativePointHazard at ih ⊢
      rw [Nat.succ_mul, sum_range_add, ih,
        sum_cycle_scheduledVortexPointHazard]
      push_cast
      ring

/-- A fixed level is visited exactly once per complete cycle. -/
theorem scheduledLevelVisits_vortexCyclicSchedule
    {ell : ℕ} (cycles : ℕ) (k : Fin (ell + 1)) :
    scheduledLevelVisits (vortexCyclicSchedule ell) k
        (cycles * (ell + 1)) = cycles := by
  rw [scheduledLevelVisits_eq_sum_indicator]
  induction cycles with
  | zero => simp
  | succ cycles ih =>
      rw [Nat.succ_mul, sum_range_add, ih]
      have hcycle :
          ∑ i ∈ range (ell + 1),
              (if vortexCyclicSchedule ell
                  (cycles * (ell + 1) + i) = k then 1 else 0) = 1 := by
        rw [← Fin.sum_univ_eq_sum_range]
        simp only [vortexCyclicSchedule_cycle_add]
        simp
      rw [hcycle]

/-- With the quadratic packing horizon as the number of cycles, every
positive-mass outcome is below every level threshold. -/
theorem cyclicVortexGreedy_supported_globalBound
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {F : ForbiddenFamilyOn V} {A : TripleSystemOn V} {W : Vortex V ell}
    {D : Fin (ell + 1) → ℕ} (hD : ∀ k, 0 < D k)
    {S₀ : GreedyStateOn V} (hS₀ : AbsorberGreedyInvariant F A S₀) :
    (scheduledStoppedVortexGreedyProcessLaw F W
      (vortexCyclicSchedule ell) D
      (vortexPackingSaturationFuel V * (ell + 1)) S₀).SupportedOn
        (fun S ↦ AbsorberGreedyInvariant F A S ∧
          S.available.card ≤ ∑ k, D k ∧ S.available ⊆ S₀.available) := by
  let cycles := vortexPackingSaturationFuel V
  let L := scheduledStoppedVortexGreedyProcessLaw F W
    (vortexCyclicSchedule ell) D (cycles * (ell + 1)) S₀
  have hInv :=
    scheduledStoppedVortexGreedyProcessLaw_supported_absorberInvariant
      (W := W) (schedule := vortexCyclicSchedule ell) (D := D) hS₀
        (cycles * (ell + 1))
  have hAvail :=
    scheduledStoppedVortexGreedyProcessLaw_supported_available_subset
      F W (vortexCyclicSchedule ell) D S₀ (cycles * (ell + 1))
  change L.SupportedOn _
  intro S hmass
  have hSInv := hInv S hmass
  have hSAvail := hAvail S hmass
  refine ⟨hSInv, ?_, hSAvail⟩
  rw [← W.sum_levelCount S.available]
  apply sum_le_sum
  intro k hk
  rw [← card_vortexLevelAvailable W k S]
  have hprogress :=
    scheduledStoppedVortexGreedyProcessLaw_supported_levelProgress
      (W := W) (schedule := vortexCyclicSchedule ell) hD hS₀ k
        (cycles * (ell + 1)) S hmass
  rcases hprogress.2.2 with hsmall | hmany
  · exact Nat.le_of_lt hsmall
  · rw [scheduledLevelVisits_vortexCyclicSchedule] at hmany
    have hpacking := hSInv.1.1.six_mul_card_le
    unfold cycles vortexPackingSaturationFuel at hmany
    omega

/-- Joint inclusion for a complete cyclic sweep, under the natural
level-by-level reciprocal-threshold comparison. -/
theorem cyclicVortexGreedy_probability_subset_chosen_le_vortexWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (F : ForbiddenFamilyOn V) (W : Vortex V ell)
    (D : Fin (ell + 1) → ℕ) (hD : ∀ k, 0 < D k)
    (cycles : ℕ) (c : ℝ≥0)
    (hratio : ∀ k : Fin (ell + 1),
      (cycles : ℝ≥0) * (D k : ℝ≥0)⁻¹ ≤ c / (W.U k).card)
    (S : GreedyStateOn V) (U : TripleSystemOn V)
    (hdisjoint : Disjoint U S.chosen) :
    (scheduledStoppedVortexGreedyProcessLaw F W
        (vortexCyclicSchedule ell) D (cycles * (ell + 1)) S).probability
          (fun S' ↦ U ⊆ S'.chosen) ≤
      (U.card.factorial : ℝ≥0) * setWeight (vortexTripleWeight W c) U := by
  apply scheduledStoppedVortexGreedy_probability_subset_chosen_le_vortexWeight
    F W (vortexCyclicSchedule ell) D hD (cycles * (ell + 1)) c
      (fun T ↦ ?_) S U hdisjoint
  rw [cumulativePointHazard_vortexCyclicSchedule]
  exact hratio (W.level T)

end

end Erdos207
