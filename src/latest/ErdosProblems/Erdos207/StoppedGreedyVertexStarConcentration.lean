/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GreedyVertexStarTrajectory

/-!
# Stopped concentration for a greedy vertex-star trajectory

Given a deterministic lower bound on the conditional probability that the
next selected triangle contains a fixed vertex, the selected vertex star
dominates the corresponding cumulative trajectory up to an exponential
lower-tail error.  The stopping clock freezes together with the state, so the
statement remains valid when the regularity hypotheses are imposed only in
the active region.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

/-- Cumulative deterministic selection rate through time `i`. -/
def cumulativeGreedyRate (r : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ range i, r j

@[simp]
lemma cumulativeGreedyRate_zero (r : ℕ → ℝ) :
    cumulativeGreedyRate r 0 = 0 := by
  simp [cumulativeGreedyRate]

lemma cumulativeGreedyRate_succ (r : ℕ → ℝ) (i : ℕ) :
    cumulativeGreedyRate r (i + 1) = cumulativeGreedyRate r i + r i := by
  simpa [cumulativeGreedyRate] using Finset.sum_range_succ r i

/-- Deficit of the selected star relative to a deterministic cumulative
rate, normalized to vanish at the initial state. -/
def selectedStarDeficit
    {V : Type*} [DecidableEq V]
    (r : ℕ → ℝ) (v : V) (S₀ : GreedyStateOn V)
    (i : ℕ) (S : GreedyStateOn V) : ℝ :=
  cumulativeGreedyRate r i -
    (selectedStarCountReal v S - selectedStarCountReal v S₀)

@[simp]
lemma selectedStarDeficit_zero_initial
    {V : Type*} [DecidableEq V]
    (r : ℕ → ℝ) (v : V) (S₀ : GreedyStateOn V) :
    selectedStarDeficit r v S₀ 0 S₀ = 0 := by
  simp [selectedStarDeficit]

/-- Freedman-style terminal lower tail for a selected vertex star in a timed
stopped greedy process. -/
theorem probability_timedStoppedGreedy_selectedStar_deficit_ge_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (r : ℕ → ℝ) (v : V)
    (theta a : ℝ)
    (hInv₀ : GreedyInvariant F S₀)
    (havailable : ∀ i, i < n → ∀ S, GreedyInvariant F S →
      active i S → S.available.Nonempty)
    (hrnonneg : ∀ i, i < n → 0 ≤ r i)
    (hrone : ∀ i, i < n → r i ≤ 1)
    (hratio : ∀ i, i < n → ∀ S, GreedyInvariant F S →
      active i S →
        r i ≤ ((availableTriplesThrough S v).card : ℝ) /
          (S.available.card : ℝ))
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1) :
    (((FiniteLaw.timedStoppedProcessLaw n
        (fun _ ↦ greedyKernel F) active S₀).probability
      (fun z ↦ a ≤ selectedStarDeficit r v S₀ z.1.1 z.2) : ℝ)) ≤
      Real.exp (-theta * a + theta ^ 2 * (n : ℝ)) := by
  classical
  let obs : ℕ → GreedyStateOn V → ℝ :=
    fun i S ↦ selectedStarDeficit r v S₀ i S
  have hjump : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      ∀ S', 0 < (greedyKernel F S).mass S' →
        GreedyInvariant F S' → |obs (i + 1) S' - obs i S| ≤ 1 := by
    intro i hi S hInv hactive S' hmass _hInv'
    have hA := havailable i hi S hInv hactive
    have hinc := greedyKernel_selectedStar_increment_mem_zero_one
      F S hInv hA v hmass
    have hdelta : obs (i + 1) S' - obs i S =
        r i - (selectedStarCountReal v S' - selectedStarCountReal v S) := by
      simp only [obs, selectedStarDeficit, cumulativeGreedyRate_succ]
      ring
    rw [hdelta]
    rcases hinc with hzero | hone
    · rw [hzero, sub_zero, abs_of_nonneg (hrnonneg i hi)]
      exact hrone i hi
    · rw [hone, abs_of_nonpos (sub_nonpos.mpr (hrone i hi))]
      linarith [hrnonneg i hi]
  have hdrift : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      (greedyKernel F S).expectationReal
        (fun S' ↦ obs (i + 1) S' - obs i S) ≤ 0 := by
    intro i hi S hInv hactive
    have hA := havailable i hi S hInv hactive
    calc
      (greedyKernel F S).expectationReal
          (fun S' ↦ obs (i + 1) S' - obs i S) =
          (greedyKernel F S).expectationReal
            (fun S' ↦ r i -
              (selectedStarCountReal v S' - selectedStarCountReal v S)) := by
        congr 1
        funext S'
        simp only [obs, selectedStarDeficit, cumulativeGreedyRate_succ]
        ring
      _ = r i - (greedyKernel F S).expectationReal
          (fun S' ↦ selectedStarCountReal v S' -
            selectedStarCountReal v S) := by
        rw [FiniteLaw.expectationReal_sub, FiniteLaw.expectationReal_const]
      _ = r i - ((availableTriplesThrough S v).card : ℝ) /
          (S.available.card : ℝ) := by
        rw [greedyKernel_expectationReal_selectedStar_increment
          F S hInv hA v]
      _ ≤ 0 := sub_nonpos.mpr (hratio i hi S hInv hactive)
  have hsecond : ∀ i, i < n → ∀ S, GreedyInvariant F S → active i S →
      (greedyKernel F S).expectationReal
        (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤ 1 := by
    intro i hi S hInv hactive
    calc
      (greedyKernel F S).expectationReal
          (fun S' ↦ (obs (i + 1) S' - obs i S) ^ 2) ≤
          (greedyKernel F S).expectationReal (fun _ ↦ (1 : ℝ)) := by
        refine FiniteLaw.expectationReal_mono_of_supported
          (greedyKernel F S)
          (P := fun S' ↦ 0 < (greedyKernel F S).mass S')
          (fun _ hmass ↦ hmass) ?_
        intro S' hmass
        have hInv' := greedyKernel_supported hInv S' hmass
        have habs := hjump i hi S hInv hactive S' hmass hInv'
        have habs0 : 0 ≤ |obs (i + 1) S' - obs i S| := abs_nonneg _
        have hsquare : |obs (i + 1) S' - obs i S| ^ 2 ≤ 1 := by
          nlinarith
        simpa [sq_abs] using hsquare
      _ = 1 := FiniteLaw.expectationReal_const _ _
  have htail := FiniteLaw.probability_timedStoppedProcess_deviation_ge_le_exp
    (P := GreedyInvariant F) n (fun _ ↦ greedyKernel F) active obs S₀
    theta 1 a 1 hInv₀ htheta (by norm_num)
    (by simpa using hthetaOne) (by norm_num)
    (fun _i _hi S hInv ↦ greedyKernel_supported hInv)
    (fun i hi S hInv hactive S' hmass hInv' ↦
      (le_abs_self _).trans (hjump i hi S hInv hactive S' hmass hInv'))
    hdrift hsecond
  simpa [obs, selectedStarDeficit_zero_initial] using htail

end

end Erdos207
