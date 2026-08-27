/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteLawKernelCalculus
import ErdosProblems.Erdos207.FiniteConditioning

/-! # Freezing a proposal seed by averaging over the entire original law -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

theorem map_mass_eq_probability
    {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (seed : Ω → R) (r : R) :
    (map seed L).mass r = L.probability (fun x ↦ seed x = r) := by
  rw [← probability_eq_mass, probability_map]

theorem sum_probability_fiber_and
    {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (seed : Ω → R) (Bad : Ω → Prop) :
    ∑ r, L.probability (fun x ↦ seed x = r ∧ Bad x) = L.probability Bad := by
  classical
  unfold probability
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_eq_single (seed x)]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

def fiberFailureRate
    {Ω R : Type*} [Fintype Ω] [Fintype R]
    (L : FiniteLaw Ω) (seed : Ω → R) (Bad : Ω → Prop) (r : R) : ℝ≥0 :=
  L.probability (fun x ↦ seed x = r ∧ Bad x) /
    L.probability (fun x ↦ seed x = r)

theorem expectation_fiberFailureRate
    {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (seed : Ω → R) (Bad : Ω → Prop) :
    (map seed L).expectation (fiberFailureRate L seed Bad) = L.probability Bad := by
  classical
  rw [← sum_probability_fiber_and L seed Bad]
  unfold expectation
  apply sum_congr rfl
  intro r _
  rw [map_mass_eq_probability]
  unfold fiberFailureRate
  by_cases hzero : L.probability (fun x ↦ seed x = r) = 0
  · have hnum : L.probability (fun x ↦ seed x = r ∧ Bad x) = 0 := by
      apply le_antisymm _ zero_le
      exact (L.probability_mono (fun _ h ↦ h.1)).trans_eq hzero
    simp [hzero, hnum]
  · exact mul_div_cancel₀ _ hzero

theorem exists_good_seed_with_small_conditional_failure
    {Ω R : Type*} [Fintype Ω] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (seed : Ω → R) (Bad : Ω → Prop) (GoodSeed : R → Prop)
    (epsilon eta delta : ℝ≥0) (hdelta : 0 < delta)
    (hbad : L.probability Bad ≤ epsilon)
    (hseed : (map seed L).probability (fun r ↦ ¬ GoodSeed r) ≤ eta)
    (hbudget : eta + epsilon / delta < 1) :
    ∃ r, ∃ hr : 0 < L.probability (fun x ↦ seed x = r),
      GoodSeed r ∧ (L.conditionOn (fun x ↦ seed x = r) hr).probability Bad < delta := by
  classical
  let Q := map seed L
  have hrate : Q.probability (fun r ↦ delta ≤ fiberFailureRate L seed Bad r) ≤ epsilon / delta := by
    apply (Q.probability_le_expectation_div (fiberFailureRate L seed Bad) hdelta).trans
    rw [expectation_fiberFailureRate]
    exact div_le_div_of_nonneg_right hbad zero_le
  have hfail : Q.probability (fun r ↦ ¬ GoodSeed r ∨ delta ≤ fiberFailureRate L seed Bad r) < 1 :=
    ((Q.probability_or_le _ _).trans (add_le_add hseed hrate)).trans_lt hbudget
  have hgood : 0 < Q.probability (fun r ↦ ¬ (¬ GoodSeed r ∨ delta ≤ fiberFailureRate L seed Bad r)) := by
    rw [probability_not]
    exact tsub_pos_iff_lt.mpr hfail
  obtain ⟨r, hr, hg⟩ := Q.exists_supported_of_probability_pos hgood
  have hr' : 0 < L.probability (fun x ↦ seed x = r) := by
    simpa only [Q, map_mass_eq_probability] using hr
  refine ⟨r, hr', not_not.mp (fun hn ↦ hg (Or.inl hn)), ?_⟩
  rw [conditionOn_probability]
  exact lt_of_not_ge (fun h ↦ hg (Or.inr h))

end

end Erdos207.FiniteLaw
