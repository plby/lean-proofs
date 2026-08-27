/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteHypergraphDegrees

/-! # A finite union bound for the maximum hypergraph degree -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem finiteHypergraphMaxDegree_ge_iff
    {I : Type*} [Fintype I] [DecidableEq I] (G : Finset (Finset I)) (K : ℝ≥0) (hK : 0 < K) :
    K ≤ (finiteHypergraphMaxDegree G : ℝ≥0) ↔ ∃ v, K ≤ (finiteHypergraphDegree G v : ℝ≥0) := by
  constructor
  · intro h
    by_cases hne : (univ : Finset I).Nonempty
    · obtain ⟨v, _hv, heq⟩ := exists_mem_eq_sup univ hne (finiteHypergraphDegree G)
      exact ⟨v, by simpa only [finiteHypergraphMaxDegree, heq] using h⟩
    · have hz : (univ : Finset I) = ∅ := not_nonempty_iff_eq_empty.mp hne
      have hzero : finiteHypergraphMaxDegree G = 0 := by simp [finiteHypergraphMaxDegree, hz]
      rw [hzero, Nat.cast_zero] at h
      exact ((not_le_of_gt hK) h).elim
  · rintro ⟨v, hv⟩
    exact hv.trans (by exact_mod_cast finiteHypergraphDegree_le_max G v)

theorem finiteHypergraphMaxDegree_probability_le
    {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (L : FiniteLaw Ω) (G : Ω → Finset (Finset I)) (K epsilon : ℝ≥0) (hK : 0 < K)
    (hpoint : ∀ v, L.probability (fun ω ↦ K ≤ (finiteHypergraphDegree (G ω) v : ℝ≥0)) ≤ epsilon) :
    L.probability (fun ω ↦ K ≤ (finiteHypergraphMaxDegree (G ω) : ℝ≥0)) ≤
      Fintype.card I * epsilon := by
  classical
  calc
    _ ≤ L.probability (fun ω ↦ ∃ v ∈ (univ : Finset I), K ≤ (finiteHypergraphDegree (G ω) v : ℝ≥0)) := by
      apply L.probability_mono
      intro ω hω
      obtain ⟨v, hv⟩ := (finiteHypergraphMaxDegree_ge_iff (G ω) K hK).mp hω
      exact ⟨v, mem_univ v, hv⟩
    _ ≤ ∑ v : I, L.probability (fun ω ↦ K ≤ (finiteHypergraphDegree (G ω) v : ℝ≥0)) :=
      L.probability_exists_le univ (fun v ω ↦ K ≤ (finiteHypergraphDegree (G ω) v : ℝ≥0))
    _ ≤ ∑ _v : I, epsilon := sum_le_sum (fun v _ ↦ hpoint v)
    _ = _ := by simp

end

end Erdos207
