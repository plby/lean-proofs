/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberGreedy

/-!
# One-step probabilities for the constrained greedy process

This file computes the exact conditional probability with which one new
triangle is inserted by the uniform constrained-greedy kernel.  It is the
local input to the later trajectory and joint-inclusion estimates.
-/

namespace Erdos207

open Finset
open scoped NNReal

/-- If `T` has not already been chosen, its one-step inclusion probability
is the reciprocal of the current availability cardinality when it is
available, and zero otherwise. -/
theorem greedyKernel_probability_new_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (hTnot : T ∉ S.chosen) :
    (greedyKernel F S).probability (fun S' ↦ T ∈ S'.chosen) =
      if T ∈ S.available then (S.available.card : ℝ≥0)⁻¹ else 0 := by
  classical
  by_cases hnonempty : S.available.Nonempty
  · let : Nonempty S.available :=
      ⟨⟨hnonempty.choose, hnonempty.choose_spec⟩⟩
    let next : S.available → GreedyStateOn V :=
      fun U ↦ greedyStep F S U.1
    simp only [greedyKernel, hnonempty]
    change (FiniteLaw.map next
      (FiniteLaw.uniform : FiniteLaw S.available)).probability
        (fun S' ↦ T ∈ S'.chosen) = _
    rw [FiniteLaw.probability_map]
    by_cases hT : T ∈ S.available
    · simp only [if_pos hT]
      let T₀ : S.available := ⟨T, hT⟩
      have hunique : ∀ U : S.available,
          T ∈ (next U).chosen ↔ U = T₀ := by
        intro U
        simp only [next, greedyStep, mem_insert]
        constructor
        · intro h
          rcases h with hTU | hTC
          · apply Subtype.ext
            exact hTU.symm
          · exact (hTnot hTC).elim
        · intro h
          subst U
          exact Or.inl rfl
      have hu := @FiniteLaw.uniform_probability_unique S.available _ inferInstance
        (fun U ↦ T ∈ (next U).chosen) T₀ hunique
      simpa using hu
    · simp only [if_neg hT]
      have hfalse : (fun U : S.available ↦ T ∈ (next U).chosen) =
          (fun _ ↦ False) := by
        funext U
        apply propext
        constructor
        · intro h
          simp only [next, greedyStep, mem_insert] at h
          rcases h with hTU | hTC
          · exact hT (hTU ▸ U.2)
          · exact hTnot hTC
        · intro h
          exact h.elim
      rw [hfalse, FiniteLaw.probability_false]
  · have hempty : S.available = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    have hT : T ∉ S.available := by simp [hempty]
    simp only [greedyKernel, hnonempty]
    simp [hT, hTnot]

/-- While at least `D > 0` choices remain, the probability of inserting one
specified new triangle in the next transition is at most `D⁻¹`. -/
theorem greedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (S : GreedyStateOn V) (T : TripleOn V)
    (D : ℕ) (hD : 0 < D) (hcard : D ≤ S.available.card)
    (hTnot : T ∉ S.chosen) :
    (greedyKernel F S).probability (fun S' ↦ T ∈ S'.chosen) ≤
      (D : ℝ≥0)⁻¹ := by
  rw [greedyKernel_probability_new_triangle F S T hTnot]
  split_ifs with hT
  · simpa only [one_div] using
      (one_div_le_one_div_of_le (by exact_mod_cast hD)
        (by exact_mod_cast hcard : (D : ℝ≥0) ≤ S.available.card))
  · exact bot_le

end Erdos207
