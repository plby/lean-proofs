/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability

/-! # Injective decoding preserves constant-weight joint inclusion -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem joint_inclusion_image_le
    {Ω I J : Type*} [Fintype Ω] [Fintype I] [DecidableEq I] [DecidableEq J]
    (L : FiniteLaw Ω) (R : Ω → Finset I) (f : I → J) (hf : Function.Injective f)
    (p : ℝ≥0) (hjoint : ∀ U, L.probability (fun ω ↦ U ⊆ R ω) ≤ p ^ U.card)
    (A : Finset J) :
    L.probability (fun ω ↦ A ⊆ (R ω).image f) ≤ p ^ A.card := by
  classical
  by_cases hA : A ⊆ univ.image f
  · let U : Finset I := univ.filter (fun i ↦ f i ∈ A)
    have himage : U.image f = A := by
      ext j
      constructor
      · intro hj
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
        exact (mem_filter.mp hi).2
      · intro hj
        obtain ⟨i, _hi, rfl⟩ := mem_image.mp (hA hj)
        exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hj⟩, rfl⟩
    have hcard : U.card = A.card := by
      rw [← himage, card_image_of_injective U hf]
    calc
      _ ≤ L.probability (fun ω ↦ U ⊆ R ω) := by
        apply L.probability_mono
        intro ω hω i hi
        have hfi : f i ∈ A := (mem_filter.mp hi).2
        obtain ⟨i', hi', heq⟩ := mem_image.mp (hω hfi)
        exact hf heq ▸ hi'
      _ ≤ p ^ U.card := hjoint U
      _ = _ := by rw [hcard]
  · have hzero : L.probability (fun ω ↦ A ⊆ (R ω).image f) ≤
        L.probability (fun _ ↦ False) := by
      apply L.probability_mono
      intro ω hω
      exact hA (hω.trans (image_subset_image (subset_univ (R ω))))
    rw [FiniteLaw.probability_false] at hzero
    exact hzero.trans zero_le

end

end Erdos207
