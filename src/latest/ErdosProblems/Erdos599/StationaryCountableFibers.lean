/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Stationary

/-!
# Stationary transversals of countable fibers

Assertion 8.20 first thins a stationary path family so that no two retained
members use the same hanging fragment.  The set-theoretic input is that a map
with countable fibers on a stationary subset of a regular uncountable cardinal
has a stationary restriction on which it is injective.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Stationary

universe u v

/-- A stationary set can be thinned to an injective transversal of a map whose
fibers on that set are countable.  The proof colors each fiber injectively by
`ℕ`; countable completeness makes one color class stationary. -/
theorem exists_stationary_subset_injOn_of_countable_fibers
    {kappa : Cardinal.{u}} (hregular : kappa.IsRegular)
    (huncountable : ℵ₀ < kappa) {X : Type v}
    {A : Set (Below kappa)} (hA : IsStationaryBelow kappa A)
    (owner : Below kappa → X)
    (hfiber : ∀ x, (A ∩ owner ⁻¹' {x}).Countable) :
    ∃ B : Set (Below kappa), B ⊆ A ∧ IsStationaryBelow kappa B ∧
      Set.InjOn owner B := by
  let fiber : X → Set (Below kappa) := fun x ↦ A ∩ owner ⁻¹' {x}
  let code : X → Below kappa → ℕ := fun x ↦
    Classical.choose (Set.countable_iff_exists_injOn.mp (hfiber x))
  have code_inj : ∀ x, Set.InjOn (code x) (fiber x) := fun x ↦
    Classical.choose_spec (Set.countable_iff_exists_injOn.mp (hfiber x))
  let colour : Below kappa → ℕ := fun a ↦ code (owner a) a
  let layer : ℕ → Set (Below kappa) := fun n ↦ {a | a ∈ A ∧ colour a = n}
  have hcover : A ⊆ ⋃ n, layer n := by
    intro a ha
    exact Set.mem_iUnion.2 ⟨colour a, ha, rfl⟩
  have hexists : ∃ n, IsStationaryBelow kappa (layer n) := by
    by_contra h
    push Not at h
    exact (not_isStationaryBelow_iUnion_of_countable
      hregular huncountable h) (hA.mono hcover)
  obtain ⟨n, hn⟩ := hexists
  refine ⟨layer n, ?_, hn, ?_⟩
  · intro a ha
    exact ha.1
  · intro a ha b hb hab
    have haFiber : a ∈ fiber (owner a) := ⟨ha.1, by simp⟩
    have hbFiber : b ∈ fiber (owner a) := by
      refine ⟨hb.1, ?_⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hab.symm
    apply code_inj (owner a) haFiber hbFiber
    have haColour : code (owner a) a = n := ha.2
    have hbColour : code (owner b) b = n := hb.2
    rw [← hab] at hbColour
    exact haColour.trans hbColour.symm

end Stationary
end Erdos599
