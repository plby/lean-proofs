/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPortToggle
import ErdosProblems.Erdos599.ReducingBoundary

/-!
# Exact domain, range and balance of a finite port toggle

No old matched port is lost. The domain gains precisely the previously
free sending endpoint, and the range gains precisely the previously free
receiving endpoint. The original vertices of these endpoints may coincide.
-/

namespace Erdos599.GroundingPortToggle.AugmentingPath

open Set DirectedPath Alternating GroundingAllMarkerPorts

universe u

variable {V : Type u} {G : DWeb V} {M : V → V → Prop} (D : AugmentingPath G M)

theorem toggled_outgoing_iff (x : V) :
    (∃ y, D.toggled x y) ↔ (∃ y, M x y) ∨ x = D.first := by
  classical
  constructor
  · rintro ⟨y, hy | hy⟩
    · exact Or.inl ⟨y, hy.1⟩
    · by_cases hx : x = D.first
      · exact Or.inr hx
      · obtain ⟨z, hz⟩ := D.backward_outgoing_of_mem_ne_first
          (D.path.edgeSet_subset_support_prod hy).1 hx
        exact Or.inl ⟨z, D.backward_mem hz⟩
  · rintro (⟨y, hy⟩ | rfl)
    · by_cases hback : D.backward x y
      · obtain ⟨z, hz⟩ := D.forward_outgoing_of_mem
          (D.path.edgeSet_subset_support_prod hback).2
        exact ⟨z, Or.inr hz⟩
      · exact ⟨y, Or.inl ⟨hy, hback⟩⟩
    · obtain ⟨z, hz⟩ := D.forward_outgoing_of_mem (D.path_start ▸ D.path.start_mem_support)
      exact ⟨z, Or.inr hz⟩

theorem toggled_incoming_iff (y : V) :
    (∃ x, D.toggled x y) ↔ (∃ x, M x y) ∨ y = D.last := by
  classical
  constructor
  · rintro ⟨x, hx | hx⟩
    · exact Or.inl ⟨x, hx.1⟩
    · by_cases hy : y = D.last
      · exact Or.inr hy
      · obtain ⟨z, hz⟩ := D.backward_incoming_of_mem_ne_last
          (D.path.edgeSet_subset_support_prod hx).2 hy
        exact Or.inl ⟨z, D.backward_mem hz⟩
  · rintro (⟨x, hx⟩ | rfl)
    · by_cases hback : D.backward x y
      · obtain ⟨z, hz⟩ := D.forward_incoming_of_mem
          (D.path.edgeSet_subset_support_prod hback).1
        exact ⟨z, Or.inr hz⟩
      · exact ⟨x, Or.inl ⟨hx, hback⟩⟩
    · obtain ⟨z, hz⟩ := D.forward_incoming_of_mem (D.path_finish ▸ D.path.finish_mem_support)
      exact ⟨z, Or.inr hz⟩

theorem outgoing_indicator (x : V) :
    propInt (∃ y, D.toggled x y) = propInt (∃ y, M x y) + propInt (x = D.first) := by
  classical
  rw [D.toggled_outgoing_iff]
  by_cases hx : x = D.first
  · subst x
    have hOld : ¬ ∃ y, M D.first y := by
      rintro ⟨y, hy⟩
      exact D.first_free y hy
    simp [propInt, hOld]
  · simp [propInt, hx]

theorem incoming_indicator (x : V) :
    propInt (∃ y, D.toggled y x) = propInt (∃ y, M y x) + propInt (x = D.last) := by
  classical
  rw [D.toggled_incoming_iff]
  by_cases hx : x = D.last
  · subst x
    have hOld : ¬ ∃ y, M y D.last := by
      rintro ⟨y, hy⟩
      exact D.last_free y hy
    simp [propInt, hOld]
  · simp [propInt, hx]

/-- Exact signed boundary conservation before discarding identities. -/
theorem toggled_edgeBalance (x : V) :
    edgeBalance {e : V × V | D.toggled e.1 e.2} x =
      edgeBalance {e : V × V | M e.1 e.2} x + propInt (x = D.first) - propInt (x = D.last) := by
  change propInt (∃ y, D.toggled x y) - propInt (∃ y, D.toggled y x) =
    (propInt (∃ y, M x y) - propInt (∃ y, M y x)) +
      propInt (x = D.first) - propInt (x = D.last)
  rw [D.outgoing_indicator, D.incoming_indicator]
  omega

#print axioms toggled_outgoing_iff
#print axioms toggled_incoming_iff
#print axioms toggled_edgeBalance

end Erdos599.GroundingPortToggle.AugmentingPath
