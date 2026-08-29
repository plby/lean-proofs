/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Bridge

/-!
# Transport of an orthogonal packing and separator through path contraction

A contraction need not be injective on all vertices.  It is enough that a
point projected from a packed path stays on that contracted path, and that
contracted paths cannot acquire intersections absent from the original
packing.  These are the exact support properties of directed subdivision.
-/

namespace Erdos599
namespace Bridge

open Set

universe u v

variable {V : Type u} {W : Type v}
variable {D : Digraph V} {E : Digraph W}
variable {A B : Set V} {A' B' : Set W}

/-- Support-exact path transport preserves the full Menger conclusion,
including exactly one separator point per packed path. -/
theorem directedMengerConclusion_of_support_transport
    (embed : V → W) (project : W → V)
    (liftPath : DirectedABPath D A B → DirectedABPath E A' B')
    (contractPath : DirectedABPath E A' B' → DirectedABPath D A B)
    (hcontract : ∀ q x, x ∈ (contractPath q).supportSet →
      embed x ∈ q.supportSet)
    (hproject : ∀ q w, w ∈ q.supportSet →
      project w ∈ (contractPath q).supportSet)
    (hlift : ∀ q w, w ∈ (liftPath q).supportSet → project w ∈ q.supportSet)
    (hmenger : DirectedMengerConclusion E A' B') :
    DirectedMengerConclusion D A B := by
  obtain ⟨P, S, hP, hsep, horth⟩ := hmenger
  refine ⟨contractPath '' P, project '' S, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    obtain ⟨p', hp', rfl⟩ := hp
    obtain ⟨q', hq', rfl⟩ := hq
    have hpq' : p' ≠ q' := by
      intro heq
      exact hpq (congrArg contractPath heq)
    apply Set.disjoint_left.2
    intro x hxp hxq
    exact Set.disjoint_left.1 (hP hp' hq' hpq')
      (hcontract p' x hxp) (hcontract q' x hxq)
  · intro q
    obtain ⟨w, hwS, hwq⟩ := hsep (liftPath q)
    exact ⟨project w, ⟨w, hwS, rfl⟩, hlift q w hwq⟩
  · constructor
    · rintro x ⟨w, hwS, rfl⟩
      have hwUnion := horth.1 hwS
      simp only [Set.mem_iUnion] at hwUnion
      obtain ⟨q, hqP, hwq⟩ := hwUnion
      exact Set.mem_iUnion.2 ⟨contractPath q,
        Set.mem_iUnion.2 ⟨⟨q, hqP, rfl⟩, hproject q w hwq⟩⟩
    · rintro p ⟨p', hp', rfl⟩
      obtain ⟨w, ⟨hwS, hwp⟩, huniq⟩ := horth.2 p' hp'
      refine ⟨project w, ⟨⟨w, hwS, rfl⟩, hproject p' w hwp⟩, ?_⟩
      rintro x ⟨⟨z, hzS, rfl⟩, hzp⟩
      have hzUnion := horth.1 hzS
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hzUnion
      obtain ⟨hqP, hzq⟩ := Set.mem_iUnion.1 hq
      have hqp : q = p' := by
        by_contra hne
        exact Set.disjoint_left.1 (hP hqP hp' hne)
          (hcontract q (project z) (hproject q z hzq))
          (hcontract p' (project z) hzp)
      subst q
      exact congrArg project (huniq z ⟨hzS, hzq⟩)

#print axioms directedMengerConclusion_of_support_transport

end Bridge
end Erdos599

