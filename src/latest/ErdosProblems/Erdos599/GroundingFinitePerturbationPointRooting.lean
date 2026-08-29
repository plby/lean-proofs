/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingFinitePerturbationRooting

/-!
# Rooting a point which cannot lie on a directed cycle

Temporarily stop the relation at the point. New positive boundaries can
only be heads of its deleted outgoing edges. A route from such a head
back to the point contradicts no-return, so sink rooting supplies an
original source. Cycles elsewhere in the relation remain permitted.
-/

noncomputable section

namespace Erdos599.GroundingFinitePerturbationPointRooting

open Set DirectedPath Alternating Alternating.TerminalContactSwitch

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A nonisolated point with no return route is source-rooted. -/
theorem rooted_of_no_return
    (E : Set (V × V)) (A : Set V)
    (hgraph : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hreverse : ¬ ContainsReverseDirectedRay E)
    (hboundary : ∀ x, edgeBalance E x = 1 → x ∈ A)
    {t : V} (ht : t ∈ A ∨ HasIncoming E t)
    (hnoReturn : ∀ y, (t, y) ∈ E →
      ¬ Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) y t) :
    ∃ a ∈ A, Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t := by
  classical
  rcases ht with ht | hin
  · exact ⟨t, ht, .refl⟩
  let K : Set (V × V) := {e | e ∈ E ∧ e.1 ≠ t}
  let A' := A ∪ {x | (t, x) ∈ E}
  have hKbi : Relator.BiUnique fun x y ↦ (x, y) ∈ K :=
    ⟨fun _ _ _ he hf ↦ hbi.1 he.1 hf.1,
      fun _ _ _ he hf ↦ hbi.2 he.1 hf.1⟩
  have hKreverse : ¬ ContainsReverseDirectedRay K := by
    rintro ⟨p, hp⟩
    exact hreverse ⟨p, fun n ↦ (hp n).1⟩
  have hKboundary : ∀ x, edgeBalance K x = 1 → x ∈ A' := by
    intro x hx
    obtain ⟨⟨y, hxy⟩, hnoIn⟩ := edgeBalance_eq_one_iff.mp hx
    by_cases hinE : HasIncoming E x
    · obtain ⟨z, hzx⟩ := hinE
      have hzt : z = t := by
        by_contra hne
        exact hnoIn ⟨z, hzx, hne⟩
      exact Or.inr (hzt ▸ hzx)
    · exact Or.inl (hboundary x (edgeBalance_eq_one_iff.mpr ⟨⟨y, hxy.1⟩, hinE⟩))
  have hinK : HasIncoming K t := by
    obtain ⟨z, hzt⟩ := hin
    exact ⟨z, hzt, fun h ↦ hnoReturn t (h ▸ hzt) .refl⟩
  have hsink : ¬ HasOutgoing K t := by
    rintro ⟨y, _he, hne⟩
    exact hne rfl
  obtain ⟨a, ha, hat⟩ := GroundingFinitePerturbationRooting.sink_rooted_of_noReverseRay
    K A' (fun _ he ↦ hgraph he.1) hKbi hKreverse hKboundary (Or.inr hinK) hsink
  have hroute : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a t :=
    Relation.ReflTransGen.mono (fun _ _ he ↦ he.1) a t hat
  exact ⟨a, ha.resolve_right (fun he ↦ hnoReturn a he hroute), hroute⟩

#print axioms rooted_of_no_return

end Erdos599.GroundingFinitePerturbationPointRooting
