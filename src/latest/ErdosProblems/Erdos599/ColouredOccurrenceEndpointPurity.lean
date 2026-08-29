/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch

/-!
# Recovering reference endpoint purity from balanced incidences

At a nonisolated reference endpoint, equal balances and removal of conflicting
incidences already exclude a forbidden forward incidence. Isolated reference
vertices are a genuine separate exception. This is useful after connector
contraction, where the exposed finite-word endpoints supply the balance.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

theorem endpoint_pure_of_incidence_balance
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {F R : Set (V × V)} (hR : R ⊆ familyEdges Y)
    (hin : ∀ {a b x}, (a, x) ∈ F → (b, x) ∈ familyEdges Y → (b, x) ∈ R)
    (hout : ∀ {x a b}, (x, a) ∈ F → (x, b) ∈ familyEdges Y → (x, b) ∈ R)
    (hbalance : ∀ x ∈ Gamma.vertexSet Y, edgeBalance F x = edgeBalance R x)
    (hisolated : ∀ {x y}, (x, y) ∈ F →
      x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y)
    {x y : V} (hxy : (x, y) ∈ F) :
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
  constructor
  · intro hy
    have hyv : y ∈ Gamma.vertexSet Y := initialSet_subset_vertexSet Y hy
    rw [initialSet_eq_isolated_union_outgoing_boundary hY hYfin] at hy
    rcases hy with hyIso | ⟨hyOut, hyNoIn⟩
    · exact (hisolated hxy).2 hyIso
    · have hFin : HasIncoming F y := ⟨x, hxy⟩
      have hRnoIn : ¬HasIncoming R y := by
        rintro ⟨a, ha⟩
        exact hyNoIn ⟨a, hR ha⟩
      have hb := hbalance y hyv
      by_cases hFout : HasOutgoing F y
      · obtain ⟨a, ha⟩ := hFout
        obtain ⟨b, hbY⟩ := hyOut
        have hFout' : HasOutgoing F y := ⟨a, ha⟩
        have hRout : HasOutgoing R y := ⟨b, hout ha hbY⟩
        simp [edgeBalance, propInt, hFin, hFout', hRnoIn, hRout] at hb
      · by_cases hRout : HasOutgoing R y <;>
          simp [edgeBalance, propInt, hFin, hFout, hRnoIn, hRout] at hb
  · intro hx
    have hxv : x ∈ Gamma.vertexSet Y := terminalFrontier_subset_vertexSet Y hx
    rw [terminalFrontier_eq_isolated_union_incoming_boundary hY hYfin] at hx
    rcases hx with hxIso | ⟨hxIn, hxNoOut⟩
    · exact (hisolated hxy).1 hxIso
    · have hFout : HasOutgoing F x := ⟨y, hxy⟩
      have hRnoOut : ¬HasOutgoing R x := by
        rintro ⟨a, ha⟩
        exact hxNoOut ⟨a, hR ha⟩
      have hb := hbalance x hxv
      by_cases hFin : HasIncoming F x
      · obtain ⟨a, ha⟩ := hFin
        obtain ⟨b, hbY⟩ := hxIn
        have hFin' : HasIncoming F x := ⟨a, ha⟩
        have hRin : HasIncoming R x := ⟨b, hin ha hbY⟩
        simp [edgeBalance, propInt, hFin', hFout, hRnoOut, hRin] at hb
      · by_cases hRin : HasIncoming R x <;>
          simp [edgeBalance, propInt, hFin, hFout, hRnoOut, hRin] at hb

namespace FiniteColouredOccurrenceWord

variable {W : Set Gamma.DPath}

/-- In the finite-word case, exposed endpoints discharge the reference
balance premise. Only isolated-reference incidence needs separate geometry. -/
theorem endpoint_pure_of_incidence_of_endpoints_outside
    (Q : FiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    (hin : ∀ {a b x}, (a, x) ∈ Q.forwardEdges →
      (b, x) ∈ familyEdges Y → (b, x) ∈ Q.backwardEdges)
    (hout : ∀ {x a b}, (x, a) ∈ Q.forwardEdges →
      (x, b) ∈ familyEdges Y → (x, b) ∈ Q.backwardEdges)
    (hfirst : Q.vertex 0 ∉ Gamma.vertexSet Y)
    (hlast : Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    (hisolated : ∀ {x y}, (x, y) ∈ Q.forwardEdges →
      x ∉ isolatedVertices Y ∧ y ∉ isolatedVertices Y)
    {x y : V} (hxy : (x, y) ∈ Q.forwardEdges) :
    y ∉ Gamma.initialSet Y ∧ x ∉ Gamma.terminalFrontier Y := by
  apply endpoint_pure_of_incidence_balance hY hYfin
    Q.backwardEdges_subset_familyEdges hin hout _ hisolated hxy
  intro z hz
  have hzFirst : z ≠ Q.vertex 0 := fun h ↦ hfirst (h ▸ hz)
  have hzLast : z ≠ Q.vertex (Fin.last Q.length) := fun h ↦ hlast (h ▸ hz)
  have hb := Q.edgeBalance_forward_sub_backward hW hY z
  simp only [propInt, hzFirst, hzLast, ↓reduceIte, sub_self] at hb
  omega

end FiniteColouredOccurrenceWord

#print axioms endpoint_pure_of_incidence_balance
#print axioms FiniteColouredOccurrenceWord.endpoint_pure_of_incidence_of_endpoints_outside

end Erdos599.Alternating
