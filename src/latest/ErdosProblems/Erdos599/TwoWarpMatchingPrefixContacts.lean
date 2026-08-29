/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingBoundaryContacts
import ErdosProblems.Erdos599.TwoWarpMatchingForwardOrbit

/-!
# Reference-contact coverage on internal matching prefixes

An internal first-return prefix is not rooted at an unmatched end of its
whole symmetric-difference component.  Nevertheless its exposed endpoints
are outside the chosen reference family.  Hence every reference contact at
an endpoint of a literal forward step occurs strictly inside the prefix and
the unique adjacent reference-only step is present.

This file records that statement before identity contraction or run
compression.  It uses literal matching incidence and does not infer contact
coverage from the weaker projected alternating path.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace FinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

/-- A reference-only step of a finite internal prefix covers a port. -/
def ReferenceCovered (P : FinitePortPrefix W Y root) (a : Port V) : Prop :=
  ∃ i : Fin P.lastIndex,
    (∃ x y, P.port i.castSucc = .inr y ∧ P.port i.succ = .inl x ∧
      Exclusive Y W x y) ∧
    (a = P.port i.castSucc ∨ a = P.port i.succ)

/-- Adjacent-step coverage on a finite prefix whose two exposed endpoints
are outside the reference carrier. -/
theorem forward_contact_covered
    (P : FinitePortPrefix W Y root)
    (hrootOff : root ∉ Gamma.vertexSet Y)
    (hterminalOff : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∉ Gamma.vertexSet Y)
    (i : Fin P.lastIndex) {x y : V}
    (hleft : P.port i.castSucc = .inl x)
    (hright : P.port i.succ = .inr y) :
    ((∃ z, (x, z) ∈ familyEdges Y ∧ Exclusive Y W x z) →
        P.ReferenceCovered (.inl x)) ∧
      ((∃ z, (z, y) ∈ familyEdges Y ∧ Exclusive Y W z y) →
        P.ReferenceCovered (.inr y)) := by
  constructor
  · rintro ⟨z, hxzY, hz⟩
    by_cases hi0 : i.1 = 0
    · have hip : i.castSucc = (0 : Fin (P.lastIndex + 1)) := Fin.ext hi0
      have hxr : x = root := Sum.inl.inj
        (hleft.symm.trans (hip ▸ P.starts))
      subst x
      apply False.elim
      apply hrootOff
      exact (familyEdges_subset_vertexSet_prod Y hxzY).1
    · let j : Fin P.lastIndex := ⟨i.1 - 1, by omega⟩
      have hjsucc : j.succ = i.castSucc := by
        apply Fin.ext
        change i.1 - 1 + 1 = i.1
        omega
      have hj := P.steps j
      rw [hjsucc, hleft] at hj
      rcases hprev : P.port j.castSucc with a | b
      · rw [hprev] at hj
        exact False.elim hj
      · rw [hprev] at hj
        have htarget : P.port j.succ = .inl x := by
          rw [hjsucc]
          exact hleft
        exact ⟨j, ⟨x, b, hprev, htarget, hj⟩, Or.inr htarget.symm⟩
  · rintro ⟨z, hzyY, hz⟩
    by_cases hilast : i.1 + 1 = P.lastIndex
    · have hisucc : i.succ =
          (⟨P.lastIndex, Nat.lt_succ_self _⟩ : Fin (P.lastIndex + 1)) :=
        Fin.ext hilast
      apply False.elim
      apply hterminalOff
      change projectPort (P.port
        ⟨P.lastIndex, Nat.lt_succ_self P.lastIndex⟩) ∈
          Gamma.vertexSet Y
      rw [← hisucc, hright]
      exact (familyEdges_subset_vertexSet_prod Y hzyY).2
    · let j : Fin P.lastIndex := ⟨i.1 + 1, by omega⟩
      have hjcast : j.castSucc = i.succ := Fin.ext rfl
      have hj := P.steps j
      rw [hjcast, hright] at hj
      rcases hnext : P.port j.succ with a | b
      · rw [hnext] at hj
        have hsource : P.port j.castSucc = .inr y := by
          rw [hjcast]
          exact hright
        exact ⟨j, ⟨a, y, hsource, hnext, hj⟩, Or.inl hsource.symm⟩
      · rw [hnext] at hj
        exact False.elim hj

/-- Boundary alignment turns every reference-carrier endpoint of a literal
forward step into a covered reference contact of the finite prefix. -/
theorem forward_vertex_contacts_covered
    (P : FinitePortPrefix W Y root)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hrootOff : root ∉ Gamma.vertexSet Y)
    (hterminalOff : P.projectedVertex
      ⟨P.lastIndex, Nat.lt_succ_self _⟩ ∉ Gamma.vertexSet Y)
    (i : Fin P.lastIndex) {x y : V}
    (hleft : P.port i.castSucc = .inl x)
    (hright : P.port i.succ = .inr y)
    (hxNotTerminalY : x ∉ Gamma.terminalFrontier Y)
    (hyNotInitialY : y ∉ Gamma.initialSet Y) :
    (x ∈ Gamma.vertexSet Y → P.ReferenceCovered (.inl x)) ∧
      (y ∈ Gamma.vertexSet Y → P.ReferenceCovered (.inr y)) := by
  have hstep := P.steps i
  rw [hleft, hright] at hstep
  have hexposed := actualExclusive_forward_contacts_of_endpoint_exclusion
    hW hY hstep hxNotTerminalY hyNotInitialY
  have hadjacent := P.forward_contact_covered hrootOff hterminalOff
    i hleft hright
  exact ⟨fun hx ↦ hadjacent.1 (hexposed.1 hx),
    fun hy ↦ hadjacent.2 (hexposed.2 hy)⟩

end FinitePortPrefix

namespace InfinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

/-- A reference-only step of an infinite internal prefix covers a port. -/
def ReferenceCovered (P : InfinitePortPrefix W Y root) (a : Port V) : Prop :=
  ∃ i,
    (∃ x y, P.port i = .inr y ∧ P.port (i + 1) = .inl x ∧
      Exclusive Y W x y) ∧
    (a = P.port i ∨ a = P.port (i + 1))

/-- Adjacent-step coverage on an infinite prefix whose exposed root is
outside the reference carrier. -/
theorem forward_contact_covered
    (P : InfinitePortPrefix W Y root)
    (hrootOff : root ∉ Gamma.vertexSet Y)
    (i : Nat) {x y : V}
    (hleft : P.port i = .inl x)
    (hright : P.port (i + 1) = .inr y) :
    ((∃ z, (x, z) ∈ familyEdges Y ∧ Exclusive Y W x z) →
        P.ReferenceCovered (.inl x)) ∧
      ((∃ z, (z, y) ∈ familyEdges Y ∧ Exclusive Y W z y) →
        P.ReferenceCovered (.inr y)) := by
  constructor
  · rintro ⟨z, hxzY, hz⟩
    cases i with
    | zero =>
        have hxr : x = root := Sum.inl.inj (hleft.symm.trans P.starts)
        subst x
        apply False.elim
        apply hrootOff
        exact (familyEdges_subset_vertexSet_prod Y hxzY).1
    | succ i =>
        have hj := P.steps i
        rw [hleft] at hj
        rcases hprev : P.port i with a | b
        · rw [hprev] at hj
          exact False.elim hj
        · rw [hprev] at hj
          exact ⟨i, ⟨x, b, hprev, hleft, hj⟩, Or.inr hleft.symm⟩
  · rintro ⟨z, _hzyY, hz⟩
    have hj := P.steps (i + 1)
    rw [hright] at hj
    rcases hnext : P.port (i + 1 + 1) with a | b
    · rw [hnext] at hj
      exact ⟨i + 1, ⟨a, y, hright, hnext, hj⟩, Or.inl hright.symm⟩
    · rw [hnext] at hj
      exact False.elim hj

/-- Boundary alignment turns every reference-carrier endpoint of a literal
forward step into a covered reference contact of the infinite prefix. -/
theorem forward_vertex_contacts_covered
    (P : InfinitePortPrefix W Y root)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hrootOff : root ∉ Gamma.vertexSet Y)
    (i : Nat) {x y : V}
    (hleft : P.port i = .inl x)
    (hright : P.port (i + 1) = .inr y)
    (hxNotTerminalY : x ∉ Gamma.terminalFrontier Y)
    (hyNotInitialY : y ∉ Gamma.initialSet Y) :
    (x ∈ Gamma.vertexSet Y → P.ReferenceCovered (.inl x)) ∧
      (y ∈ Gamma.vertexSet Y → P.ReferenceCovered (.inr y)) := by
  have hstep := P.steps i
  rw [hleft, hright] at hstep
  have hexposed := actualExclusive_forward_contacts_of_endpoint_exclusion
    hW hY hstep hxNotTerminalY hyNotInitialY
  have hadjacent := P.forward_contact_covered hrootOff i hleft hright
  exact ⟨fun hx ↦ hadjacent.1 (hexposed.1 hx),
    fun hy ↦ hadjacent.2 (hexposed.2 hy)⟩

end InfinitePortPrefix

#print axioms FinitePortPrefix.forward_vertex_contacts_covered
#print axioms InfinitePortPrefix.forward_vertex_contacts_covered

end TwoWarpMatchingTraversal
end Erdos599
