/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeHammockClosure
import ErdosProblems.Erdos599.SingularCardinal
import ErdosProblems.Erdos599.OutsideReferenceCore

/-!
# The reference with its endpoint owners excluded

This is an explicit reference subfamily, not an identification with the
original reference or a new meaning of a global imaginary edge. At most two
owners are removed, and whole-reference closure confines all removed owners
to the already closed carrier when the displayed endpoints belong to it.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointReference

open Set Cardinal DirectedPath
open ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {s t : V} {e : Option V} {X : Set V}

def reference (Y : Set Gamma.DPath) (s : V) (e : Option V) : Set Gamma.DPath :=
  outsideReference Y (endpoints s e)

theorem reference_subset : reference Y s e ⊆ Y := fun _ hp ↦ hp.1

theorem isWarp (hY : Gamma.IsWarp Y) : Gamma.IsWarp (reference Y s e) :=
  hY.subset reference_subset

theorem vertexSet_disjoint_endpoints :
    Disjoint (Gamma.vertexSet (reference Y s e)) (endpoints s e) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, hxp⟩ hx
  exact Set.disjoint_left.mp hp.2 hxp hx

theorem source_off : s ∉ Gamma.vertexSet (reference Y s e) := by
  intro hs
  exact Set.disjoint_left.mp vertexSet_disjoint_endpoints hs (Or.inl rfl)

theorem terminal_off (ht : e = some t) : t ∉ Gamma.vertexSet (reference Y s e) := by
  intro hmem
  exact Set.disjoint_left.mp vertexSet_disjoint_endpoints hmem (Or.inr ht)

theorem endpoints_card_le_two (s : V) (e : Option V) : #(endpoints s e) ≤ 2 := by
  cases e with
  | none => simp
  | some t =>
      have heq : endpoints s (some t) = ({s} : Set V) ∪ {t} := by
        ext x
        simp [endpoints, eq_comm]
      rw [heq]
      calc
        #(({s} : Set V) ∪ {t} : Set V) ≤ #({s} : Set V) + #({t} : Set V) :=
          Cardinal.mk_union_le _ _
        _ = 2 := by norm_num

/-- Removed owners inject into their endpoint contacts by warp disjointness. -/
theorem removed_card_le_two (hY : Gamma.IsWarp Y) :
    #(Y \ reference Y s e : Set Gamma.DPath) ≤ 2 := by
  have heq : Y \ reference Y s e =
      {p ∈ Y | ¬Disjoint p.support (endpoints s e)} := by
    ext p
    simp only [reference, outsideReference, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact (Gamma.mk_pathsMeeting_le Y (endpoints s e) hY).trans (endpoints_card_le_two s e)

/-- Excluding endpoint owners never changes the reference outside the cut
when that cut is closed under complete original reference paths. -/
theorem removed_vertices_subset_closed
    (hclosed : ClosedUnderPaths Gamma Y X) (hendpoints : endpoints s e ⊆ X) :
    Gamma.vertexSet (Y \ reference Y s e) ⊆ X := by
  rintro x ⟨p, hp, hxp⟩
  have hmeet : ¬Disjoint p.support (endpoints s e) := by
    intro hd
    exact hp.2 ⟨hp.1, hd⟩
  obtain ⟨w, hwp, hwEnd⟩ := Set.not_disjoint_iff.mp hmeet
  exact hclosed p hp.1 ⟨w, hwp, hendpoints hwEnd⟩ hxp

#print axioms removed_card_le_two
#print axioms removed_vertices_subset_closed

end Erdos599.Blueprint.ColouredSafeEndpointReference
