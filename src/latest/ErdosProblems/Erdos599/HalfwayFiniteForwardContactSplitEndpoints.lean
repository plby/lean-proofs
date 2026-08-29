/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayFiniteForwardContactSplit

/-!
# Pieces starting and ending at every finite-path contact

The all-contact splitter records that every contact is *an* endpoint of a
piece.  Trace-level interval assembly needs the oriented refinement: unless
the contact is the terminal of the parent, some piece starts there; dually,
unless it is the initial of the parent, some piece finishes there.

For an endpoint with the wrong orientation, the next or previous list member
has the required orientation by the chain law.  The only obstruction would
make that member the last or first piece, contradicting the corresponding
parent-endpoint inequality.
-/

noncomputable section

open Set

namespace Erdos599
namespace DirectedPath
namespace FinitePath
namespace ContactSplit

universe u

variable {V : Type u} {D : Digraph V}
variable {p : FinitePath D} {X : Set V}

/-- Every contact, including the parent start, which is not the parent finish
is the start of a concrete child piece. -/
theorem exists_piece_start (A : ContactSplit p X) {x : V}
    (hx : x ∈ p.support ∩ X ∨ x = p.start)
    (hxfinish : x ≠ p.finish) :
    ∃ q : {q : FinitePath D // q ∈ A.pieces}, q.1.start = x := by
  classical
  rcases hx with hxContact | hxStart
  · obtain ⟨q, hq, hxq | hxq⟩ := A.every_contact_is_piece_endpoint hxContact
    · exact ⟨⟨q, hq⟩, hxq.symm⟩
    · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hq
      have hnext : i + 1 < A.pieces.length := by
        by_contra hnot
        have hilast : i = A.pieces.length - 1 := by omega
        have hqLast : q = A.pieces.getLast A.pieces_ne := by
          subst i
          calc
            q = A.pieces[A.pieces.length - 1] := hget.symm
            _ = A.pieces.getLast A.pieces_ne :=
              (List.getLast_eq_getElem A.pieces_ne).symm
        apply hxfinish
        calc
          x = q.finish := hxq
          _ = (A.pieces.getLast A.pieces_ne).finish :=
            congrArg FinitePath.finish hqLast
          _ = p.finish := A.last_finish
      let r : FinitePath D := A.pieces[i + 1]
      have hr : r ∈ A.pieces := List.getElem_mem _
      have hchain := (List.isChain_iff_getElem.mp A.chain) i hnext
      refine ⟨⟨r, hr⟩, ?_⟩
      calc
        r.start = A.pieces[i].finish := hchain.symm
        _ = q.finish := congrArg FinitePath.finish hget
        _ = x := hxq.symm
  · let q := A.pieces.head A.pieces_ne
    refine ⟨⟨q, List.head_mem A.pieces_ne⟩, ?_⟩
    exact A.first_start.trans hxStart.symm

/-- Every contact, including the parent finish, which is not the parent
start is the finish of a concrete child piece. -/
theorem exists_piece_finish (A : ContactSplit p X) {x : V}
    (hx : x ∈ p.support ∩ X ∨ x = p.finish)
    (hxstart : x ≠ p.start) :
    ∃ q : {q : FinitePath D // q ∈ A.pieces}, q.1.finish = x := by
  classical
  rcases hx with hxContact | hxFinish
  · obtain ⟨q, hq, hxq | hxq⟩ := A.every_contact_is_piece_endpoint hxContact
    · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hq
      have hipos : 0 < i := by
        by_contra hnot
        have hizero : i = 0 := by omega
        have hqHead : q = A.pieces.head A.pieces_ne := by
          subst i
          calc
            q = A.pieces[0] := hget.symm
            _ = A.pieces.head A.pieces_ne :=
              (List.head_eq_getElem A.pieces_ne).symm
        apply hxstart
        calc
          x = q.start := hxq
          _ = (A.pieces.head A.pieces_ne).start :=
            congrArg FinitePath.start hqHead
          _ = p.start := A.first_start
      let r : FinitePath D := A.pieces[i - 1]
      have hprev : i - 1 < A.pieces.length := by omega
      have hr : r ∈ A.pieces := List.getElem_mem _
      have hadj : (i - 1) + 1 < A.pieces.length := by omega
      have hchain := (List.isChain_iff_getElem.mp A.chain) (i - 1) hadj
      refine ⟨⟨r, hr⟩, ?_⟩
      calc
        r.finish = A.pieces[(i - 1) + 1].start := hchain
        _ = A.pieces[i].start := by
          have hind : (i - 1) + 1 = i := by omega
          have hfin :
              (⟨(i - 1) + 1, hadj⟩ : Fin A.pieces.length) = ⟨i, hi⟩ :=
            Fin.ext hind
          exact congrArg FinitePath.start (congrArg A.pieces.get hfin)
        _ = q.start := congrArg FinitePath.start hget
        _ = x := hxq.symm
    · exact ⟨⟨q, hq⟩, hxq.symm⟩
  · let q := A.pieces.getLast A.pieces_ne
    refine ⟨⟨q, List.getLast_mem A.pieces_ne⟩, ?_⟩
    exact A.last_finish.trans hxFinish.symm

#print axioms exists_piece_start
#print axioms exists_piece_finish

end ContactSplit
end FinitePath
end DirectedPath
end Erdos599
