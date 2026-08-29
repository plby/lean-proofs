/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteCompleteWordBoundary

/-!
# Interior defects of a complete safe-word family

At a vertex of the reference warp, every incidence of the union forward
relation forces the corresponding incidence of the union removed relation.
For a family of complete words, the exact boundary lemmas then show that a
nonzero difference between the two balances can occur only strictly inside
the removed relation.

This is the local reduction needed by finite Hall counting.  It deliberately
does not assert that the number of positive interior defects dominates the
number of negative ones; that remaining assertion is a nonlocal saturation
theorem.
-/

noncomputable section

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- A forward outgoing incidence at a reference vertex forces a removed
outgoing reference incidence.  At a reference terminal, endpoint purity
excludes the forward incidence instead. -/
theorem family_backward_hasOutgoing_of_forward_hasOutgoing_on_reference
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    {x : V} (hx : x ∈ Gamma.vertexSet Y)
    (hF : HasOutgoing (familyForwardEdges A) x) :
    HasOutgoing (familyBackwardEdges A) x := by
  obtain ⟨a, hxa⟩ := hF
  by_cases hYout : HasOutgoing (familyEdges Y) x
  · obtain ⟨b, hxb⟩ := hYout
    exact ⟨b, family_outgoing_removed hsafe hxa hxb⟩
  · have hxTerminal : x ∈ Gamma.terminalFrontier Y := by
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin]
      exact ⟨hx, hYout⟩
    exact False.elim ((family_endpoint_pure hsafe hxa).2 hxTerminal)

/-- The incoming dual of
`family_backward_hasOutgoing_of_forward_hasOutgoing_on_reference`. -/
theorem family_backward_hasIncoming_of_forward_hasIncoming_on_reference
    (hY : Gamma.IsWarp Y) (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    {x : V} (hx : x ∈ Gamma.vertexSet Y)
    (hF : HasIncoming (familyForwardEdges A) x) :
    HasIncoming (familyBackwardEdges A) x := by
  obtain ⟨a, hax⟩ := hF
  by_cases hYin : HasIncoming (familyEdges Y) x
  · obtain ⟨b, hbx⟩ := hYin
    exact ⟨b, family_incoming_removed hsafe hax hbx⟩
  · have hxInitial : x ∈ Gamma.initialSet Y := by
      rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin]
      exact ⟨hx, hYin⟩
    exact False.elim ((family_endpoint_pure hsafe hax).1 hxInitial)

private theorem edgeBalance_cases (E : Set (V × V)) (x : V) :
    edgeBalance E x = -1 ∨ edgeBalance E x = 0 ∨ edgeBalance E x = 1 := by
  by_cases hout : HasOutgoing E x <;>
    by_cases hin : HasIncoming E x <;>
    simp [edgeBalance, propInt, hout, hin]

/-- A positive aggregate defect on the reference carrier is exactly a
forward-only exit at a vertex which is internal to the removed relation. -/
theorem family_positiveDefect_iff_forwardExit_removedInterior
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hx : x ∈ Gamma.vertexSet Y) :
    edgeBalance (familyForwardEdges A) x -
        edgeBalance (familyBackwardEdges A) x = 1 ↔
      HasOutgoing (familyForwardEdges A) x ∧
        ¬HasIncoming (familyForwardEdges A) x ∧
        HasOutgoing (familyBackwardEdges A) x ∧
        HasIncoming (familyBackwardEdges A) x := by
  let F := familyForwardEdges A
  let R := familyBackwardEdges A
  change edgeBalance F x - edgeBalance R x = 1 ↔
    HasOutgoing F x ∧ ¬HasIncoming F x ∧
      HasOutgoing R x ∧ HasIncoming R x
  have hOut : HasOutgoing F x → HasOutgoing R x :=
    family_backward_hasOutgoing_of_forward_hasOutgoing_on_reference
      hY hYfin hsafe hx
  have hIn : HasIncoming F x → HasIncoming R x :=
    family_backward_hasIncoming_of_forward_hasIncoming_on_reference
      hY hYfin hsafe hx
  constructor
  · intro hdef
    have hcasesF := edgeBalance_cases F x
    have hcasesR := edgeBalance_cases R x
    have hnotRneg : edgeBalance R x ≠ -1 := by
      intro hRneg
      have hFneg : edgeBalance F x = -1 :=
        family_forward_negative_of_backward_negative hW hY hYfin hsafe hends
          (by simpa [R] using hRneg)
      omega
    have hFb : edgeBalance F x = 1 := by
      rcases hcasesF with hFneg | hFzero | hFpos
      · omega
      · rcases hcasesR with hRneg | hRzero | hRpos <;> omega
      · exact hFpos
    have hRb : edgeBalance R x = 0 := by omega
    obtain ⟨hFout, hFnoIn⟩ := edgeBalance_eq_one_iff.mp hFb
    have hRout := hOut hFout
    have hRin : HasIncoming R x := by
      by_contra hno
      have : edgeBalance R x = 1 :=
        edgeBalance_eq_one_iff.mpr ⟨hRout, hno⟩
      omega
    exact ⟨hFout, hFnoIn, hRout, hRin⟩
  · rintro ⟨hFout, hFnoIn, hRout, hRin⟩
    have hFb : edgeBalance F x = 1 :=
      edgeBalance_eq_one_iff.mpr ⟨hFout, hFnoIn⟩
    have hRb : edgeBalance R x = 0 := by
      simp [edgeBalance, hRout, hRin]
    omega

/-- A negative aggregate defect is the incoming dual: a forward-only entry
strictly inside the removed relation. -/
theorem family_negativeDefect_iff_forwardEntry_removedInterior
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {A : Set (FiniteColouredOccurrenceWord W Y)}
    (hsafe : ∀ Q ∈ A, Q.IsIntervalSafe)
    (hends : ∀ Q ∈ A, Q.vertex 0 ∉ Gamma.vertexSet Y ∧
      Q.vertex (Fin.last Q.length) ∉ Gamma.vertexSet Y)
    {x : V} (hx : x ∈ Gamma.vertexSet Y) :
    edgeBalance (familyForwardEdges A) x -
        edgeBalance (familyBackwardEdges A) x = -1 ↔
      HasIncoming (familyForwardEdges A) x ∧
        ¬HasOutgoing (familyForwardEdges A) x ∧
        HasOutgoing (familyBackwardEdges A) x ∧
        HasIncoming (familyBackwardEdges A) x := by
  let F := familyForwardEdges A
  let R := familyBackwardEdges A
  change edgeBalance F x - edgeBalance R x = -1 ↔
    HasIncoming F x ∧ ¬HasOutgoing F x ∧
      HasOutgoing R x ∧ HasIncoming R x
  have hOut : HasOutgoing F x → HasOutgoing R x :=
    family_backward_hasOutgoing_of_forward_hasOutgoing_on_reference
      hY hYfin hsafe hx
  have hIn : HasIncoming F x → HasIncoming R x :=
    family_backward_hasIncoming_of_forward_hasIncoming_on_reference
      hY hYfin hsafe hx
  constructor
  · intro hdef
    have hcasesF := edgeBalance_cases F x
    have hcasesR := edgeBalance_cases R x
    have hnotRpos : edgeBalance R x ≠ 1 := by
      intro hRpos
      have hFpos : edgeBalance F x = 1 :=
        family_forward_positive_of_backward_positive hW hY hYfin hsafe hends
          (by simpa [R] using hRpos)
      omega
    have hFb : edgeBalance F x = -1 := by
      rcases hcasesF with hFneg | hFzero | hFpos
      · exact hFneg
      · rcases hcasesR with hRneg | hRzero | hRpos <;> omega
      · omega
    have hRb : edgeBalance R x = 0 := by omega
    obtain ⟨hFin, hFnoOut⟩ := edgeBalance_eq_neg_one_iff.mp hFb
    have hRin := hIn hFin
    have hRout : HasOutgoing R x := by
      by_contra hno
      have : edgeBalance R x = -1 :=
        edgeBalance_eq_neg_one_iff.mpr ⟨hRin, hno⟩
      omega
    exact ⟨hFin, hFnoOut, hRout, hRin⟩
  · rintro ⟨hFin, hFnoOut, hRout, hRin⟩
    have hFb : edgeBalance F x = -1 :=
      edgeBalance_eq_neg_one_iff.mpr ⟨hFin, hFnoOut⟩
    have hRb : edgeBalance R x = 0 := by
      simp [edgeBalance, hRout, hRin]
    omega

#print axioms family_backward_hasOutgoing_of_forward_hasOutgoing_on_reference
#print axioms family_backward_hasIncoming_of_forward_hasIncoming_on_reference
#print axioms family_positiveDefect_iff_forwardExit_removedInterior
#print axioms family_negativeDefect_iff_forwardEntry_removedInterior

end Erdos599.Alternating.FiniteColouredOccurrenceWord
