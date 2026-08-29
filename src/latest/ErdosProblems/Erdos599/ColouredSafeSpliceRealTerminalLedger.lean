/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeOnePortSplice
import ErdosProblems.Erdos599.GroundingPointwiseSwitch

/-!
# Predicate-parametric edge and terminal ledgers for coloured splices

The one- and two-port splice constructions are graph-independent: they do
not know which represented edges a later application calls real.  This file
therefore fixes an arbitrary predicate `R` on directed edges.  A real
terminal of a path family is a vertex in its carrier from which the family
has no outgoing `R`-edge.

The exact edge identities of the two splice constructions imply two useful
facts.  Every old real edge survives a one-port splice.  It also survives a
two-port splice provided the single cut edge is not real.  Moreover, an old
real terminal other than the processed source port remains a real terminal.
For the two-port construction, the only additional carrier intersection is
the head port `t`; its membership in the terminal frontier of the inserted
warp rules out an inserted outgoing edge there.

No conclusion is made about whether the processed source port ceases to be
a terminal: that requires a nontrivial inserted real edge and is deliberately
kept separate from this preservation ledger.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeSpliceRealTerminalLedger

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The edges of a family selected by an arbitrary edge predicate. -/
def realFamilyEdges (R : V → V → Prop) (W : Set Gamma.DPath) : Set (V × V) :=
  {e | e ∈ familyEdges W ∧ R e.1 e.2}

/-- A carrier vertex with no outgoing family edge selected by `R`. -/
def IsRealTerminal (R : V → V → Prop) (W : Set Gamma.DPath) (x : V) : Prop :=
  x ∈ Gamma.vertexSet W ∧ ¬ ∃ y, (x, y) ∈ familyEdges W ∧ R x y

namespace OnePort

variable {R : V → V → Prop} {W K : Set Gamma.DPath} {s : V}

/-- Every old real edge survives the one-port splice. -/
theorem realFamilyEdges_subset
    (D : ColouredSafeOnePortSplice.Data W K s) :
    realFamilyEdges (Gamma := Gamma) R W ⊆
      realFamilyEdges (Gamma := Gamma) R D.paths := by
  rintro e ⟨heW, heR⟩
  exact ⟨by rw [D.familyEdges_paths]; exact Or.inl heW, heR⟩

/-- An old real terminal away from the processed port remains a real
terminal after a one-port splice. -/
theorem isRealTerminal_of_ne_port
    (D : ColouredSafeOnePortSplice.Data W K s) {x : V}
    (hx : IsRealTerminal (Gamma := Gamma) R W x) (hxs : x ≠ s) :
    IsRealTerminal (Gamma := Gamma) R D.paths x := by
  refine ⟨?_, ?_⟩
  · rw [D.vertexSet_paths]
    exact Or.inl hx.1
  · rintro ⟨y, hyU, hRxy⟩
    rw [D.familyEdges_paths] at hyU
    rcases hyU with hyW | hyK
    · exact hx.2 ⟨y, hyW, hRxy⟩
    · have hxK : x ∈ Gamma.vertexSet K :=
        (familyEdges_subset_vertexSet_prod K hyK).1
      have hxPort : x ∈ ({s} : Set V) := D.carrier_inter ⟨hxK, hx.1⟩
      exact hxs (Set.mem_singleton_iff.mp hxPort)

/-- The one-port splice simultaneously retains all old real edges and all
old real terminals away from its processed port. -/
theorem realLedger (D : ColouredSafeOnePortSplice.Data W K s) :
    realFamilyEdges (Gamma := Gamma) R W ⊆
        realFamilyEdges (Gamma := Gamma) R D.paths ∧
      ∀ x : V, IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R D.paths x :=
  ⟨realFamilyEdges_subset D,
    fun _ hx hxs => isRealTerminal_of_ne_port D hx hxs⟩

#print axioms realFamilyEdges_subset
#print axioms isRealTerminal_of_ne_port
#print axioms realLedger

end OnePort

namespace TwoPort

variable {R : V → V → Prop} {W K : Set Gamma.DPath} {s t : V}

/-- If the cut edge is not real, every old real edge survives the two-port
splice. -/
theorem realFamilyEdges_subset
    (D : ColouredSafeStrongTwoPortSplice.Data W K s t)
    (hcut : ¬ R s t) :
    realFamilyEdges (Gamma := Gamma) R W ⊆
      realFamilyEdges (Gamma := Gamma) R D.paths := by
  rintro e ⟨heW, heR⟩
  refine ⟨?_, heR⟩
  rw [D.familyEdges_paths]
  left
  refine ⟨heW, ?_⟩
  intro heCut
  have heEq : e = (s, t) := Set.mem_singleton_iff.mp heCut
  subst e
  exact hcut heR

/-- An old real terminal away from the processed source port remains a real
terminal after a two-port splice.  At the other possible carrier
intersection `t`, terminality in `K` excludes any new outgoing `K`-edge. -/
theorem isRealTerminal_of_ne_source
    (D : ColouredSafeStrongTwoPortSplice.Data W K s t)
    (htK : t ∈ Gamma.terminalFrontier K) {x : V}
    (hx : IsRealTerminal (Gamma := Gamma) R W x) (hxs : x ≠ s) :
    IsRealTerminal (Gamma := Gamma) R D.paths x := by
  refine ⟨?_, ?_⟩
  · rw [D.vertexSet_paths]
    exact Or.inl hx.1
  · rintro ⟨y, hyU, hRxy⟩
    rw [D.familyEdges_paths] at hyU
    rcases hyU with hyOld | hyK
    · exact hx.2 ⟨y, hyOld.1, hRxy⟩
    · have hxK : x ∈ Gamma.vertexSet K :=
        (familyEdges_subset_vertexSet_prod K hyK).1
      have hxPorts : x ∈ ({s, t} : Set V) :=
        D.carrier_inter ⟨hxK, hx.1⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxPorts
      rcases hxPorts with hxeqS | hxeqT
      · exact hxs hxeqS
      · subst x
        exact (Alternating.not_hasOutgoing_familyEdges_of_mem_terminalFrontier_anyWarp
          D.switch_isWarp htK) ⟨y, hyK⟩

/-- The two-port splice retains the whole old real-edge relation when its
single removed edge is not real, and retains all old real terminals except
possibly the processed source port. -/
theorem realLedger
    (D : ColouredSafeStrongTwoPortSplice.Data W K s t)
    (hcut : ¬ R s t)
    (htK : t ∈ Gamma.terminalFrontier K) :
    realFamilyEdges (Gamma := Gamma) R W ⊆
        realFamilyEdges (Gamma := Gamma) R D.paths ∧
      ∀ x : V, IsRealTerminal (Gamma := Gamma) R W x → x ≠ s →
        IsRealTerminal (Gamma := Gamma) R D.paths x :=
  ⟨realFamilyEdges_subset D hcut,
    fun _ hx hxs => isRealTerminal_of_ne_source D htK hx hxs⟩

#print axioms realFamilyEdges_subset
#print axioms isRealTerminal_of_ne_source
#print axioms realLedger

end TwoPort

end Erdos599.ColouredSafeSpliceRealTerminalLedger
