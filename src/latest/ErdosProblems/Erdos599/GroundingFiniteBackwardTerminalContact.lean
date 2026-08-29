/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingDichotomy
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# The canonical backward terminal contact of a finite warp member

A nontrivial finite member of a warp can always be traversed as one
backward alternating link.  This elementary normalization is independent
of the auxiliary decoder and is the common local construction behind both
finite-boundary collisions and finite-source root obstructions.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open _root_.Erdos599.DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The whole-path backward traversal of a nontrivial finite warp member is
an honest terminal-contact switch.  Its alternating initial is the old
path's terminal and its terminal contact is the old path's initial. -/
theorem exists_wholePathBackwardTerminalContactSwitching
    (Z : Set Gamma.DPath) (hZ : Gamma.IsWarp Z)
    (p : FinitePath Gamma.graph)
    (hp : (Sum.inl p : Gamma.DPath) ∈ Z)
    (hne : p.start ≠ p.finish) :
    ∃ Q : FiniteTrace Gamma.graph,
      IsTerminalContactSwitching Z Q p.start ∧
        Q.initial = p.finish := by
  let l : Link Gamma.graph := ⟨p, .backward, hne⟩
  let Q : FiniteTrace Gamma.graph := FiniteTrace.singleton l
  have hbracket : IsBracketSwitchingAlternating Z Z (.finite Q) := by
    simpa only [Q, l, AltPath.single] using
      (isBracketSwitchingAlternating_single_backward
        (U := Z) (Z := Z) hZ p hp hne)
  have hswitch := hbracket.isSwitchingAlternating
  have huInitial : p.start ∈ Gamma.initialSet Z :=
    ⟨Sum.inl p, hp, rfl⟩
  have huOutgoing : HasOutgoing (familyEdges Z) p.start := by
    obtain ⟨z, hz⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        p p.start_mem_support hne
    exact ⟨z, Set.mem_iUnion.2
      ⟨Sum.inl p, Set.mem_iUnion.2 ⟨hp, hz⟩⟩⟩
  have hcontact : IsTerminalContactSwitching Z Q p.start := by
    refine
      { warp := hswitch.1.1
        backwardLinksOn := hswitch.1.2.1
        forwardLinksOff := hswitch.2.1
        contactsCoveredAtTerminal := ?_
        firstForwardInitialOff := hswitch.1.2.2.1
        terminal_eq := by simp [Q, l, Link.exit]
        terminal_mem_initialSet := huInitial
        terminal_outgoing_or_isolated := Or.inl huOutgoing
        noForwardOutgoingAtTerminal := by
          rintro ⟨z, hz⟩
          simp only [AltPath.directionEdges, Set.mem_iUnion] at hz
          obtain ⟨k, hk, hdir, _he⟩ := hz
          have hkEq : k = l := by
            simp only [AltPath.links, FiniteTrace.links,
              Set.mem_range] at hk
            obtain ⟨i, rfl⟩ := hk
            have hi : i = 0 := Fin.eq_zero i
            subst i
            rfl
          subst k
          simp [l] at hdir }
    intro x hxForward hxZ
    exact Or.inl (hswitch.2.2 ⟨hxForward, hxZ⟩)
  exact ⟨Q, hcontact, by simp [Q, l, Link.entry]⟩

end Alternating
end Erdos599

#print axioms
  Erdos599.Alternating.exists_wholePathBackwardTerminalContactSwitching
