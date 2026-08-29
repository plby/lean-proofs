/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularContinuation

/-!
# An obstruction to terminal-cleaning a half-way linkage

A target-linked member of a warp in a normalized web ends at the target
vertex which it visits.  Consequently, if the family is terminal-clean at
`C`, a designated non-target vertex cannot itself belong to `C`: that
vertex lies on the selected member, so cleanliness would also make it the
member's terminal.

This is the precise missing premise in an attempted unconditional
"first-hit tightening" of a weak half-way linkage.  The public predicate
`IsHalfwayLinkageOfAltitude` does not require its designated set to be
disjoint from its stop-over (or from the canonical separating enlargement
of that stop-over).
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularInitialTightObstruction

universe u

variable {V : Type u}

/-- A terminal-clean family which links `A` to the target has no
non-target designated vertex on its clean boundary. -/
theorem disjoint_designated_nonTarget_of_terminalClean
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A C : Set V}
    (hlinks : LinksToTarget G W A)
    (hclean : SingularContinuation.TerminalCleanAt G W C) :
    Disjoint (A \ G.target) C := by
  rw [Set.disjoint_left]
  intro a ha hC
  obtain ⟨p, hpW, q, hpq, hpure, before, after, hsupport,
    b, hbTarget, hbAfter⟩ := hlinks a ha.1
  subst p
  have haSupport : a ∈ q.support := by
    have haInter : a ∈ q.support ∩ A := by
      rw [hpure]
      exact Set.mem_singleton a
    exact haInter.1
  have hterminalA : G.terminal? (.inl q : G.DPath) = some a :=
    hclean (.inl q) hpW a haSupport hC
  have hbSupport : b ∈ q.support := by
    change b ∈ q.walk.support
    rw [hsupport]
    exact List.mem_append_right before hbAfter
  have hterminalB : G.terminal? (.inl q : G.DPath) = some b :=
    hNorm.terminal?_eq_of_mem_path (.inl q) hbSupport hbTarget
  have hab : a = b :=
    Option.some.inj (hterminalA.symm.trans hterminalB)
  exact ha.2 (hab ▸ hbTarget)

/-- Pointwise form of
`disjoint_designated_nonTarget_of_terminalClean`. -/
theorem designated_mem_boundary_imp_target
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A C : Set V}
    (hlinks : LinksToTarget G W A)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {a : V} (ha : a ∈ A) (haC : a ∈ C) :
    a ∈ G.target := by
  by_contra haTarget
  exact Set.disjoint_left.1
    (disjoint_designated_nonTarget_of_terminalClean hNorm hlinks hclean)
    ⟨ha, haTarget⟩ haC

end SingularInitialTightObstruction
end CardinalInduction
end Erdos599

