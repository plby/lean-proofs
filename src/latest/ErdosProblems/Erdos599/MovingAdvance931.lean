/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayClause
import ErdosProblems.Erdos599.IntermediateRelationLimitRefinement

/-!
# The moving-slice 9.31--9.34 interface

Assertion 9.30 reaches the old slice. Assertion 9.31 then produces a stable
blueprint at a later slice, not at the old one. This module retains both
slice parameters while composing the concrete reachability, terminal
preservation, and real-extension certificates. No transport of the new roof
back into the old roof is asserted.
-/

noncomputable section

open Cardinal Set

namespace Erdos599.Blueprint.LinkageBlueprint

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The actual heterogeneous-slice output of Assertion 9.31 needed for
9.34. Terminal preservation refers to the old slice, while the resulting
blueprint and its stability are certified at the new slice. -/
structure MovingAdvance931 (W current U : LinkageBlueprint Gamma Y kappa)
    (z : V) (Told Tnew Z persistent B : Set V) : Prop where
  conclusion : AdvanceConclusion current U z Told persistent B
  isBlueprint : U.IsLinkageBlueprint Tnew Z persistent
  stable : U.Stable Tnew persistent
  family_extends : current.familyGraph.Extends U.familyGraph
  real_extends : current.realPart.Extends U.realPart
  preserves_except : current.realPart.terminals \ {z} ⊆ U.realPart.terminals
  preserves_inherited_full_terminals :
    ∀ x, x ∈ W.terminalSet → x ∈ current.terminalSet → x ≠ z →
      x ∈ U.terminalSet

/-- The fixed-slice helper is the diagonal case, not the general source
statement. -/
theorem Advance931.toMoving
    {W current U : LinkageBlueprint Gamma Y kappa} {z : V}
    {T Z persistent B : Set V}
    (h : Advance931 W current U z T Z persistent B) :
    MovingAdvance931 W current U z T T Z persistent B :=
  ⟨h.conclusion, h.isBlueprint, h.stable, h.family_extends,
    h.real_extends, h.preserves_except, h.preserves_inherited_full_terminals⟩

/-- Assertions 9.30 and 9.31 compose with their different slice indices
intact. The result is certified at `Tnew`. -/
theorem movingAssertion934_of_930_931
    {W cut current U : LinkageBlueprint Gamma Y kappa} {u z : V}
    {Told Tnew Z persistent B : Set V}
    (h30 : Continuation930 W cut current u z Told B)
    (h31 : MovingAdvance931 W current U z Told Tnew Z persistent B) :
    StableExtensionConclusion W U u Tnew Z persistent B := by
  have hlinksUZ : U.RealLinksTo u {z} :=
    realLinksTo_mono h31.real_extends h30.links_to_endpoint
  have hlinksUB : U.RealLinksTo u B :=
    realLinksTo_trans hlinksUZ h31.conclusion.links
  have hreal : W.RealExtends U B := by
    refine ⟨FamilyGraph.extends_trans
      h30.real_extends_to_endpoint.1 h31.real_extends, ?_⟩
    intro x hxW
    rcases h30.real_extends_to_endpoint.2 hxW with hxAB | hxcomplete
    · rcases hxAB with hxterm | hxedge
      · rcases hxterm with ⟨hxCurrent, hxWterm⟩
        by_cases hxz : x = z
        · subst x
          exact Or.inr h31.conclusion.links.start_mem_completedRealVertices
        · exact Or.inl (Or.inl
            ⟨h31.preserves_inherited_full_terminals x hxWterm hxCurrent hxz,
              hxWterm⟩)
      · rcases hxedge with ⟨y, hyW, hyCurrent⟩
        exact Or.inl (Or.inr ⟨y, hyW, h31.family_extends.2 hyCurrent⟩)
    · have hxCurrent : current.RealLinksTo x {z} :=
        realLinksTo_of_mem_completedRealVertices hxcomplete
      have hxU : U.RealLinksTo x {z} :=
        realLinksTo_mono h31.real_extends hxCurrent
      exact Or.inr
        (realLinksTo_trans hxU h31.conclusion.links).start_mem_completedRealVertices
  refine ⟨h31.isBlueprint, h31.stable, hreal, hlinksUB, ?_⟩
  intro x hx
  have hxCurrent := h30.preserves_other_terminals hx
  have hxne : x ≠ z := by
    intro hxz
    subst x
    exact h30.endpoint_fresh hx
  exact h31.preserves_except ⟨hxCurrent, hxne⟩

/-- The concrete predecessor-refinement certificates compose independently
of the moving slice index. -/
theorem movingAssertion934_of_refining_930_931
    {W cut current U : LinkageBlueprint Gamma Y kappa} {u z : V}
    {Told Tnew Z persistent B : Set V}
    (h30 : Continuation930 W cut current u z Told B)
    (h31 : MovingAdvance931 W current U z Told Tnew Z persistent B)
    (h30refines : W.PredecessorRefines current)
    (h31refines : current.PredecessorRefines U) :
    StableExtensionConclusion W U u Tnew Z persistent B ∧
      W.PredecessorRefines U := by
  refine ⟨movingAssertion934_of_930_931 h30 h31, ?_⟩
  exact h30refines.trans h31refines
    h30.real_extends_to_endpoint.1.1 h31.real_extends.2

/-- The stage-indexed existential form preserves the strict advance supplied
by the actual 9.31 construction. -/
theorem exists_indexedAssertion934
    {I : Type v} [LT I] (slice closure : I → Set V) (i : I)
    {W : LinkageBlueprint Gamma Y kappa} {u : V} {persistent B : Set V}
    (h30 : ∃ (cut current : LinkageBlueprint Gamma Y kappa) (z : V),
      Continuation930 W cut current u z (slice i) B ∧
        W.PredecessorRefines current)
    (h31 : ∀ (cut current : LinkageBlueprint Gamma Y kappa) (z : V),
      Continuation930 W cut current u z (slice i) B →
        ∃ (j : I) (U : LinkageBlueprint Gamma Y kappa), i < j ∧
          MovingAdvance931 W current U z (slice i) (slice j)
            (closure j) persistent B ∧ current.PredecessorRefines U) :
    ∃ (j : I) (U : LinkageBlueprint Gamma Y kappa), i < j ∧
      StableExtensionConclusion W U u (slice j) (closure j) persistent B ∧
        W.PredecessorRefines U := by
  obtain ⟨cut, current, z, hcontinue, hcontinueRefines⟩ := h30
  obtain ⟨j, U, hij, hadvance, hadvanceRefines⟩ := h31 cut current z hcontinue
  exact ⟨j, U, hij, movingAssertion934_of_refining_930_931
    hcontinue hadvance hcontinueRefines hadvanceRefines⟩

#print axioms movingAssertion934_of_930_931
#print axioms movingAssertion934_of_refining_930_931
#print axioms exists_indexedAssertion934

end Erdos599.Blueprint.LinkageBlueprint
