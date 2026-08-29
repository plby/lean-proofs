/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularContinuation
import ErdosProblems.Erdos599.QuotientAssociativity

/-!
# Composing separating half-way stopovers

This file isolates the quotient-composition calculation used at a singular
successor step.  If `C` is a separating trimmed stopover in `G` and `D` is
a separating trimmed stopover in `G / C`, the ambient stopover is the
essential core of `C ∪ D`.  In a normalized web its quotient is exactly the
iterated quotient `(G / C) / D`.

The terminal-clean hypothesis is kept explicit.  It is precisely the
geometric premise needed by `SingularContinuation.continuation`; it is not a
formal consequence of trimmedness when the source can meet the stopover.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularHalfwayComposition

universe u

variable {V : Type u}

/-- The ambient stopover obtained after first stopping at `C` and then at
`D` in the quotient by `C`. -/
def composedStopover (G : DWeb V) (C D : Set V) : Set V :=
  G.essential (C ∪ D)

/-- The composed stopover is trimmed by construction. -/
theorem composedStopover_isTrimmedSeparator
    (G : DWeb V) (C D : Set V) :
    IsTrimmedSeparator G (composedStopover G C D) := by
  exact G.essential_idem (C ∪ D)

/-- A separator at the first stage still roofs the source after the second
commitment set is adjoined. -/
theorem source_subset_roof_union
    (G : DWeb V) {C D : Set V}
    (hC : IsSeparatorFrom G G.source C) :
    G.source ⊆ G.roof (C ∪ D) := by
  exact hC.trans (G.roof_mono Set.subset_union_left)

/-- Essentializing the union does not change its roof, so the composed
stopover is again a separator from the original source. -/
theorem composedStopover_isSeparatorFrom
    (G : DWeb V) {C D : Set V}
    (hC : IsSeparatorFrom G G.source C) :
    IsSeparatorFrom G G.source (composedStopover G C D) := by
  rw [IsSeparatorFrom, composedStopover, G.roof_essential]
  exact source_subset_roof_union G hC

/-- Normalized quotient associativity in the form used by the singular
half-way recursion. -/
theorem quotient_composedStopover_eq_iterated
    (G : DWeb V) (hG : G.IsNormalized) {C D : Set V}
    (hC : IsSeparatorFrom G G.source C) :
    G.quotient (composedStopover G C D) =
      (G.quotient C).quotient D := by
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  calc
    G.quotient (composedStopover G C D) = G.quotient (C ∪ D) := by
      exact G.quotient_essential_eq_of_subset_roof (C ∪ D)
        (source_subset_roof_union G hC)
    _ = (G.quotient C).quotient D :=
      (G.quotient_quotient_eq_union C D hNoEnter).symm

/-- Unhinderedness of the second quotient transports to the ambient
essential union. -/
theorem quotient_composedStopover_isUnhindered
    (G : DWeb V) (hG : G.IsNormalized) {C D : Set V}
    (hC : IsSeparatorFrom G G.source C)
    (hD : ((G.quotient C).quotient D).IsUnhindered) :
    (G.quotient (composedStopover G C D)).IsUnhindered := by
  rw [quotient_composedStopover_eq_iterated G hG hC]
  exact hD

/-- Once both stopovers are separating and trimmed, the quotient-stage
stopover `D` is literally the ambient essential union.  This is the useful
endpoint identity: it converts the terminal set of quotient paths into the
terminal set of the ambient continuation. -/
theorem composedStopover_eq_second
    (G : DWeb V) (hG : G.IsNormalized) {C D : Set V}
    (hCsep : IsSeparatorFrom G G.source C)
    (hCtrim : IsTrimmedSeparator G C)
    {U : Set (G.quotient C).DPath}
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    composedStopover G C D = D := by
  have hEsep : IsSeparatorFrom G G.source (composedStopover G C D) :=
    composedStopover_isSeparatorFrom G hCsep
  have hEtrim : IsTrimmedSeparator G (composedStopover G C D) :=
    composedStopover_isTrimmedSeparator G C D
  calc
    composedStopover G C D =
        (G.quotient (composedStopover G C D)).source :=
      (SingularContinuation.quotient_source_eq_stopover
        G hEsep hEtrim).symm
    _ = ((G.quotient C).quotient D).source := by
      rw [quotient_composedStopover_eq_iterated G hG hCsep]
    _ = D := SingularContinuation.quotient_source_eq_stopover
      (G.quotient C) hD.separator hD.stopover.minimal

/-- The actual ambient family obtained by source-star continuation. -/
noncomputable def composedContinuation
    (G : DWeb V) {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    Set G.DPath :=
  SingularContinuation.continuation G hC.linkage hC.separator
    hC.stopover.minimal hclean U hD.linkage.initialSet_eq

/-- The composed continuation is a warp. -/
theorem composedContinuation_isWarp
    (G : DWeb V) {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    G.IsWarp (composedContinuation G hC hclean U hD) := by
  exact SingularContinuation.continuation_isWarp G hC.linkage
    hC.separator hC.stopover.minimal hclean hD.linkage.isWarp
    hD.linkage.initialSet_eq

/-- The composed continuation has finite character. -/
theorem composedContinuation_finiteCharacter
    (G : DWeb V) {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    G.HasFiniteCharacter (composedContinuation G hC hclean U hD) := by
  exact SingularContinuation.continuation_finiteCharacter G hC.linkage
    hC.separator hC.stopover.minimal hclean hD.linkage.finiteCharacter
    hD.linkage.initialSet_eq

/-- The composed continuation retains every original source exactly once. -/
theorem initialSet_composedContinuation
    (G : DWeb V) {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    G.initialSet (composedContinuation G hC hclean U hD) = G.source := by
  exact SingularContinuation.initialSet_continuation G hC.linkage
    hC.separator hC.stopover.minimal hclean U hD.linkage.initialSet_eq

/-- Every terminal of the continued ambient family lies in the composed
stopover. -/
theorem terminalFrontier_composedContinuation_subset
    (G : DWeb V) (hG : G.IsNormalized)
    {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    G.terminalFrontier (composedContinuation G hC hclean U hD) ⊆
      composedStopover G C D := by
  have hfront := SingularContinuation.terminalFrontier_continuation_subset
    G hC.linkage hC.separator hC.stopover.minimal hclean
      hD.linkage.initialSet_eq
  rw [G.terminalFrontier_liftQuotientFamily] at hfront
  rw [composedStopover_eq_second G hG hC.separator
    hC.stopover.minimal hD]
  exact hfront.trans hD.linkage.terminalFrontier_subset

/-- The continuation is a genuine forward extension of the first
half-way linkage. -/
theorem forwardExtension_composedContinuation
    (G : DWeb V) {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    (U : Set (G.quotient C).DPath)
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D) :
    G.ForwardExtension W (composedContinuation G hC hclean U hD) := by
  exact SingularContinuation.forwardExtension_continuation G hC.linkage
    hC.separator hC.stopover.minimal hclean U hD.linkage.initialSet_eq

end SingularHalfwayComposition
end CardinalInduction
end Erdos599

