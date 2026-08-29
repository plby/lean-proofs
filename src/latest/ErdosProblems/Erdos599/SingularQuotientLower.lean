/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularQuotientDelete
import ErdosProblems.Erdos599.SliceHalfwayCore
import ErdosProblems.Erdos599.SafeLinkBridge

/-!
# Lower-cardinal selection in a singular quotient-delete web

At a singular successor stage the pending boundary is a subset of the
source of a quotient followed by a deletion.  Applying the lower induction
hypothesis to that entire auxiliary source would produce paths starting at
unrelated old sources.  The continuation splice instead needs every new
path to start on the pending boundary (and hence in the current commitment
set).

The correct auxiliary web is therefore the `sourceSubweb` on the pending
boundary.  Provided the quotient-delete web is unhindered, source-subweb
inheritance and the separating lower half-way clause choose a family whose
ambient initial set is *exactly* that boundary.  This file packages that
selection and all of the geometric projections consumed by
`SingularQuotientDelete`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExtension

universe u

variable {V : Type u}

/-- Apply the strong lower half-way clause to the source-subweb on `A`.

The conclusion retains the separating stop-over and height certificate in
the source-subweb, and also exposes the ambient-web facts needed by a
singular continuation: warp and finite character, exact initial set,
source membership, and containment in the commitment set `C`. -/
theorem exists_sourceSubwebSeparatingHalfway_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (H : DWeb V) (hH : H.IsUnhindered)
    (hNoEnter : H.NoEdgeEnters H.source)
    {A C : Set V} (hAsource : A ⊆ H.source) (hAC : A ⊆ C)
    (hAInfinite : aleph0 ≤ #A) (hAcard : #A < kappa) :
    ∃ (U : Set H.DPath) (D : Set V),
      IsSeparatingHalfwayStopover (H.sourceSubweb A) U D ∧
      LinksToTarget (H.sourceSubweb A) U A ∧
      HeightAtMost (H.sourceSubweb A) D (#A) ∧
      H.IsWarp U ∧ H.HasFiniteCharacter U ∧
      H.initialSet U = A ∧
      H.initialSet U ⊆ H.source ∧ H.initialSet U ⊆ C ∧
      (H.sourceSubweb A).terminalFrontier U = D := by
  have hSub : (H.sourceSubweb A).IsUnhindered :=
    hH.sourceSubweb H hNoEnter hAsource
  obtain ⟨U, D, hstop, hlinks, hheight, hfrontier⟩ :=
    (hlower #A hAcard (H.sourceSubweb A) hSub).separatingHalfway
      hAInfinite A (by simp) rfl
  have hinitial : H.initialSet U = A := by
    simpa using hstop.linkage.initialSet_eq
  refine ⟨U, D, hstop, hlinks, hheight, ?_, ?_, hinitial, ?_, ?_,
    hfrontier⟩
  · exact (H.sourceSubweb_isWarp A U).mp hstop.linkage.isWarp
  · exact hstop.linkage.finiteCharacter
  · rw [hinitial]
    exact hAsource
  · rw [hinitial]
    exact hAC

/-- Quotient-then-deletion specialization of
`exists_sourceSubwebSeparatingHalfway_of_lower`.

This is the direct producer for the family consumed by
`exists_frozenPendingContinuation_of_quotientDeleteFamily`.  In particular,
the final two conclusions are precisely that theorem's `hUsource` and
`hUstart` premises. -/
theorem exists_quotientDeleteSeparatingHalfway_of_lower
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (G : DWeb V) {C Q A : Set V}
    (hAux : ((G.quotient C).delete Q).IsUnhindered)
    (hNoEnter : ((G.quotient C).delete Q).NoEdgeEnters
      ((G.quotient C).delete Q).source)
    (hAsource : A ⊆ ((G.quotient C).delete Q).source)
    (hAC : A ⊆ C)
    (hAInfinite : aleph0 ≤ #A) (hAcard : #A < kappa) :
    ∃ (U : Set ((G.quotient C).delete Q).DPath) (D : Set V),
      IsSeparatingHalfwayStopover
        (((G.quotient C).delete Q).sourceSubweb A) U D ∧
      LinksToTarget (((G.quotient C).delete Q).sourceSubweb A) U A ∧
      HeightAtMost (((G.quotient C).delete Q).sourceSubweb A) D (#A) ∧
      ((G.quotient C).delete Q).IsWarp U ∧
      ((G.quotient C).delete Q).HasFiniteCharacter U ∧
      ((G.quotient C).delete Q).initialSet U = A ∧
      ((G.quotient C).delete Q).initialSet U ⊆
        ((G.quotient C).delete Q).source ∧
      ((G.quotient C).delete Q).initialSet U ⊆ C ∧
      ((((G.quotient C).delete Q).sourceSubweb A).terminalFrontier U = D) := by
  exact exists_sourceSubwebSeparatingHalfway_of_lower
    hlower ((G.quotient C).delete Q) hAux hNoEnter
      hAsource hAC hAInfinite hAcard

/-- In a normalized ambient web, the no-incoming-source premise for the
quotient-delete specialization is automatic. -/
theorem exists_quotientDeleteSeparatingHalfway_of_lower_of_normalized
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (G : DWeb V) (hNorm : G.IsNormalized) {C Q A : Set V}
    (hAux : ((G.quotient C).delete Q).IsUnhindered)
    (hAsource : A ⊆ ((G.quotient C).delete Q).source)
    (hAC : A ⊆ C)
    (hAInfinite : aleph0 ≤ #A) (hAcard : #A < kappa) :
    ∃ (U : Set ((G.quotient C).delete Q).DPath) (D : Set V),
      IsSeparatingHalfwayStopover
        (((G.quotient C).delete Q).sourceSubweb A) U D ∧
      LinksToTarget (((G.quotient C).delete Q).sourceSubweb A) U A ∧
      HeightAtMost (((G.quotient C).delete Q).sourceSubweb A) D (#A) ∧
      ((G.quotient C).delete Q).IsWarp U ∧
      ((G.quotient C).delete Q).HasFiniteCharacter U ∧
      ((G.quotient C).delete Q).initialSet U = A ∧
      ((G.quotient C).delete Q).initialSet U ⊆
        ((G.quotient C).delete Q).source ∧
      ((G.quotient C).delete Q).initialSet U ⊆ C ∧
      ((((G.quotient C).delete Q).sourceSubweb A).terminalFrontier U = D) := by
  have hAuxNoEnter : ((G.quotient C).delete Q).NoEdgeEnters
      ((G.quotient C).delete Q).source := by
    intro x y hxy hy
    rcases hy.1.1 with hyOld | hyC
    · exact (hNorm hxy.1.1).1 hyOld
    · exact hxy.1.2.2.2 hyC
  exact exists_quotientDeleteSeparatingHalfway_of_lower
    hlower G hAux hAuxNoEnter hAsource hAC hAInfinite hAcard

end SingularExtension
end CardinalInduction
end Erdos599
