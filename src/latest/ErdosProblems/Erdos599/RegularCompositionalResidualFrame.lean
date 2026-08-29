/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularQuotientReentry
import ErdosProblems.Erdos599.SingularSelectedFreeze

/-!
# Compositional ambient quotient frames

The protected deletion/quotient state used by a one-step safe replacement is
not, in general, the deletion/quotient state associated with the restored
ambient row.  Iterating such a state therefore requires a genuine transport
certificate, rather than an equality between noncommuting operations.

For the quotient-only construction there is a canonical such certificate.
An `AmbientQuotientFrame` stores an ambient terminal-clean separating row and
uses the literal ambient quotient by its terminal stop-over as its residual
web.  `extend` is the compositional successor: a separating row in that
literal quotient is re-entered using `frozenRestrictedContinuation`.  The
nested quotient theorem proves that the successor residual is again the
literal ambient quotient by the new stop-over.

The frame also carries the completed source coordinates.  The successor
preserves all old target links and, under the exact routing and avoidance
hypotheses of quotient re-entry, adds the newly selected coordinates.  Thus
the state is not phantom: its web, row, boundary, forward-extension law, and
path-lift/routing law all participate in the successor proof.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCompositionalResidualFrame

open SingularExtension SingularContinuation SliceSpliceSource

universe u

variable {V : Type u}

/-- A genuinely compositional ambient restoration frame.  Its residual web
is definitionally `G.quotient boundary`; no deletion/quotient commutation is
part of the invariant. -/
structure AmbientQuotientFrame (G : DWeb V) where
  row : Set G.DPath
  boundary : Set V
  separating : IsSeparatingHalfwayStopover G row boundary
  terminalClean : TerminalCleanAt G row boundary
  completed : Set V
  completed_source : completed ⊆ G.source
  completed_links : LinksToTarget G (completedPart G row) completed

namespace AmbientQuotientFrame

/-- The residual web represented by an ambient quotient frame. -/
abbrev residual {G : DWeb V} (F : AmbientQuotientFrame G) : DWeb V :=
  G.quotient F.boundary

theorem residual_unhindered {G : DWeb V} (F : AmbientQuotientFrame G) :
    F.residual.IsUnhindered :=
  F.separating.quotient_unhindered

theorem row_isWarp {G : DWeb V} (F : AmbientQuotientFrame G) : G.IsWarp F.row :=
  F.separating.linkage.isWarp

theorem row_finite {G : DWeb V} (F : AmbientQuotientFrame G) :
    G.HasFiniteCharacter F.row :=
  F.separating.linkage.finiteCharacter

theorem row_initialSet {G : DWeb V} (F : AmbientQuotientFrame G) :
    G.initialSet F.row = G.source :=
  F.separating.linkage.initialSet_eq

/-- Old completed coordinates remain target-linked after any finite full-row
forward extension.  This is the preservation component used by `extend`. -/
theorem completedLinks_of_forwardExtension
    {G : DWeb V} (hNorm : G.IsNormalized)
    (F : AmbientQuotientFrame G) {W' : Set G.DPath}
    (hforward : G.ForwardExtension F.row W')
    (hfinite : G.HasFiniteCharacter W') :
    LinksToTarget G W' F.completed := by
  have hlinksRow : LinksToTarget G F.row F.completed := by
    intro a ha
    obtain ⟨p, hp, hpa⟩ := F.completed_links a ha
    exact ⟨p, hp.1, hpa⟩
  exact SingularExtension.linksToTarget_of_forwardExtension hNorm
    F.completed_source hlinksRow hforward hfinite

/-- The exact quotient-reentry successor.

`A` is the set of starts in the current quotient row which carry the new
target links.  `B` is the corresponding set of original ambient sources;
`route` exhibits the owner/prefix map from each `B`-component of the old
ambient row to its terminal in `A`.  The avoidance `A ⊆ Eᶜ` is precisely
what guarantees that quotient restriction does not discard those paths. -/
theorem extend
    {G : DWeb V} (hNorm : G.IsNormalized)
    (F : AmbientQuotientFrame G)
    {U : Set F.residual.DPath} {E A B : Set V}
    (hE : IsSeparatingHalfwayStopover F.residual U E)
    (hB : B ⊆ G.source)
    (hA : A ⊆ F.residual.source)
    (hAE : A ⊆ Eᶜ)
    (hroute : SingularQuotientReentry.RoutesTerminals
      G F.row B A)
    (hlinks : LinksToTarget F.residual U A) :
    ∃ F' : AmbientQuotientFrame G,
      F'.row = SingularQuotientReentry.frozenRestrictedContinuation
        G F.separating F.terminalClean hE ∧
      F'.boundary = E ∧
      F'.completed = F.completed ∪ B ∧
      G.ForwardExtension F.row F'.row := by
  let W' : Set G.DPath :=
    SingularQuotientReentry.frozenRestrictedContinuation
      G F.separating F.terminalClean hE
  have hstruct :=
    SingularQuotientReentry.frozenRestrictedContinuation_structural
      hNorm F.separating F.terminalClean hE
  have hnew : LinksToTarget G W' B := by
    exact SingularQuotientReentry.linksToTarget_frozenRestrictedContinuation
      hNorm F.separating F.terminalClean hE hB hA hAE hroute hlinks
  have hold : LinksToTarget G W' F.completed := by
    exact F.completedLinks_of_forwardExtension hNorm hstruct.2.2.1
      hstruct.1.stopover.linkage.finiteCharacter
  have hall : LinksToTarget G W' (F.completed ∪ B) := by
    exact SingularSelectedFreeze.linksToTarget_union_of_normalized
      hNorm F.completed_source hB hold hnew
  have hallCompleted : LinksToTarget G (completedPart G W')
      (F.completed ∪ B) :=
    linksToTarget_completedPart hNorm hall
  let F' : AmbientQuotientFrame G :=
    { row := W'
      boundary := E
      separating := hstruct.1
      terminalClean := hstruct.2.1
      completed := F.completed ∪ B
      completed_source := Set.union_subset F.completed_source hB
      completed_links := hallCompleted }
  exact ⟨F', rfl, rfl, rfl, hstruct.2.2.1⟩

/-- The successor residual is literally the new ambient quotient.  This
small projection is useful to prevent callers from replacing it by an
iterated deletion/quotient expression. -/
@[simp] theorem extend_residual
    {G : DWeb V} (hNorm : G.IsNormalized)
    (F : AmbientQuotientFrame G)
    {U : Set F.residual.DPath} {E A B : Set V}
    (hE : IsSeparatingHalfwayStopover F.residual U E)
    (hB : B ⊆ G.source) (hA : A ⊆ F.residual.source)
    (hAE : A ⊆ Eᶜ)
    (hroute : SingularQuotientReentry.RoutesTerminals G F.row B A)
    (hlinks : LinksToTarget F.residual U A) :
    let F' := Classical.choose
      (F.extend hNorm hE hB hA hAE hroute hlinks)
    F'.residual = G.quotient E := by
  dsimp only
  have hspec := Classical.choose_spec
    (F.extend hNorm hE hB hA hAE hroute hlinks)
  change G.quotient
      (Classical.choose
        (F.extend hNorm hE hB hA hAE hroute hlinks)).boundary =
    G.quotient E
  rw [hspec.2.1]

end AmbientQuotientFrame

end RegularCompositionalResidualFrame
end CardinalInduction
end Erdos599
