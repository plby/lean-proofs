/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedBackwardSubtrace

/-!
# Internal safeness when only backward links are literal

Contact splitting replaces the two boundary forward links by subpaths, so
not every child link occurs literally in the parent.  Every backward link,
however, is unchanged.  Since owner data are required only in the backward
case, this weaker restriction is sufficient for the full indexed interval
certificate.
-/

noncomputable section

open Set

namespace Erdos599

open DirectedPath

namespace Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}
variable {parent child : AltPath Gamma.graph} {I : Type w}

namespace AltPath.IndexedBackwardProvenance

noncomputable def backwardParentIndex
    (P : parent.IndexedBackwardProvenance Y I)
    (hback : ∀ l ∈ child.links, l.direction = .backward → l ∈ parent.links)
    (l : {l // l ∈ child.links}) (hd : l.1.direction = .backward) : I :=
  Classical.choose (by
    rw [P.links_eq_range] at hback
    exact hback l.1 l.2 hd)

theorem link_backwardParentIndex
    (P : parent.IndexedBackwardProvenance Y I)
    (hback : ∀ l ∈ child.links, l.direction = .backward → l ∈ parent.links)
    (l : {l // l ∈ child.links}) (hd : l.1.direction = .backward) :
    P.link (P.backwardParentIndex hback l hd) = l.1 :=
  Classical.choose_spec (by
    rw [P.links_eq_range] at hback
    exact hback l.1 l.2 hd)

/-- Restrict indexed owners using literal containment only in the backward
case; split forward boundary links need no owner. -/
noncomputable def restrictBackwardLinks
    (P : parent.IndexedBackwardProvenance Y I)
    (hback : ∀ l ∈ child.links, l.direction = .backward → l ∈ parent.links) :
    child.IndexedBackwardProvenance Y {l // l ∈ child.links} where
  link l := l.1
  links_eq_range := by
    ext l
    constructor
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact l.2
  owner l hd := P.owner (P.backwardParentIndex hback l hd)
    (by simpa [P.link_backwardParentIndex hback l hd] using hd)
  owner_mem l hd := P.owner_mem (P.backwardParentIndex hback l hd)
    (by simpa [P.link_backwardParentIndex hback l hd] using hd)
  isSubpath l hd := by
    have h := P.isSubpath (P.backwardParentIndex hback l hd)
      (by simpa [P.link_backwardParentIndex hback l hd] using hd)
    simpa [P.link_backwardParentIndex hback l hd] using h
  owner_unique := by
    intro l r hl hr howner
    have hlink := P.owner_unique
      (P.backwardParentIndex hback l hl)
      (P.backwardParentIndex hback r hr)
      (by simpa [P.link_backwardParentIndex hback l hl] using hl)
      (by simpa [P.link_backwardParentIndex hback r hr] using hr)
      howner
    simpa [P.link_backwardParentIndex hback l hl,
      P.link_backwardParentIndex hback r hr] using hlink

end AltPath.IndexedBackwardProvenance
end Alternating

namespace Blueprint

open _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}
variable {parent child : AltPath Gamma.graph} {I : Type w}

/-- Internal safeness of a contact subtrace: only its backward links must be
literal parent links, while its whole edge set is a parent subset. -/
theorem InternallySafe.of_backwardLiteralSubtrace
    (hparent : IsSafe Y parent)
    (P : parent.IndexedBackwardProvenance Y I)
    (hback : ∀ l ∈ child.links, l.direction = .backward → l ∈ parent.links)
    (hedges : child.edgeSet ⊆ parent.edgeSet) :
    InternallySafe Y child := by
  let Pchild := P.restrictBackwardLinks hback
  refine ⟨hparent.1.1, Pchild.backwardLinksOn,
    Pchild.intervals hparent.1.1, ?_, ?_⟩
  · rintro ⟨R, hR⟩
    exact hparent.2.2.1 ⟨R, hR.trans (by
      rintro e ⟨he, hnot⟩
      exact ⟨hedges he, hnot⟩)⟩
  · rintro ⟨C, hC⟩
    exact hparent.2.2.2 ⟨C, hC.trans (by
      rintro e ⟨he, hnot⟩
      exact ⟨hedges he, hnot⟩)⟩

end Blueprint
end Erdos599

#print axioms Erdos599.Alternating.AltPath.IndexedBackwardProvenance.restrictBackwardLinks
#print axioms Erdos599.Blueprint.InternallySafe.of_backwardLiteralSubtrace
