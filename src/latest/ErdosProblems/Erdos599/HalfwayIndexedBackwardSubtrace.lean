/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayEndpointCoveredClaim2
import ErdosProblems.Erdos599.AlternatingMacroProvenance

/-!
# Internal safeness of literal compressed subtraces

The maximal-run compressor supplies an injectively owned enumeration of all
parent links.  Any child whose links occur literally in the parent inherits
the same indexed owner certificate.  If its edge set is also contained in
the parent, internal safeness follows from parent safeness: the exact
reference intervals come from the restricted owner certificate, and the
ray/cycle exclusions are monotone under edge-set containment.
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

/-- A canonical parent index for every literal child link. -/
noncomputable def childParentIndex
    (P : parent.IndexedBackwardProvenance Y I)
    (hlinks : child.links ⊆ parent.links)
    (l : {l // l ∈ child.links}) : I :=
  Classical.choose (by
    rw [P.links_eq_range] at hlinks
    exact hlinks l.2)

theorem link_childParentIndex
    (P : parent.IndexedBackwardProvenance Y I)
    (hlinks : child.links ⊆ parent.links)
    (l : {l // l ∈ child.links}) :
    P.link (P.childParentIndex hlinks l) = l.1 :=
  Classical.choose_spec (by
    rw [P.links_eq_range] at hlinks
    exact hlinks l.2)

/-- Restrict the concrete compressor enumeration to an arbitrary literal
subtrace.  Forward links are indexed as well, exactly as required by
`IndexedBackwardProvenance.links_eq_range`. -/
noncomputable def restrictLinks
    (P : parent.IndexedBackwardProvenance Y I)
    (hlinks : child.links ⊆ parent.links) :
    child.IndexedBackwardProvenance Y {l // l ∈ child.links} where
  link l := l.1
  links_eq_range := by
    ext l
    constructor
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨l, rfl⟩
      exact l.2
  owner l hd :=
    P.owner (P.childParentIndex hlinks l)
      (by simpa [P.link_childParentIndex hlinks l] using hd)
  owner_mem l hd := by
    exact P.owner_mem (P.childParentIndex hlinks l)
      (by simpa [P.link_childParentIndex hlinks l] using hd)
  isSubpath l hd := by
    have h := P.isSubpath (P.childParentIndex hlinks l)
      (by simpa [P.link_childParentIndex hlinks l] using hd)
    simpa [P.link_childParentIndex hlinks l] using h
  owner_unique := by
    intro l r hl hr howner
    have hlink := P.owner_unique
      (P.childParentIndex hlinks l) (P.childParentIndex hlinks r)
      (by simpa [P.link_childParentIndex hlinks l] using hl)
      (by simpa [P.link_childParentIndex hlinks r] using hr) howner
    simpa [P.link_childParentIndex hlinks l,
      P.link_childParentIndex hlinks r] using hlink

/-- Indexed provenance supplies ordinary backward-link ownership. -/
theorem backwardLinksOn
    (P : child.IndexedBackwardProvenance Y I) :
    BackwardLinksOn Y child := by
  intro l hl hd
  rw [P.links_eq_range] at hl
  obtain ⟨i, rfl⟩ := hl
  exact ⟨P.owner i hd, P.owner_mem i hd, P.isSubpath i hd⟩

end AltPath.IndexedBackwardProvenance
end Alternating

namespace Blueprint

open _root_.Erdos599.Alternating

universe u w

variable {V : Type u} {Gamma : DWeb V}
variable {Y : Set Gamma.DPath}
variable {parent child : AltPath Gamma.graph} {I : Type w}

/-- A literal edge/link restriction of an internally generated compressed
trace is internally safe. -/
theorem InternallySafe.of_literalSubtrace
    (hparent : IsSafe Y parent)
    (P : parent.IndexedBackwardProvenance Y I)
    (hlinks : child.links ⊆ parent.links)
    (hedges : child.edgeSet ⊆ parent.edgeSet) :
    InternallySafe Y child := by
  let Pchild := P.restrictLinks hlinks
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

#print axioms Erdos599.Alternating.AltPath.IndexedBackwardProvenance.restrictLinks
#print axioms Erdos599.Blueprint.InternallySafe.of_literalSubtrace
