/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCertifiedSafeCompletion
import ErdosProblems.Erdos599.SingularSafeDesignatedLinkage

/-!
# Certified successor steps for safely completed histories

The finite safe-designated construction can retain the Section 6 maximal-tree
certificate at every successor.  This file packages one such successor step:
an already safely completed linkage is enlarged by the certified path selected
in its residual.  The old carrier is literally preserved, and the new path is
disjoint from it.  Thus this is a sound positive replacement for attempting to
extend an arbitrary half-way row.

The statement intentionally concerns a single successor.  At an infinite
limit, one must additionally prove that deletion of the union carrier stays
unhindered (or resurrect maximal waves through that union); that assertion does
not follow merely from the finite successor invariant.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularCertifiedSafeHistory

open RegularSafeCompletion
open SingularCertifiedSafeCompletion
open SingularSafeDesignatedLinkage

universe u

variable {V : Type u}

/-- A certified successor to a safely completed designated linkage.  Besides
the enlarged safe linkage, it records that the old family is preserved
literally and that the added singleton path is the lift of a certified path
in the old residual. -/
structure CertifiedSafeDesignatedExtension
    (G : DWeb V) {A : Set V}
    (old : SafeDesignatedLinkage G A) (a : V) where
  choice : CertifiedSafeCompletionChoice G (G.vertexSet old.paths) a
  extended : SafeDesignatedLinkage G (insert a A)
  paths_eq : extended.paths = old.paths ∪ choice.completion.family

namespace CertifiedSafeDesignatedExtension

variable {G : DWeb V} {A : Set V}
    {old : SafeDesignatedLinkage G A} {a : V}

/-- The old safely completed family is retained at the successor. -/
theorem old_subset_paths
    (E : CertifiedSafeDesignatedExtension G old a) :
    old.paths ⊆ E.extended.paths := by
  rw [E.paths_eq]
  exact Set.subset_union_left

/-- The certified new singleton family is retained at the successor. -/
theorem new_subset_paths
    (E : CertifiedSafeDesignatedExtension G old a) :
    E.choice.completion.family ⊆ E.extended.paths := by
  rw [E.paths_eq]
  exact Set.subset_union_right

/-- The new carrier is the disjoint union of the previous carrier and the
certified completion path. -/
theorem vertexSet_eq
    (E : CertifiedSafeDesignatedExtension G old a) :
    G.vertexSet E.extended.paths =
      G.vertexSet old.paths ∪ E.choice.completion.path.support := by
  rw [E.paths_eq, G.vertexSet_union,
    E.choice.completion.vertexSet_family]

/-- The certified completion avoids the complete historical carrier. -/
theorem new_disjoint_old
    (E : CertifiedSafeDesignatedExtension G old a) :
    Disjoint E.choice.completion.path.support (G.vertexSet old.paths) :=
  E.choice.completion.avoids

end CertifiedSafeDesignatedExtension

/-- Extend a safely completed designated linkage by one fresh source, while
retaining the complete Section 6 tree/boundary certificate for the new path.

This is unconditional because the old linkage's residual is unhindered.  The
normalization hypothesis makes a source outside `A` absent from the whole old
carrier, so certified Theorem 6.1 applies there. -/
theorem exists_certifiedSafeDesignatedExtension
    (G : DWeb V) (hNorm : G.IsNormalized)
    {A : Set V} (old : SafeDesignatedLinkage G A) {a : V}
    (hASource : A ⊆ G.source)
    (haSource : a ∈ G.source) (haFresh : a ∉ A) :
    Nonempty (CertifiedSafeDesignatedExtension G old a) := by
  have haCarrier : a ∉ G.vertexSet old.paths :=
    source_not_mem_vertexSet_of_not_mem_initialSet
      hNorm old.linkage haSource haFresh
  obtain ⟨C⟩ := exists_certifiedSafeCompletionChoice G hNorm
    (G.vertexSet old.paths) old.residual_unhindered haSource haCarrier
  have hcross : Disjoint (G.vertexSet old.paths)
      (G.vertexSet C.completion.family) := by
    rw [C.completion.vertexSet_family]
    exact C.completion.avoids.symm
  let L := old.paths ∪ C.completion.family
  have hlink : IsLinkageBetween G (A ∪ {a}) G.target L :=
    linkage_union_of_disjoint hNorm
      hASource
      (Set.singleton_subset_iff.2 haSource)
      old.linkage C.completion.family_isLinkageBetween hcross
  have hlink' : IsLinkageBetween G (insert a A) G.target L := by
    simpa [Set.union_comm] using hlink
  let extended : SafeDesignatedLinkage G (insert a A) :=
    { paths := L
      linkage := hlink'
      residual_unhindered := by
        dsimp only [L]
        rw [G.vertexSet_union, C.completion.vertexSet_family]
        exact C.completion.next_unhindered }
  exact ⟨{
    choice := C
    extended := extended
    paths_eq := rfl }⟩

/-! ## Scope of an unrestricted selector

The safe-designated interface is deliberately strong.  On the entire source
it is exactly ordinary linkability: the residual-safety field adds no extra
difficulty once a full linkage has already been obtained, but the linkage
field itself is the desired conclusion.  Consequently a selector usable as
an induction input must remain restricted to genuinely smaller designated
sets; proving it for arbitrary sets would simply re-prove the main theorem.
-/

/-- A safely deletable linkage on the full source exists exactly when the web
is linkable. -/
theorem nonempty_full_iff_isLinkable (G : DWeb V) :
    Nonempty (SafeDesignatedLinkage G G.source) ↔ IsLinkable G := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.paths, S.linkage⟩
  · rintro ⟨P, hP⟩
    exact ⟨ofFullLinkage hP⟩

#print axioms exists_certifiedSafeDesignatedExtension
#print axioms nonempty_full_iff_isLinkable

end SingularCertifiedSafeHistory
end CardinalInduction
end Erdos599
