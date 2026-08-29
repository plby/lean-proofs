/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.SliceDeltaLift

/-!
# Protecting frozen regular-row components during a Delta fill

The clean row in the regular-cardinal construction is continued inside a
normalized restricted `Delta` web.  Components already completed in the
target row must be frozen: the new continuation has to avoid their entire
ambient vertex set.  This file records the exact transport statement needed
for that history-sensitive construction.

The continuation is first built in a vertex-deleted normalized `Delta` web.
Lifting it through the deletion and then through the two induced-graph
restrictions cannot introduce a deleted vertex.  Finally, a compatible star
with a previously disjoint pending family still avoids the protected set.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularProtectedDeltaLift

open SliceRestrictedDelta
open SliceDeltaLift

universe u

variable {V : Type u}

/-- A finite linkage path in a deleted web remains the same endpoint-pure
path after its edges are retyped in the original web. -/
theorem isPathBetween_liftDeletePath
    (H : DWeb V) (X A B : Set V) {p : (H.delete X).DPath}
    (hp : IsPathBetween (H.delete X) A B p) :
    IsPathBetween H A B (H.liftDeletePath X p) := by
  rcases hp with ⟨q, rfl, hends, hsource⟩
  let q' : DirectedPath.FinitePath H.graph := q.lift H.delete_adj_imp
  refine ⟨q', rfl, ?_, ?_⟩
  · rw [show q'.support = q.support by
      exact DirectedPath.FinitePath.support_lift _ q]
    exact hends
  · rw [show q'.support = q.support by
      exact DirectedPath.FinitePath.support_lift _ q]
    exact hsource

/-- An exact linkage in a vertex-deleted web lifts to the original web with
the same two endpoint sets. -/
theorem IsLinkageBetween.liftDeleteFamily
    (H : DWeb V) (X : Set V) {A B : Set V}
    {R : Set (H.delete X).DPath}
    (hR : IsLinkageBetween (H.delete X) A B R) :
    IsLinkageBetween H A B (H.liftDeleteFamily X R) := by
  refine ⟨hR.isWarp.liftDeleteFamily,
    H.fd_hasFiniteCharacter_liftDeleteFamily hR.finiteCharacter,
    ?_, ?_, ?_⟩
  · simpa only [H.initialSet_liftDeleteFamily] using hR.initialSet_eq
  · simpa only [H.terminalFrontier_liftDeleteFamily] using
      hR.terminalFrontier_subset
  · rintro _ ⟨p, hpR, rfl⟩
    exact isPathBetween_liftDeletePath H X A B (hR.endpointPure p hpR)

/-- Lifting a family first out of a vertex deletion and then out of normalized
`Delta` preserves avoidance of the deleted set.  The source premise is exactly
the premise needed by `DWeb.vertexSet_liftDeleteFamily_disjoint`; in intended
use it follows from the initial-set equality of the deleted-web linkage. -/
theorem vertexSet_liftNormalized_liftDeleteFamily_disjoint
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath) (X : Set V)
    (R : Set ((normalizedDelta Q C D T F).delete X).DPath)
    (hstart : ((normalizedDelta Q C D T F).delete X).initialSet R ⊆
      ((normalizedDelta Q C D T F).delete X).source) :
    Disjoint
      (Q.vertexSet
        (liftNormalizedFamily Q C D T F
          ((normalizedDelta Q C D T F).liftDeleteFamily X R)))
      X := by
  have havoid : Disjoint
      ((normalizedDelta Q C D T F).vertexSet
        ((normalizedDelta Q C D T F).liftDeleteFamily X R)) X :=
    (normalizedDelta Q C D T F).vertexSet_liftDeleteFamily_disjoint hstart
  apply Set.disjoint_left.2
  rintro x ⟨_, ⟨p, rfl⟩, hxp⟩ hxX
  apply Set.disjoint_left.1 havoid
  · exact ⟨p.1, p.2,
      by simpa only [support_liftNormalizedPath] using hxp⟩
  · exact hxX

/-- A linkage built after deleting `X` from normalized `Delta` can be
restored all the way to the ambient web.  The restored linkage has exactly
the same initial and terminal sets and its ambient carrier avoids `X`. -/
theorem IsLinkageBetween.liftDeleteNormalizedDelta
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath) (X : Set V)
    {A B : Set V}
    {R : Set ((normalizedDelta Q C D T F).delete X).DPath}
    (hR : IsLinkageBetween
      ((normalizedDelta Q C D T F).delete X) A B R)
    (hA : A ⊆ ((normalizedDelta Q C D T F).delete X).source) :
    IsLinkageBetween Q A B
        (liftNormalizedFamily Q C D T F
          ((normalizedDelta Q C D T F).liftDeleteFamily X R)) ∧
      Disjoint
        (Q.vertexSet
          (liftNormalizedFamily Q C D T F
            ((normalizedDelta Q C D T F).liftDeleteFamily X R))) X := by
  have hRlift : IsLinkageBetween (normalizedDelta Q C D T F) A B
      ((normalizedDelta Q C D T F).liftDeleteFamily X R) :=
    IsLinkageBetween.liftDeleteFamily
      (normalizedDelta Q C D T F) X hR
  refine ⟨SliceDeltaLift.IsLinkageBetween.liftNormalizedDelta
      Q C D T F hRlift, ?_⟩
  apply vertexSet_liftNormalized_liftDeleteFamily_disjoint
    Q C D T F X R
  rw [hR.initialSet_eq]
  exact hA

/-- If a protected carrier avoids both the old pending family and its new
continuation, it avoids their compatible star. -/
theorem disjoint_vertexSet_star_of_disjoint
    (Q : DWeb V) {K P Z : Set Q.DPath}
    (hKP : Disjoint (Q.vertexSet K) (Q.vertexSet P))
    (hKZ : Disjoint (Q.vertexSet K) (Q.vertexSet Z))
    (hcompat : Q.StarCompatible P Z) :
    Disjoint (Q.vertexSet K) (Q.vertexSet (Q.star hcompat)) := by
  apply Set.disjoint_left.2
  intro x hxK hxStar
  rcases SliceSpliceSource.vertexSet_star_subset_union hcompat hxStar with
      hxP | hxZ
  · exact Set.disjoint_left.1 hKP hxK hxP
  · exact Set.disjoint_left.1 hKZ hxK hxZ

/-- The packaged frozen-carrier bridge used by a clean-target step.  A
continuation constructed in normalized `Delta` with the frozen carrier
deleted yields an ambient compatible star disjoint from every frozen path.

This theorem deliberately does not assert that the deleted web is unhindered:
that is the genuinely history-sensitive existence obligation of the regular
recursion, not a formal consequence of unhinderedness before deletion. -/
theorem disjoint_protected_star_liftDeleteNormalizedFamily
    (Q : DWeb V) (C D T : Set V) (F : Set Q.DPath)
    {K P : Set Q.DPath}
    (R : Set
      ((normalizedDelta Q C D T F).delete (Q.vertexSet K)).DPath)
    (hstart :
      ((normalizedDelta Q C D T F).delete (Q.vertexSet K)).initialSet R ⊆
        ((normalizedDelta Q C D T F).delete (Q.vertexSet K)).source)
    (hKP : Disjoint (Q.vertexSet K) (Q.vertexSet P))
    (hcompat : Q.StarCompatible P
      (liftNormalizedFamily Q C D T F
        ((normalizedDelta Q C D T F).liftDeleteFamily
          (Q.vertexSet K) R))) :
    Disjoint (Q.vertexSet K) (Q.vertexSet (Q.star hcompat)) := by
  apply disjoint_vertexSet_star_of_disjoint Q hKP
  exact (vertexSet_liftNormalized_liftDeleteFamily_disjoint
    Q C D T F (Q.vertexSet K) R hstart).symm

end RegularProtectedDeltaLift
end CardinalInduction
end Erdos599
