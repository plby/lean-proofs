/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SliceCandidate
import ErdosProblems.Erdos599.SingularContinuation

/-!
# Clean first-hit prefixes of a full finite warp

A finite full-source warp is automatically a linkage to its own terminal
frontier: disjointness prevents a member from meeting the initial or terminal
vertex of another member.  Consequently, if all terminals lie in `D`, cutting
every component at its first visit to `D` gives a source--`D` linkage which is
terminal-clean and is a forward prefix of the original warp.

This construction does not assume endpoint purity of the displayed warp.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFirstHitCleanPrefix

open DirectedPath SingularContinuation SliceCandidate

universe u

variable {V : Type u}

/-- A finite warp which has exactly the full source as its initial set is a
linkage from the source to its own terminal frontier.  In particular, the
endpoint-purity field is a consequence rather than an assumption. -/
theorem isLinkageBetween_terminalFrontier_of_finite_full
    {G : DWeb V} {W : Set G.DPath}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source) :
    IsLinkageBetween G G.source (G.terminalFrontier W) W := by
  refine ⟨hW, hfinite, hinitial, Set.Subset.rfl, ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := hfinite hp
  have hsource : q.support ∩ G.source = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxsource⟩
      have hxinitial : x ∈ G.initialSet W := hinitial.symm ▸ hxsource
      obtain ⟨r, hrW, hrinitial⟩ := hxinitial
      have hrq : r = (Sum.inl q : G.DPath) := by
        by_contra hrq
        exact Set.disjoint_left.1 (hW hrW hp hrq)
          (hrinitial ▸ r.initial_mem_support) hxq
      subst r
      exact Set.mem_singleton_iff.mpr hrinitial.symm
    · rintro x hx
      have hxq : x = q.start := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.start_mem_support,
        hinitial ▸ ⟨(Sum.inl q : G.DPath), hp, rfl⟩⟩
  have hterminal :
      q.support ∩ G.terminalFrontier W = {q.finish} := by
    apply Set.Subset.antisymm
    · exact DWeb.IsWarp.finite_support_inter_terminalFrontier G hW hp
    · rintro x hx
      have hxq : x = q.finish := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨q.finish_mem_support, ⟨(Sum.inl q : G.DPath), hp, rfl⟩⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, hterminal]
  ext x
  simp [or_comm]

/-- A set containing the terminal frontier separates the source from that
frontier, simply because the last vertex of every relevant walk lies in the
set. -/
theorem separates_terminalFrontier_of_subset
    (G : DWeb V) {W : Set G.DPath} {D : Set V}
    (hterminal : G.terminalFrontier W ⊆ D) :
    RelationalRoof.Separates G.graph.Adj G.source
      (G.terminalFrontier W) D := by
  intro r t p _hr ht
  exact ⟨t, p.end_mem_support, hterminal ht⟩

/-- The canonical clean prefix: regard `W` as a linkage to its own terminal
frontier and cut each component at its first visit to `D`. -/
noncomputable def firstHitCleanPrefix
    (G : DWeb V) (W : Set G.DPath) (D : Set V)
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hterminal : G.terminalFrontier W ⊆ D) : Set G.DPath :=
  firstHitPrefixFamily
    (isLinkageBetween_terminalFrontier_of_finite_full hW hfinite hinitial)
    (separates_terminalFrontier_of_subset G hterminal)

/-- The first-hit family is a full source--`D` linkage. -/
theorem firstHitCleanPrefix_isLinkageBetween
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hterminal : G.terminalFrontier W ⊆ D) :
    IsLinkageBetween G G.source D
      (firstHitCleanPrefix G W D hW hfinite hinitial hterminal) := by
  exact firstHitPrefixFamily_isLinkageBetween
    (isLinkageBetween_terminalFrontier_of_finite_full hW hfinite hinitial)
    (separates_terminalFrontier_of_subset G hterminal)

/-- First-hit truncation makes the new family terminal-clean at `D`, even
when the source and `D` overlap. -/
theorem firstHitCleanPrefix_terminalClean
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hterminal : G.terminalFrontier W ⊆ D) :
    TerminalCleanAt G
      (firstHitCleanPrefix G W D hW hfinite hinitial hterminal) D := by
  let hL := isLinkageBetween_terminalFrontier_of_finite_full
    hW hfinite hinitial
  let hsep : RelationalRoof.Separates G.graph.Adj G.source
      (G.terminalFrontier W) D :=
    separates_terminalFrontier_of_subset G hterminal
  rintro p ⟨a, rfl⟩ x hx hxD
  have hx' : x ∈ (linkageFirstHitAt hL hsep a).support ∩ D := ⟨hx, hxD⟩
  rw [linkageFirstHitAt_targetPure hL hsep a] at hx'
  have hxeq : x = (linkageFirstHitAt hL hsep a).finish :=
    Set.mem_singleton_iff.mp hx'
  subst x
  rfl

/-- The clean first-hit family is a componentwise forward prefix of `W`. -/
theorem forwardExtension_firstHitCleanPrefix
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hterminal : G.terminalFrontier W ⊆ D) :
    G.ForwardExtension
      (firstHitCleanPrefix G W D hW hfinite hinitial hterminal) W := by
  let hL := isLinkageBetween_terminalFrontier_of_finite_full
    hW hfinite hinitial
  let hsep : RelationalRoof.Separates G.graph.Adj G.source
      (G.terminalFrontier W) D :=
    separates_terminalFrontier_of_subset G hterminal
  constructor
  · rintro p ⟨a, rfl⟩
    refine ⟨(linkageMemberAt hL a).1, (linkageMemberAt hL a).2, ?_⟩
    rw [linkageMemberAt_eq_finite]
    exact (linkageFiniteAt hL a).walk.firstHit D
      (linkageFiniteAt_meets hL hsep a) |>.support_prefix
  · intro q hqW
    have hqsource : q.initial ∈ G.source := by
      rw [← hinitial]
      exact ⟨q, hqW, rfl⟩
    let a : G.source := ⟨q.initial, hqsource⟩
    have hmember : (linkageMemberAt hL a).1 = q := by
      by_contra hne
      have hdisjoint := hW (linkageMemberAt hL a).2 hqW hne
      have hinitialEq : (linkageMemberAt hL a).1.initial = q.initial := by
        simpa only [a] using linkageMemberAt_initial hL a
      exact Set.disjoint_left.1 hdisjoint
        (linkageMemberAt hL a).1.initial_mem_support (by
          rw [hinitialEq]
          exact q.initial_mem_support)
    refine ⟨(Sum.inl (linkageFirstHitAt hL hsep a) : G.DPath),
      ⟨a, rfl⟩, ?_⟩
    rw [← hmember, linkageMemberAt_eq_finite]
    exact (linkageFiniteAt hL a).walk.firstHit D
      (linkageFiniteAt_meets hL hsep a) |>.support_prefix

/-- Packaged reconstruction theorem used by the singular target-row
machine.  The separator hypothesis is recorded at the interface expected by
the machine; the actual truncation only needs the stronger concrete fact
that every displayed terminal already belongs to `D`. -/
theorem firstHitCleanPrefix_spec
    {G : DWeb V} {W : Set G.DPath} {D : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hterminal : G.terminalFrontier W ⊆ D)
    (_hseparator : IsSeparatorFrom G G.source D) :
    IsLinkageBetween G G.source D
        (firstHitCleanPrefix G W D hW hfinite hinitial hterminal) ∧
      TerminalCleanAt G
        (firstHitCleanPrefix G W D hW hfinite hinitial hterminal) D ∧
      G.ForwardExtension
        (firstHitCleanPrefix G W D hW hfinite hinitial hterminal) W := by
  exact ⟨firstHitCleanPrefix_isLinkageBetween hW hfinite hinitial hterminal,
    firstHitCleanPrefix_terminalClean hW hfinite hinitial hterminal,
    forwardExtension_firstHitCleanPrefix hW hfinite hinitial hterminal⟩

end SingularFirstHitCleanPrefix
end CardinalInduction
end Erdos599
