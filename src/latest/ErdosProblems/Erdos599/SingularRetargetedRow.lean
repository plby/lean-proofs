/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension

/-!
# Bounded singular rows from retargeted lower extension

For a bounded piece `B` of the designated source set `A₀`, retarget the web
at the original target together with `A₀ \ B`.  The fixed complementary
linkage, joined with trivial paths at `A₀ \ B`, links the complement of `B`
to that enlarged target.  The lower extension clause therefore gives a
full-source linkage in the retargeted web.  Normalization forces the members
starting in `B` to finish at the original target.

This is a positive finite-horizon ingredient for the singular construction:
every bounded requested row can be selected from scratch.  It intentionally
does not assert compatibility between rows selected for different requests.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularRetargetedRow

open DirectedPath SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- Trivial paths on `S` form an `S`--`C` linkage when `S` belongs to both
distinguished sides. -/
theorem trivialPaths_isLinkageBetween
    (G : DWeb V) {S C : Set V} (hStarget : S ⊆ C) :
    IsLinkageBetween (G.retarget C) S C
      ((G.retarget C).trivialPath '' S) := by
  let H := G.retarget C
  change IsLinkageBetween H S C (H.trivialPath '' S)
  refine ⟨H.isWarp_trivialPaths S, ?_,
    H.initialSet_trivialPaths S, ?_, ?_⟩
  · rintro p ⟨a, ha, rfl⟩
    exact ⟨FinitePath.trivial H.graph a, rfl⟩
  · rw [H.terminalFrontier_trivialPaths]
    exact hStarget
  · rintro p ⟨a, ha, rfl⟩
    refine ⟨FinitePath.trivial H.graph a, rfl, ?_, ?_⟩
    · simp only [FinitePath.support_trivial, FinitePath.trivial_start,
        FinitePath.trivial_finish]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_insert_iff]
      constructor
      · intro hx
        exact Or.inl hx.1
      · intro hx
        rcases hx with hxa | hxa <;> subst x
        · exact ⟨rfl, Or.inl ha⟩
        · exact ⟨rfl, Or.inl ha⟩
    · simp only [FinitePath.support_trivial, FinitePath.trivial_start]
      ext x
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        subst x
        exact ⟨rfl, ha⟩

/-- Two vertex-disjoint linkages to one target can be united. -/
theorem linkageBetween_union_of_vertexSet_disjoint
    (G : DWeb V) {A B C : Set V} {P Q : Set G.DPath}
    (hP : IsLinkageBetween G A C P)
    (hQ : IsLinkageBetween G B C Q)
    (hdisjoint : Disjoint (G.vertexSet P) (G.vertexSet Q)) :
    IsLinkageBetween G (A ∪ B) C (P ∪ Q) := by
  have hAvertex : A ⊆ G.vertexSet P := by
    rw [← hP.initialSet_eq]
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p, hp, p.initial_mem_support⟩
  have hBvertex : B ⊆ G.vertexSet Q := by
    rw [← hQ.initialSet_eq]
    rintro x ⟨q, hq, rfl⟩
    exact ⟨q, hq, q.initial_mem_support⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hpq
    rcases hp with hpP | hpQ <;> rcases hq with hqP | hqQ
    · exact hP.isWarp hpP hqP hpq
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 hdisjoint
        ⟨p, hpP, hxp⟩ ⟨q, hqQ, hxq⟩
    · apply Set.disjoint_left.2
      intro x hxp hxq
      exact Set.disjoint_left.1 hdisjoint
        ⟨q, hqP, hxq⟩ ⟨p, hpQ, hxp⟩
    · exact hQ.isWarp hpQ hqQ hpq
  · intro p hp
    rcases hp with hpP | hpQ
    · exact hP.finiteCharacter hpP
    · exact hQ.finiteCharacter hpQ
  · rw [G.initialSet_union, hP.initialSet_eq, hQ.initialSet_eq]
  · intro x hx
    obtain ⟨p, hpP | hpQ, hpx⟩ := hx
    · exact hP.terminalFrontier_subset ⟨p, hpP, hpx⟩
    · exact hQ.terminalFrontier_subset ⟨p, hpQ, hpx⟩
  · intro p hp
    rcases hp with hpP | hpQ
    · have hpath := hP.endpointPure p hpP
      rcases hpath with ⟨q, rfl, hends, hsource⟩
      have havoidB : Disjoint q.support B := by
        rw [Set.disjoint_left]
        intro x hxq hxB
        exact Set.disjoint_left.1 hdisjoint
          ⟨.inl q, hpP, hxq⟩ (hBvertex hxB)
      refine ⟨q, rfl, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, (hxA | hxB) | hxC⟩
          · exact hends ▸ ⟨hxq, Or.inl hxA⟩
          · exact False.elim (Set.disjoint_left.1 havoidB hxq hxB)
          · exact hends ▸ ⟨hxq, Or.inr hxC⟩
        · intro x hx
          have hxOld : x ∈ q.support ∩ (A ∪ C) := hends.symm ▸ hx
          exact ⟨hxOld.1, hxOld.2.elim
            (fun hxA ↦ Or.inl (Or.inl hxA)) Or.inr⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · exact hsource ▸ ⟨hxq, hxA⟩
          · exact False.elim (Set.disjoint_left.1 havoidB hxq hxB)
        · intro x hx
          have hxOld : x ∈ q.support ∩ A := hsource.symm ▸ hx
          exact ⟨hxOld.1, Or.inl hxOld.2⟩
    · have hpath := hQ.endpointPure p hpQ
      rcases hpath with ⟨q, rfl, hends, hsource⟩
      have havoidA : Disjoint q.support A := by
        rw [Set.disjoint_left]
        intro x hxq hxA
        exact Set.disjoint_left.1 hdisjoint
          (hAvertex hxA) ⟨.inl q, hpQ, hxq⟩
      refine ⟨q, rfl, ?_, ?_⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, (hxA | hxB) | hxC⟩
          · exact False.elim (Set.disjoint_left.1 havoidA hxq hxA)
          · exact hends ▸ ⟨hxq, Or.inl hxB⟩
          · exact hends ▸ ⟨hxq, Or.inr hxC⟩
        · intro x hx
          have hxOld : x ∈ q.support ∩ (B ∪ C) := hends.symm ▸ hx
          exact ⟨hxOld.1, hxOld.2.elim
            (fun hxB ↦ Or.inl (Or.inr hxB)) Or.inr⟩
      · apply Set.Subset.antisymm
        · rintro x ⟨hxq, hxA | hxB⟩
          · exact False.elim (Set.disjoint_left.1 havoidA hxq hxA)
          · exact hsource ▸ ⟨hxq, hxB⟩
        · intro x hx
          have hxOld : x ∈ q.support ∩ B := hsource.symm ▸ hx
          exact ⟨hxOld.1, Or.inr hxOld.2⟩

/-- A normalized linkage remains a linkage after adding a disjoint set of
ambient sources to the target. -/
theorem linkageBetween_retarget_source_addition
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A B S : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A B P)
    (hSsource : S ⊆ G.source) (hAS : Disjoint A S) :
    IsLinkageBetween (G.retarget (B ∪ S)) A (B ∪ S) P := by
  change IsLinkageBetween G A (B ∪ S) P
  refine ⟨hP.isWarp, hP.finiteCharacter, hP.initialSet_eq, ?_, ?_⟩
  · intro x hx
    exact Or.inl (hP.terminalFrontier_subset hx)
  · intro p hpP
    obtain ⟨q, rfl, hends, hsource⟩ := hP.endpointPure p hpP
    refine ⟨q, rfl, ?_, hsource⟩
    have havoidS : Disjoint q.support S := by
      rw [Set.disjoint_left]
      intro x hxq hxS
      have hxStart : x = q.start :=
        hNorm.eq_start_of_mem_walk q.walk hxq (hSsource hxS)
      have hstartA : q.start ∈ A := by
        have : q.start ∈ q.support ∩ A := by
          rw [hsource]
          exact Set.mem_singleton q.start
        exact this.2
      exact Set.disjoint_left.1 hAS hstartA (hxStart ▸ hxS)
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxA | hxBS⟩
      · exact hends ▸ ⟨hxq, Or.inl hxA⟩
      · rcases hxBS with hxB | hxS
        · exact hends ▸ ⟨hxq, Or.inr hxB⟩
        · exact False.elim (Set.disjoint_left.1 havoidS hxq hxS)
    · intro x hx
      have hxOld : x ∈ q.support ∩ (A ∪ B) := hends.symm ▸ hx
      exact ⟨hxOld.1, hxOld.2.elim Or.inl (fun h ↦ Or.inr (Or.inl h))⟩

/-- Source vertices added temporarily to the target can be removed again
when they are disjoint from the initial set of the linkage.  Normalization
forces a path ending at such a temporary target to be trivial, contradicting
the disjointness of its initial vertex. -/
theorem linkageBetween_remove_disjoint_source_targets
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A C S : Set V} {P : Set G.DPath}
    (hS : S ⊆ G.source)
    (hAS : Disjoint A S)
    (hP : IsLinkageBetween G A (C ∪ S) P) :
    IsLinkageBetween G A C P := by
  have hterminal : G.terminalFrontier P ⊆ C := by
    rintro x ⟨p, hpP, hpx⟩
    obtain ⟨q, rfl⟩ := hP.finiteCharacter hpP
    change some q.finish = some x at hpx
    have hfinishX : q.finish = x := Option.some.inj hpx
    subst x
    rcases hP.terminalFrontier_subset
        ⟨(Sum.inl q : G.DPath), hpP, rfl⟩ with hfinishC | hfinishS
    · exact hfinishC
    · have hfinishStart : q.finish = q.start :=
        hNorm.eq_start_of_mem_walk q.walk q.finish_mem_support
          (hS hfinishS)
      have hstartA : q.start ∈ A := by
        have hstartInitial : q.start ∈ G.initialSet P :=
          ⟨(Sum.inl q : G.DPath), hpP, rfl⟩
        exact hP.initialSet_eq ▸ hstartInitial
      have hstartS : q.start ∈ S := by
        rw [← hfinishStart]
        exact hfinishS
      exact False.elim (Set.disjoint_left.1 hAS hstartA hstartS)
  refine ⟨hP.isWarp, hP.finiteCharacter, hP.initialSet_eq,
    hterminal, ?_⟩
  intro p hpP
  obtain ⟨q, rfl, hends, hsource⟩ := hP.endpointPure p hpP
  have hstartA : q.start ∈ A := by
    have hstartInitial : q.start ∈ G.initialSet P :=
      ⟨(Sum.inl q : G.DPath), hpP, rfl⟩
    exact hP.initialSet_eq ▸ hstartInitial
  have hfinishC : q.finish ∈ C :=
    hterminal ⟨(Sum.inl q : G.DPath), hpP, rfl⟩
  refine ⟨q, rfl, ?_, hsource⟩
  apply Set.Subset.antisymm
  · intro x hx
    have hxOld : x ∈ q.support ∩ (A ∪ (C ∪ S)) :=
      ⟨hx.1, hx.2.elim Or.inl (fun hxC ↦ Or.inr (Or.inl hxC))⟩
    exact hends ▸ hxOld
  · intro x hx
    rcases Set.mem_insert_iff.1 hx with hstart | hfinish
    · subst x
      exact ⟨q.start_mem_support, Or.inl hstartA⟩
    · have hfinishEq : x = q.finish := Set.mem_singleton_iff.1 hfinish
      subst x
      exact ⟨q.finish_mem_support, Or.inr hfinishC⟩

/-- The fixed complement linkage is disjoint from trivial paths at a
disjoint set of normalized source vertices. -/
theorem vertexSet_disjoint_trivialPaths_of_normalized
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A S : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P)
    (hSsource : S ⊆ G.source) (hAS : Disjoint A S) :
    Disjoint (G.vertexSet P) (G.vertexSet (G.trivialPath '' S)) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hpP, hxp⟩ ⟨q, ⟨s, hs, rfl⟩, hxq⟩
  have hxs : x = s := by
    simpa only [G.support_trivialPath, Set.mem_singleton_iff] using hxq
  have hxInitial : x = p.initial :=
    hNorm.eq_initial_of_mem_path p hxp (hSsource (hxs ▸ hs))
  have hpInitialA : p.initial ∈ A := by
    rw [← hP.initialSet_eq]
    exact ⟨p, hpP, rfl⟩
  exact Set.disjoint_left.1 hAS hpInitialA
    (hxInitial.symm ▸ hxs ▸ hs)

/-- The complement of `B` is linked to the enlarged target by the fixed
complement linkage and trivial paths on `A₀ \ B`. -/
theorem exists_retargetedComplementLinkage
    {G : DWeb V} (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ K : Set (G.retarget (G.target ∪ (A₀ \ B))).DPath,
      IsLinkageBetween (G.retarget (G.target ∪ (A₀ \ B)))
        ((G.retarget (G.target ∪ (A₀ \ B))).source \ B)
        (G.retarget (G.target ∪ (A₀ \ B))).target K := by
  let S := A₀ \ B
  let H := G.retarget (G.target ∪ S)
  let T : Set H.DPath := H.trivialPath '' S
  have hSsource : S ⊆ G.source := Set.sdiff_subset.trans hA₀
  have hdisAS : Disjoint (G.source \ A₀) S := by
    rw [Set.disjoint_left]
    exact fun _ hx hy ↦ hx.2 hy.1
  have hfixedH : IsLinkageBetween H (G.source \ A₀) H.target fixed := by
    exact linkageBetween_retarget_source_addition hNorm hfixed
      hSsource hdisAS
  have htrivialH : IsLinkageBetween H S H.target T := by
    exact trivialPaths_isLinkageBetween G Set.subset_union_right
  have hvertex : Disjoint (H.vertexSet fixed) (H.vertexSet T) := by
    exact vertexSet_disjoint_trivialPaths_of_normalized hNorm hfixed
      hSsource hdisAS
  refine ⟨fixed ∪ T, ?_⟩
  have hunion := linkageBetween_union_of_vertexSet_disjoint H
    hfixedH htrivialH hvertex
  have hsources : (G.source \ A₀) ∪ S = H.source \ B := by
    dsimp only [H, S]
    ext x
    simp only [DWeb.retarget_source, Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hx
      rcases hx with ⟨hxSource, hxA₀⟩ | ⟨hxA₀, hxB⟩
      · exact ⟨hxSource, fun hxB ↦ hxA₀ (hB hxB)⟩
      · exact ⟨hA₀ hxA₀, hxB⟩
    · intro hx
      rcases hx with ⟨hxSource, hxB⟩
      by_cases hxA₀ : x ∈ A₀
      · exact Or.inr ⟨hxA₀, hxB⟩
      · exact Or.inl ⟨hxSource, hxA₀⟩
  rw [← hsources]
  exact hunion

/-- Retargeting at a superset of the original target preserves
unhinderedness. -/
theorem retarget_union_isUnhindered
    {G : DWeb V} (hG : G.IsUnhindered) (S : Set V) :
    (G.retarget (G.target ∪ S)).IsUnhindered := by
  rintro ⟨W, hW⟩
  apply hG
  refine ⟨W, DWeb.IsHindrance.of_retarget G hW ?_⟩
  intro a _ha p hp
  exact ⟨p.finish, p.finish_mem_support, Or.inl hp.2⟩

/-- Every bounded requested part of `A₀` admits a full-source row linking
that part to the original target.  The construction uses only the lower
extension clause, not the singular extension conclusion at `kappa`. -/
theorem exists_fullSourceRow_links_bounded
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : rho < kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B = rho)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ P : Set G.DPath,
      G.IsWarp P ∧ G.HasFiniteCharacter P ∧
        G.initialSet P = G.source ∧ LinksToTarget G P B := by
  let S := A₀ \ B
  let H := G.retarget (G.target ∪ S)
  have hHunhindered : H.IsUnhindered := retarget_union_isUnhindered hG S
  obtain ⟨K, hK⟩ :=
    exists_retargetedComplementLinkage hNorm hA₀ hB hfixed
  have hcardH : #B = rho := hBcard
  have hBsource : B ⊆ H.source := hB.trans hA₀
  have hHlinkable : IsLinkable H := by
    have hbelow := hlower rho hrho H hHunhindered
    exact hbelow.extension B hBsource hcardH ⟨K, hK⟩
  obtain ⟨P, hP⟩ := hHlinkable
  have hPwarp : G.IsWarp P := hP.isWarp
  have hPfinite : G.HasFiniteCharacter P := hP.finiteCharacter
  have hPinitial : G.initialSet P = G.source := hP.initialSet_eq
  refine ⟨P, hPwarp, hPfinite, hPinitial, ?_⟩
  intro a haB
  have haInitial : a ∈ H.initialSet P := hP.initialSet_eq.symm ▸ hBsource haB
  obtain ⟨p, hpP, hpInitial⟩ := haInitial
  obtain ⟨q, rfl, _hends, hsource⟩ := hP.endpointPure p hpP
  change FinitePath G.graph at q
  have hstart : q.start = a := hpInitial
  subst a
  have hfinishH : q.finish ∈ H.target := by
    exact hP.terminalFrontier_subset ⟨Sum.inl q, hpP, rfl⟩
  have hfinishG : q.finish ∈ G.target := by
    rcases hfinishH with hfinishTarget | hfinishS
    · exact hfinishTarget
    · have hfinishSource : q.finish ∈ H.source := hA₀ hfinishS.1
      have hfinishEq : q.finish = q.start :=
        hNorm.eq_start_of_mem_walk q.walk q.finish_mem_support
          hfinishSource
      exact False.elim (hfinishS.2 (hfinishEq ▸ haB))
  refine ⟨Sum.inl q, hpP, q, rfl, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxB⟩
      have hxSource : x ∈ H.source := hA₀ (hB hxB)
      have hxStart : x = q.start :=
        hNorm.eq_start_of_mem_walk q.walk hxq hxSource
      exact hxStart ▸ Set.mem_singleton q.start
    · intro x hx
      have hxStart : x = q.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨q.start_mem_support, haB⟩
  · refine ⟨[], q.walk.support.tail, ?_, q.finish, hfinishG, ?_⟩
    · simp only [List.nil_append]
      calc
        q.walk.support =
            q.walk.support.head q.walk.support_ne_nil ::
              q.walk.support.tail :=
          (q.walk.support.cons_head_tail q.walk.support_ne_nil).symm
        _ = q.start :: q.walk.support.tail := by
          rw [q.walk.head_support]
    · have hfinishSupport : q.finish ∈ q.walk.support :=
        q.finish_mem_support
      have hcons : q.start :: q.walk.support.tail = q.walk.support := by
        calc
          q.start :: q.walk.support.tail =
              q.walk.support.head q.walk.support_ne_nil ::
                q.walk.support.tail := by rw [q.walk.head_support]
          _ = q.walk.support :=
            q.walk.support.cons_head_tail q.walk.support_ne_nil
      change q.finish ∈ q.start :: q.walk.support.tail
      rw [hcons]
      exact hfinishSupport

/-- In particular, every bounded part of `A₀` has an ordinary linkage to
the original target.  Unlike the full row above, this result retains only
the components rooted in `B`; temporary source targets are eliminated by
normalization. -/
theorem exists_boundedTargetLinkage
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : rho < kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B = rho)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ L : Set G.DPath, IsLinkageBetween G B G.target L := by
  let S := A₀ \ B
  let H := G.retarget (G.target ∪ S)
  have hHunhindered : H.IsUnhindered := retarget_union_isUnhindered hG S
  obtain ⟨K, hK⟩ :=
    exists_retargetedComplementLinkage hNorm hA₀ hB hfixed
  have hBsource : B ⊆ H.source := hB.trans hA₀
  have hHlinkable : IsLinkable H := by
    have hbelow := hlower rho hrho H hHunhindered
    exact hbelow.extension B hBsource hBcard ⟨K, hK⟩
  obtain ⟨P, hP⟩ := hHlinkable
  let L := initialRestriction H P B
  have hLlarge : IsLinkageBetween H B H.target L :=
    isLinkageBetween_initialRestriction hP hBsource
  have hSsource : S ⊆ G.source := Set.sdiff_subset.trans hA₀
  have hBS : Disjoint B S := by
    rw [Set.disjoint_left]
    exact fun _ hxB hxS ↦ hxS.2 hxB
  refine ⟨L, ?_⟩
  apply linkageBetween_remove_disjoint_source_targets hNorm
    hSsource hBS
  change IsLinkageBetween H B H.target L at hLlarge
  exact hLlarge

/-- The same retargeted linkage simultaneously preserves the entire fixed
complement domain.  Thus every bounded approximation `B` can be joined to
`source \ A₀` by one ordinary linkage to the original target; no
disjointness argument between independently selected families is needed. -/
theorem exists_jointBoundedTargetLinkage
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : rho < kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B = rho)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ L : Set G.DPath,
      IsLinkageBetween G ((G.source \ A₀) ∪ B) G.target L := by
  let S := A₀ \ B
  let H := G.retarget (G.target ∪ S)
  let D := (G.source \ A₀) ∪ B
  have hHunhindered : H.IsUnhindered := retarget_union_isUnhindered hG S
  obtain ⟨K, hK⟩ :=
    exists_retargetedComplementLinkage hNorm hA₀ hB hfixed
  have hBsource : B ⊆ H.source := hB.trans hA₀
  have hHlinkable : IsLinkable H := by
    have hbelow := hlower rho hrho H hHunhindered
    exact hbelow.extension B hBsource hBcard ⟨K, hK⟩
  obtain ⟨P, hP⟩ := hHlinkable
  let L := initialRestriction H P D
  have hDsource : D ⊆ H.source := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hA₀ (hB hx)
  have hLlarge : IsLinkageBetween H D H.target L :=
    isLinkageBetween_initialRestriction hP hDsource
  have hSsource : S ⊆ G.source := Set.sdiff_subset.trans hA₀
  have hDS : Disjoint D S := by
    rw [Set.disjoint_left]
    intro x hxD hxS
    rcases hxD with hxComplement | hxB
    · exact hxComplement.2 hxS.1
    · exact hxS.2 hxB
  refine ⟨L, ?_⟩
  apply linkageBetween_remove_disjoint_source_targets hNorm
    hSsource hDS
  change IsLinkageBetween H D H.target L at hLlarge
  exact hLlarge

/-- Strict-cardinality form of `exists_fullSourceRow_links_bounded`. -/
theorem exists_fullSourceRow_links_of_mk_lt
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B < kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ P : Set G.DPath,
      G.IsWarp P ∧ G.HasFiniteCharacter P ∧
        G.initialSet P = G.source ∧ LinksToTarget G P B := by
  exact exists_fullSourceRow_links_bounded hlower hBcard hG hNorm
    hA₀ hB rfl hfixed

/-- Strict-cardinality form of the joint bounded approximant. -/
theorem exists_jointBoundedTargetLinkage_of_mk_lt
    {kappa : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    {G : DWeb V} (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {A₀ B : Set V} (hA₀ : A₀ ⊆ G.source) (hB : B ⊆ A₀)
    (hBcard : #B < kappa)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    ∃ L : Set G.DPath,
      IsLinkageBetween G ((G.source \ A₀) ∪ B) G.target L := by
  exact exists_jointBoundedTargetLinkage hlower hBcard hG hNorm
    hA₀ hB rfl hfixed

#print axioms exists_fullSourceRow_links_bounded
#print axioms exists_boundedTargetLinkage
#print axioms exists_jointBoundedTargetLinkage
#print axioms exists_jointBoundedTargetLinkage_of_mk_lt

end SingularRetargetedRow
end CardinalInduction
end Erdos599
