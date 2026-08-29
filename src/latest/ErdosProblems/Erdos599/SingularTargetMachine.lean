/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularExtension
import ErdosProblems.Erdos599.SingularQuotientDelete
import ErdosProblems.Erdos599.SingularHalfwayComposition
import ErdosProblems.Erdos599.SingularLinkageGeometry

/-!
# Safe quotient selection for the singular target-row machine

The singular successor step freezes the components which have already
reached the target and continues the pending components through a quotient.
The quotient family must be chosen with an avoidance certificate: competitor
closure of the old row alone says nothing about a family selected later.

This file records the useful positive statement.  If the new family is first
chosen in deletion-then-quotient, and every frozen vertex is either deleted
or lies in the strict roof removed by the quotient, transporting it to
quotient-then-deletion and then back to the ambient web supplies exactly the
cross-disjointness premise of
`exists_frozenPendingContinuation_of_componentwise_disjoint`.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularExtension

universe u

variable {V : Type u}

/-! ## The active terminal boundary -/

/-- Terminals of the current row components whose original sources belong
to `A`.  This is the directed-web analogue of the source proof's
`boundaryActive`: the next lower-cardinal half-way linkage is requested at
these quotient sources. -/
def activeBoundary (G : DWeb V) (W : Set G.DPath) (A : Set V) : Set V :=
  {c | ∃ p ∈ W, p.initial ∈ A ∧ G.terminal? p = some c}

theorem activeBoundary_subset_terminalFrontier
    (G : DWeb V) (W : Set G.DPath) (A : Set V) :
    activeBoundary G W A ⊆ G.terminalFrontier W := by
  rintro c ⟨p, hpW, _hpA, hpc⟩
  exact ⟨p, hpW, hpc⟩

/-- The current component selected by a source. -/
noncomputable def sourcePath
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source)
    (a : A) : G.DPath :=
  Classical.choose (show a.1 ∈ G.initialSet W from hinitial.symm ▸ hA a.2)

theorem sourcePath_mem
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source)
    (a : A) : sourcePath G hinitial hA a ∈ W :=
  (Classical.choose_spec
    (show a.1 ∈ G.initialSet W from hinitial.symm ▸ hA a.2)).1

@[simp] theorem sourcePath_initial
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source)
    (a : A) : (sourcePath G hinitial hA a).initial = a.1 :=
  (Classical.choose_spec
    (show a.1 ∈ G.initialSet W from hinitial.symm ▸ hA a.2)).2

/-- The terminal of the current component selected by a source. -/
noncomputable def sourceTerminal
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source)
    (a : A) : V :=
  (Classical.choose (hfinite (sourcePath_mem G hinitial hA a))).finish

theorem terminal_sourcePath
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source)
    (a : A) :
    G.terminal? (sourcePath G hinitial hA a) =
      some (sourceTerminal G hfinite hinitial hA a) := by
  let f := Classical.choose (hfinite (sourcePath_mem G hinitial hA a))
  have hf := Classical.choose_spec
    (hfinite (sourcePath_mem G hinitial hA a))
  change G.terminal? (sourcePath G hinitial hA a) = some f.finish
  rw [hf]
  rfl

theorem sourceTerminal_mem_activeBoundary
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source)
    (a : A) :
    sourceTerminal G hfinite hinitial hA a ∈ activeBoundary G W A := by
  exact ⟨sourcePath G hinitial hA a, sourcePath_mem G hinitial hA a,
    sourcePath_initial G hinitial hA a ▸ a.2,
    terminal_sourcePath G hfinite hinitial hA a⟩

/-- Distinct sources of a warp have distinct finite terminals. -/
theorem sourceTerminal_injective
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source) :
    Function.Injective (sourceTerminal G hfinite hinitial hA) := by
  intro a b hab
  have hpq : sourcePath G hinitial hA a = sourcePath G hinitial hA b := by
    by_contra hpq
    exact Set.disjoint_left.1
      (hW (sourcePath_mem G hinitial hA a)
        (sourcePath_mem G hinitial hA b) hpq)
      (G.terminal_mem_support (terminal_sourcePath G hfinite hinitial hA a))
      (G.terminal_mem_support ((terminal_sourcePath G hfinite hinitial hA b).trans
        (congrArg some hab.symm)))
  apply Subtype.ext
  calc
    a.1 = (sourcePath G hinitial hA a).initial :=
      (sourcePath_initial G hinitial hA a).symm
    _ = (sourcePath G hinitial hA b).initial := congrArg _ hpq
    _ = b.1 := sourcePath_initial G hinitial hA b

/-- Choose the old component witnessing an active boundary point. -/
noncomputable def activeBoundaryPath
    (G : DWeb V) (W : Set G.DPath) (A : Set V)
    (c : activeBoundary G W A) : G.DPath :=
  Classical.choose c.2

theorem activeBoundaryPath_spec
    (G : DWeb V) (W : Set G.DPath) (A : Set V)
    (c : activeBoundary G W A) :
    activeBoundaryPath G W A c ∈ W ∧
      (activeBoundaryPath G W A c).initial ∈ A ∧
      G.terminal? (activeBoundaryPath G W A c) = some c.1 :=
  Classical.choose_spec c.2

/-- Sending an active terminal back to its old source is injective. -/
theorem activeBoundaryInitial_injective
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hW : G.IsWarp W) :
    Function.Injective (fun c : activeBoundary G W A =>
      (⟨(activeBoundaryPath G W A c).initial,
        (activeBoundaryPath_spec G W A c).2.1⟩ : A)) := by
  intro c d hcd
  have hinit : (activeBoundaryPath G W A c).initial =
      (activeBoundaryPath G W A d).initial := congrArg Subtype.val hcd
  have hpq : activeBoundaryPath G W A c =
      activeBoundaryPath G W A d :=
    DWeb.IsWarp.eq_of_initial_eq G hW
      (activeBoundaryPath_spec G W A c).1
      (activeBoundaryPath_spec G W A d).1 hinit
  apply Subtype.ext
  exact Option.some.inj <| calc
    some c.1 = G.terminal? (activeBoundaryPath G W A c) :=
      (activeBoundaryPath_spec G W A c).2.2.symm
    _ = G.terminal? (activeBoundaryPath G W A d) := congrArg _ hpq
    _ = some d.1 := (activeBoundaryPath_spec G W A d).2.2

/-- For a finite-character full-source warp, the active terminal boundary
has exactly the cardinality of the selected source set. -/
theorem mk_activeBoundary_eq
    (G : DWeb V) {W : Set G.DPath} {A : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source) (hA : A ⊆ G.source) :
    Cardinal.mk (activeBoundary G W A) = Cardinal.mk A := by
  apply le_antisymm
  · exact Cardinal.mk_le_of_injective
      (activeBoundaryInitial_injective G hW)
  · let f : A → activeBoundary G W A := fun a =>
      ⟨sourceTerminal G hfinite hinitial hA a,
        sourceTerminal_mem_activeBoundary G hfinite hinitial hA a⟩
    exact Cardinal.mk_le_of_injective (f := f) (by
      intro a b hab
      apply sourceTerminal_injective G hW hfinite hinitial hA
      exact congrArg Subtype.val hab)

/-! ## Transporting target completion through source star -/

/-- In a normalized web, finite completed components starting at all
members of `A` give the source-faithful suffix certificate used by the
matrix.  Normalization supplies purity against the entire selected source
set. -/
theorem linksToTarget_of_completed_sources
    {G : DWeb V} (hNorm : G.IsNormalized)
    {W : Set G.DPath} {A : Set V} (hA : A ⊆ G.source)
    (hfinite : G.HasFiniteCharacter W)
    (hcompleted : ∀ a ∈ A, ∃ p ∈ W, p.initial = a ∧
      ∃ b ∈ G.target, G.terminal? p = some b) :
    LinksToTarget G W A := by
  intro a ha
  obtain ⟨p, hpW, hpstart, b, hbTarget, hpterm⟩ := hcompleted a ha
  obtain ⟨f, hpf⟩ := hfinite hpW
  subst p
  have hfStart : f.start = a := hpstart
  have hfPure : f.support ∩ A = {a} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxStart : x = f.start :=
        hNorm.eq_initial_of_mem_path (.inl f) hx.1 (hA hx.2)
      exact Set.mem_singleton_iff.2 (hxStart.trans hfStart)
    · intro x hx
      have hxa : x = a := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨by simpa only [hfStart] using f.start_mem_support, ha⟩
  have hfFinish : f.finish = b := Option.some.inj hpterm
  refine ⟨.inl f, hpW, f, rfl, hfPure, ?_⟩
  refine ⟨[], f.walk.support.tail, ?_, b, hbTarget, ?_⟩
  · simp only [List.nil_append]
    calc
      f.walk.support =
          f.walk.support.head f.walk.support_ne_nil ::
            f.walk.support.tail :=
        (f.walk.support.cons_head_tail f.walk.support_ne_nil).symm
      _ = a :: f.walk.support.tail := by
        exact congrArg (fun x ↦ x :: f.walk.support.tail)
          (f.walk.head_support.trans hfStart)
  · have hcons : a :: f.walk.support.tail = f.walk.support := by
      calc
        a :: f.walk.support.tail =
            f.walk.support.head f.walk.support_ne_nil ::
              f.walk.support.tail := by
          exact congrArg (fun x ↦ x :: f.walk.support.tail)
            (hfStart.symm.trans f.walk.head_support.symm)
        _ = f.walk.support :=
          f.walk.support.cons_head_tail f.walk.support_ne_nil
    change b ∈ a :: f.walk.support.tail
    rw [hcons, ← hfFinish]
    exact f.finish_mem_support

/-- Lower-cardinal target links on the active terminal boundary become
target links for the corresponding original sources after composition. -/
theorem linksToTarget_composedContinuation
    (G : DWeb V) (hNorm : G.IsNormalized)
    {C D : Set V} {W : Set G.DPath}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set (G.quotient C).DPath}
    (hD : IsSeparatingHalfwayStopover (G.quotient C) U D)
    {A : Set V} (hA : A ⊆ G.source)
    (hlinks : LinksToTarget (G.quotient C) U
      (activeBoundary G W A)) :
    LinksToTarget G
      (SingularHalfwayComposition.composedContinuation G hC hclean U hD)
      A := by
  exact SingularContinuation.linksToTarget_continuation_of_activeBoundary
    G hNorm hC.linkage hC.separator hC.stopover.minimal hclean hA hD
      (by simpa only [activeBoundary] using hlinks)

/-! ## One exact composed successor -/

/-- A finite full-source warp is a linkage to its exact terminal frontier.
The proof is purely warp-theoretic: another source or terminal-frontier
point on a member would belong to a second component and violate
disjointness. -/
theorem isLinkageBetween_of_isWarp_finite_initial_frontier_eq
    (G : DWeb V) {W : Set G.DPath} {C : Set V}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W)
    (hinitial : G.initialSet W = G.source)
    (hfront : G.terminalFrontier W = C) :
    IsLinkageBetween G G.source C W := by
  refine ⟨hW, hfinite, hinitial, hfront.le, ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := hfinite hp
  have hsource : q.support ∩ G.source = {q.start} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxinitial : x ∈ G.initialSet W := hinitial.symm ▸ hx.2
      obtain ⟨r, hrW, hrstart⟩ := hxinitial
      have hrq : r = (Sum.inl q : G.DPath) := by
        by_contra hrq
        exact Set.disjoint_left.1 (hW hrW hp hrq)
          (hrstart ▸ r.initial_mem_support) hx.1
      subst r
      exact hrstart.symm
    · intro x hx
      have hxq : x = q.start := by simpa using hx
      subst x
      exact ⟨q.start_mem_support,
        hinitial ▸ ⟨(Sum.inl q : G.DPath), hp, rfl⟩⟩
  have hterminal : q.support ∩ C = {q.finish} := by
    rw [← hfront]
    apply Set.Subset.antisymm
    · exact DWeb.IsWarp.finite_support_inter_terminalFrontier G hW hp
    · intro x hx
      have hxq : x = q.finish := by simpa using hx
      subst x
      exact ⟨q.finish_mem_support,
        ⟨(Sum.inl q : G.DPath), hp, rfl⟩⟩
  refine ⟨q, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, hterminal]
  ext x
  simp [or_comm]

/-- The sound one-column singular successor.  The designated next source
set is sent to the terminals of its current components, the lower
separating half-way clause is applied in `G / C`, and source star composes
the resulting full-source quotient linkage back into `G`. -/
theorem exists_exactComposedSuccessor_of_lower
    {kappa rho : Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : rho < kappa) (hrhoInfinite : Cardinal.aleph0 ≤ rho)
    (G : DWeb V) (hNorm : G.IsNormalized)
    {W : Set G.DPath} {C A : Set V}
    (hC : IsSeparatingHalfwayStopover G W C)
    (hfront : G.terminalFrontier W = C)
    (hA : A ⊆ G.source) (hAcard : Cardinal.mk A = rho) :
    ∃ (W' : Set G.DPath) (D : Set V),
      IsSeparatingHalfwayStopover G W' D ∧
      LinksToTarget G W' A ∧
      G.terminalFrontier W' = D ∧
      G.ForwardExtension W W' := by
  let B : Set V := activeBoundary G W A
  have hBsource : B ⊆ (G.quotient C).source := by
    rw [SingularContinuation.quotient_source_eq_stopover
      G hC.separator hC.stopover.minimal]
    exact (activeBoundary_subset_terminalFrontier G W A).trans
      hfront.le
  have hBcard : Cardinal.mk B = rho := by
    calc
      Cardinal.mk B = Cardinal.mk A := mk_activeBoundary_eq G hC.linkage.isWarp
        hC.linkage.finiteCharacter hC.linkage.initialSet_eq hA
      _ = rho := hAcard
  obtain ⟨U, D, hD, hUlinks, _hDheight, hDfront⟩ :=
    (hlower rho hrho (G.quotient C)
      hC.stopover.quotient_unhindered).separatingHalfway
        hrhoInfinite B hBsource hBcard
  let hclean : SingularContinuation.TerminalCleanAt G W C :=
    SingularContinuation.terminalCleanAt_of_linkage_terminalFrontier_eq
      G hC.linkage hfront
  let W' : Set G.DPath :=
    SingularHalfwayComposition.composedContinuation G hC hclean U hD
  have hW'warp : G.IsWarp W' :=
    SingularHalfwayComposition.composedContinuation_isWarp
      G hC hclean hD
  have hW'finite : G.HasFiniteCharacter W' :=
    SingularHalfwayComposition.composedContinuation_finiteCharacter
      G hC hclean hD
  have hW'initial : G.initialSet W' = G.source :=
    SingularHalfwayComposition.initialSet_composedContinuation
      G hC hclean U hD
  have hW'front : G.terminalFrontier W' = D := by
    change G.terminalFrontier
        (SingularContinuation.continuation G hC.linkage hC.separator
          hC.stopover.minimal hclean U hD.linkage.initialSet_eq) = D
    calc
      G.terminalFrontier
          (SingularContinuation.continuation G hC.linkage hC.separator
            hC.stopover.minimal hclean U hD.linkage.initialSet_eq) =
          (G.quotient C).terminalFrontier U :=
        SingularContinuation.terminalFrontier_continuation_eq_of_terminalFrontier_eq
          G hC.linkage hC.separator hC.stopover.minimal hclean hfront
            hD.linkage.isWarp hD.linkage.initialSet_eq
      _ = D := hDfront
  have hW'link : IsLinkageBetween G G.source D W' :=
    isLinkageBetween_of_isWarp_finite_initial_frontier_eq
      G hW'warp hW'finite hW'initial hW'front
  have hcomposedEq :
      SingularHalfwayComposition.composedStopover G C D = D :=
    SingularHalfwayComposition.composedStopover_eq_second
      G hNorm hC.separator hC.stopover.minimal hD
  have hDtrim : IsTrimmedSeparator G D := by
    rw [← hcomposedEq]
    exact SingularHalfwayComposition.composedStopover_isTrimmedSeparator
      G C D
  have hDsep : IsSeparatorFrom G G.source D := by
    rw [← hcomposedEq]
    exact SingularHalfwayComposition.composedStopover_isSeparatorFrom
      G hC.separator
  have hDunhindered : (G.quotient D).IsUnhindered := by
    rw [← hcomposedEq]
    exact SingularHalfwayComposition.quotient_composedStopover_isUnhindered
      G hNorm hC.separator hD.stopover.quotient_unhindered
  have hstop' : IsSeparatingHalfwayStopover G W' D :=
    ⟨⟨hW'link, hDtrim, hDunhindered⟩, hDsep⟩
  refine ⟨W', D, hstop', ?_, hW'front, ?_⟩
  · exact linksToTarget_composedContinuation
      G hNorm hC hclean hD hA (by simpa only [B] using hUlinks)
  · exact SingularHalfwayComposition.forwardExtension_composedContinuation
      G hC hclean U hD

/-! ## Simultaneous composable row states -/

/-- The exact data which must survive after the zeroth certified row.
Ambient height is intentionally absent: every successor applies the lower
clause in the current quotient and then discards that quotient-local height
witness. -/
structure ComposableTargetRowStage (G : DWeb V) (I : Type u)
    (rho : I → Cardinal.{u}) where
  row : TargetRowStage G I
  stopover : I → Set V
  separating : ∀ i,
    IsSeparatingHalfwayStopover G (row.paths i) (stopover i)
  frontier_eq : ∀ i, G.terminalFrontier (row.paths i) = stopover i
  sources_subset : ∀ i, row.sources i ⊆ G.source
  sources_card : ∀ i, Cardinal.mk (row.sources i) = rho i

/-- Forget the zeroth row's ambient height witness while retaining the
exact frontier and cardinal/source invariants used by composition. -/
noncomputable def ComposableTargetRowStage.ofCertified
    {G : DWeb V} {I : Type u} {rho : I → Cardinal.{u}}
    (S : CertifiedTargetRowStage G I rho)
    (hsource : ∀ i, S.row.sources i ⊆ G.source)
    (hcard : ∀ i, Cardinal.mk (S.row.sources i) = rho i) :
    ComposableTargetRowStage G I rho where
  row := S.row
  stopover := S.stopover
  separating := S.separating
  frontier_eq := S.frontier_eq
  sources_subset := hsource
  sources_card := hcard

/-- Competitor closing preserves membership in the ambient source whenever
the fixed warp and every current row start in that source. -/
theorem nextTargetSources_subset_source
    {I : Type u} (G : DWeb V) {fixed : Set G.DPath}
    (hfixed : G.initialSet fixed ⊆ G.source)
    (S : TargetRowStage G I) (hsource : ∀ i, S.sources i ⊆ G.source)
    (i : I) : nextTargetSources G fixed S i ⊆ G.source := by
  rintro x (hx | hx)
  · exact hsource i hx
  · apply (SingularMatrix.competitorClosure_subset_initialSet G
      (fixed ∪ ⋃ j, S.paths j) (S.sources i)) at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rcases hp with hpfixed | hprows
    · exact hfixed ⟨p, hpfixed, rfl⟩
    · obtain ⟨j, hpj⟩ := Set.mem_iUnion.1 hprows
      have hpinitial : p.initial ∈ G.initialSet (S.paths j) :=
        ⟨p, hpj, rfl⟩
      rw [S.initialSet j] at hpinitial
      exact hpinitial

/-- One competitor-closing step preserves the exact row cardinal. -/
theorem mk_nextTargetSources_eq
    {I : Type u} (G : DWeb V) {fixed : Set G.DPath}
    (hfixed : G.IsWarp fixed) (S : TargetRowStage G I)
    {rho : I → Cardinal.{u}}
    (hinfinite : ∀ i, Cardinal.aleph0 ≤ rho i)
    (hindex : ∀ i, Cardinal.mk I ≤ rho i)
    (hcard : ∀ i, Cardinal.mk (S.sources i) = rho i)
    (i : I) : Cardinal.mk (nextTargetSources G fixed S i) = rho i := by
  apply le_antisymm
  · refine (Cardinal.mk_union_le _ _).trans ?_
    apply Cardinal.add_le_of_le (hinfinite i) (hcard i).le
    apply G.mk_competitorClosure_fixed_iUnion_le fixed S.paths
      (S.sources i) hfixed S.isWarp (hinfinite i) (hindex i)
    exact (hcard i).le
  · rw [← hcard i]
    exact Cardinal.mk_subtype_mono Set.subset_union_left

/-- Apply the checked one-column composition simultaneously in every row
of a composable state. -/
theorem exists_composableTargetRowStage_successor
    {kappa : Cardinal.{u}} {I : Type u}
    {rho : I → Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : ∀ i, rho i < kappa)
    (hinfinite : ∀ i, Cardinal.aleph0 ≤ rho i)
    (hindex : ∀ i, Cardinal.mk I ≤ rho i)
    (G : DWeb V) (hNorm : G.IsNormalized)
    {fixed : Set G.DPath} (hfixed : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : ComposableTargetRowStage G I rho) :
    ∃ T : ComposableTargetRowStage G I rho,
      T.row.sources = nextTargetSources G fixed S.row ∧
      ∀ i, G.ForwardExtension (S.row.paths i) (T.row.paths i) := by
  let A : I → Set V := nextTargetSources G fixed S.row
  have hAsource (i : I) : A i ⊆ G.source :=
    nextTargetSources_subset_source G hfixedSource S.row
      S.sources_subset i
  have hAcard (i : I) : Cardinal.mk (A i) = rho i :=
    mk_nextTargetSources_eq G hfixed S.row hinfinite hindex
      S.sources_card i
  have hex : ∀ i, ∃ (W' : Set G.DPath) (D : Set V),
      IsSeparatingHalfwayStopover G W' D ∧
      LinksToTarget G W' (A i) ∧
      G.terminalFrontier W' = D ∧
      G.ForwardExtension (S.row.paths i) W' := by
    intro i
    exact exists_exactComposedSuccessor_of_lower
      hlower (hrho i) (hinfinite i) G hNorm
        (S.separating i) (S.frontier_eq i) (hAsource i) (hAcard i)
  let W' : I → Set G.DPath := fun i ↦ Classical.choose (hex i)
  let D : I → Set V := fun i ↦
    Classical.choose (Classical.choose_spec (hex i))
  have hspec (i : I) :
      IsSeparatingHalfwayStopover G (W' i) (D i) ∧
      LinksToTarget G (W' i) (A i) ∧
      G.terminalFrontier (W' i) = D i ∧
      G.ForwardExtension (S.row.paths i) (W' i) :=
    Classical.choose_spec (Classical.choose_spec (hex i))
  refine ⟨{
    row := {
      sources := A
      paths := W'
      isWarp := fun i ↦ (hspec i).1.linkage.isWarp
      finiteCharacter := fun i ↦ (hspec i).1.linkage.finiteCharacter
      initialSet := fun i ↦ (hspec i).1.linkage.initialSet_eq
      links := fun i ↦ (hspec i).2.1 }
    stopover := D
    separating := fun i ↦ (hspec i).1
    frontier_eq := fun i ↦ (hspec i).2.2.1
    sources_subset := hAsource
    sources_card := hAcard }, rfl, ?_⟩
  intro i
  exact (hspec i).2.2.2

/-- The chosen simultaneous successor. -/
noncomputable def nextComposableTargetRowStage
    {kappa : Cardinal.{u}} {I : Type u}
    {rho : I → Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : ∀ i, rho i < kappa)
    (hinfinite : ∀ i, Cardinal.aleph0 ≤ rho i)
    (hindex : ∀ i, Cardinal.mk I ≤ rho i)
    (G : DWeb V) (hNorm : G.IsNormalized)
    {fixed : Set G.DPath} (hfixed : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : ComposableTargetRowStage G I rho) :
    ComposableTargetRowStage G I rho :=
  Classical.choose (exists_composableTargetRowStage_successor
    hlower hrho hinfinite hindex G hNorm hfixed hfixedSource S)

theorem nextComposableTargetRowStage_sources
    {kappa : Cardinal.{u}} {I : Type u}
    {rho : I → Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : ∀ i, rho i < kappa)
    (hinfinite : ∀ i, Cardinal.aleph0 ≤ rho i)
    (hindex : ∀ i, Cardinal.mk I ≤ rho i)
    (G : DWeb V) (hNorm : G.IsNormalized)
    {fixed : Set G.DPath} (hfixed : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : ComposableTargetRowStage G I rho) :
    (nextComposableTargetRowStage hlower hrho hinfinite hindex G hNorm
      hfixed hfixedSource S).row.sources =
        nextTargetSources G fixed S.row :=
  (Classical.choose_spec (exists_composableTargetRowStage_successor
    hlower hrho hinfinite hindex G hNorm hfixed hfixedSource S)).1

theorem nextComposableTargetRowStage_forward
    {kappa : Cardinal.{u}} {I : Type u}
    {rho : I → Cardinal.{u}}
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hrho : ∀ i, rho i < kappa)
    (hinfinite : ∀ i, Cardinal.aleph0 ≤ rho i)
    (hindex : ∀ i, Cardinal.mk I ≤ rho i)
    (G : DWeb V) (hNorm : G.IsNormalized)
    {fixed : Set G.DPath} (hfixed : G.IsWarp fixed)
    (hfixedSource : G.initialSet fixed ⊆ G.source)
    (S : ComposableTargetRowStage G I rho) (i : I) :
    G.ForwardExtension (S.row.paths i)
      ((nextComposableTargetRowStage hlower hrho hinfinite hindex G hNorm
        hfixed hfixedSource S).row.paths i) :=
  (Classical.choose_spec (exists_composableTargetRowStage_successor
    hlower hrho hinfinite hindex G hNorm hfixed hfixedSource S)).2 i

/-! ## The unconditional singular target-row machine -/

/-- Iterate exact composed row successors starting from the certified
zeroth row. -/
noncomputable def targetRowMachineOfCertified
    {G : DWeb V} {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : Cardinal.mk A₀ = kappa)
    (huncountable : Cardinal.aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hNorm : G.IsNormalized)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed)
    (S₀ : CertifiedTargetRowStage G (SingularMatrix.Index kappa)
      (SingularMatrix.scale kappa huncountable hsingular))
    (hS₀sources : S₀.row.sources =
      SingularMatrix.sourceLayer A₀ kappa hcard huncountable hsingular) :
    TargetRowMachine G fixed
      (SingularMatrix.sourceLayer A₀ kappa hcard
        huncountable hsingular) := by
  let rho : SingularMatrix.Index kappa → Cardinal.{u} :=
    SingularMatrix.scale kappa huncountable hsingular
  have hsource (i : SingularMatrix.Index kappa) :
      S₀.row.sources i ⊆ G.source := by
    rw [hS₀sources]
    exact (SingularMatrix.sourceLayer_subset A₀ kappa hcard
      huncountable hsingular i).trans hA₀
  have hsourceCard (i : SingularMatrix.Index kappa) :
      Cardinal.mk (S₀.row.sources i) = rho i := by
    rw [hS₀sources]
    exact SingularMatrix.sourceLayer_card A₀ kappa hcard
      huncountable hsingular i
  let initial : ComposableTargetRowStage G
      (SingularMatrix.Index kappa) rho :=
    ComposableTargetRowStage.ofCertified S₀ hsource hsourceCard
  let next : ComposableTargetRowStage G
      (SingularMatrix.Index kappa) rho →
      ComposableTargetRowStage G (SingularMatrix.Index kappa) rho :=
    fun S ↦ nextComposableTargetRowStage hlower
      (SingularMatrix.scale_below kappa huncountable hsingular)
      (SingularMatrix.scale_infinite kappa huncountable hsingular)
      (SingularMatrix.scale_index_le kappa huncountable hsingular)
      G hNorm hfixed.isWarp
      (hfixed.initialSet_eq.le.trans Set.diff_subset) S
  refine {
    State := ComposableTargetRowStage G
      (SingularMatrix.Index kappa) rho
    row := ComposableTargetRowStage.row
    initial := initial
    next := next
    sources_initial := ?_
    sources_next := ?_
    forward_next := ?_ }
  · exact hS₀sources
  · intro S
    exact nextComposableTargetRowStage_sources hlower
      (SingularMatrix.scale_below kappa huncountable hsingular)
      (SingularMatrix.scale_infinite kappa huncountable hsingular)
      (SingularMatrix.scale_index_le kappa huncountable hsingular)
      G hNorm hfixed.isWarp
      (hfixed.initialSet_eq.le.trans Set.diff_subset) S
  · intro S i
    exact nextComposableTargetRowStage_forward hlower
      (SingularMatrix.scale_below kappa huncountable hsingular)
      (SingularMatrix.scale_infinite kappa huncountable hsingular)
      (SingularMatrix.scale_index_le kappa huncountable hsingular)
      G hNorm hfixed.isWarp
      (hfixed.initialSet_eq.le.trans Set.diff_subset) S i

/-- Construct the certified zeroth row and then run the unconditional
composed-continuation machine. -/
noncomputable def singularTargetRowMachine
    {G : DWeb V} {A₀ : Set V} {kappa : Cardinal.{u}}
    (hA₀ : A₀ ⊆ G.source) (hcard : Cardinal.mk A₀ = kappa)
    (huncountable : Cardinal.aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hG : G.IsUnhindered) (hNorm : G.IsNormalized)
    {fixed : Set G.DPath}
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    TargetRowMachine G fixed
      (SingularMatrix.sourceLayer A₀ kappa hcard
        huncountable hsingular) := by
  let S₀ := initialCertifiedTargetRowStage hA₀ hcard huncountable
    hsingular hlower hG
  exact targetRowMachineOfCertified hA₀ hcard huncountable hsingular
    hlower hNorm hfixed S₀ rfl

/-- A quotient family whose initial set lies in the trimmed commitment set
avoids the old strict roof.  The only apparent exception in
`quotientPath_support_initial_or_avoids` is the initial vertex itself; it is
in `C = essential C`, and hence cannot be in the strict roof either. -/
theorem disjoint_lift_deletedQuotientFamily_strictRoof
    (G : DWeb V) {C Q : Set V}
    (htrim : IsTrimmedSeparator G C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hUstart : ((G.delete Q).quotient C).initialSet U ⊆ C) :
    Disjoint
      (G.vertexSet
        (G.liftQuotientFamily C (deletedQuotientFamily G C Q U)))
      (G.strictRoof C) := by
  apply Set.disjoint_left.2
  intro x hxU hxStrict
  obtain ⟨p, hpU', hxp⟩ := hxU
  obtain ⟨q, hqU', rfl⟩ := hpU'
  obtain ⟨r, hrU', rfl⟩ := hqU'
  obtain ⟨q₀, hq₀U, rfl⟩ := hrU'
  let q' : (G.quotient C).DPath :=
    (G.quotient C).liftDeletePath Q
      (G.liftDeleteQuotientPathToQuotientDelete C Q q₀)
  have hxq' : x ∈ q'.support := by
    simpa [q'] using hxp
  rcases G.quotientPath_support_initial_or_avoids C
      q' hxq' with
    hxInitial | hxAvoid
  · have hxC : x ∈ C := by
      rw [hxInitial]
      have hq₀C : q₀.initial ∈ C := hUstart ⟨q₀, hq₀U, rfl⟩
      simpa [q'] using hq₀C
    have hxEssential : x ∈ G.essential C := htrim.symm ▸ hxC
    exact Set.disjoint_left.1 (G.disjoint_strictRoof_essential C)
      hxStrict hxEssential
  · exact hxAvoid.1 hxStrict

/-- A family chosen in `(G - Q) / C` is automatically safe for a frozen
family whose vertices are either in `Q` or in the strict roof of `C`.  The
other hypotheses are the geometric pending-continuation data and the two
coverage statements needed by source star. -/
theorem exists_frozenPendingContinuation_of_deletedQuotientFamily
    (G : DWeb V) {F W : Set G.DPath} {C Q : Set V}
    (hF : G.IsWarp F) (hW : G.IsWarp W)
    (hFfinite : G.HasFiniteCharacter F)
    (hWfinite : G.HasFiniteCharacter W)
    (hroof : G.vertexSet W ⊆ G.roof C)
    (htrim : IsTrimmedSeparator G C)
    (hclean : SingularContinuation.TerminalCleanAt G W C)
    {U : Set ((G.delete Q).quotient C).DPath}
    (hU : ((G.delete Q).quotient C).IsWarp U)
    (hUfinite : ((G.delete Q).quotient C).HasFiniteCharacter U)
    (hUsource : ((G.delete Q).quotient C).initialSet U ⊆
      ((G.delete Q).quotient C).source)
    (hUstart : ((G.delete Q).quotient C).initialSet U ⊆ C)
    (hcover : G.terminalFrontier W ⊆
      ((G.delete Q).quotient C).initialSet U)
    (hFW : Disjoint (G.vertexSet F) (G.vertexSet W))
    (hFsafe : G.vertexSet F ⊆ Q ∪ G.strictRoof C) :
    ∃ W' : Set G.DPath,
      G.IsWarp W' ∧ G.HasFiniteCharacter W' ∧
      G.ForwardExtension (F ∪ W) W' ∧
      G.initialSet W' = G.initialSet (F ∪ W) ∧
      G.terminalFrontier W' ⊆
        G.terminalFrontier F ∪
          (G.quotient C).terminalFrontier
            (deletedQuotientFamily G C Q U) := by
  let U' : Set (G.quotient C).DPath :=
    deletedQuotientFamily G C Q U
  have hU' : (G.quotient C).IsWarp U' :=
    deletedQuotientFamily_isWarp hU
  have hU'finite : (G.quotient C).HasFiniteCharacter U' :=
    deletedQuotientFamily_hasFiniteCharacter hUfinite
  have hU'initial :
      (G.quotient C).initialSet U' =
        ((G.delete Q).quotient C).initialSet U :=
    deletedQuotientFamily_initialSet G C Q U
  have hU'start : (G.quotient C).initialSet U' ⊆ C := by
    rw [hU'initial]
    exact hUstart
  have hU'cover : G.terminalFrontier W ⊆
      (G.quotient C).initialSet U' := by
    rw [hU'initial]
    exact hcover
  have hsafe : Disjoint
      (G.vertexSet
        (G.liftQuotientFamily C U')) Q := by
    exact lift_deletedQuotientFamily_vertexSet_disjoint hUsource
  have hsafeStrict : Disjoint
      (G.vertexSet (G.liftQuotientFamily C U'))
      (G.strictRoof C) := by
    exact disjoint_lift_deletedQuotientFamily_strictRoof G htrim hUstart
  have hFU : Disjoint (G.vertexSet F)
      (G.vertexSet (SingularContinuation.liftedQuotientFamily G C U')) := by
    apply Set.disjoint_left.2
    intro x hxF hxU'
    rcases hFsafe hxF with hxQ | hxStrict
    · exact Set.disjoint_left.1 hsafe hxU' hxQ
    · exact Set.disjoint_left.1 hsafeStrict hxU' hxStrict
  exact SingularContinuation.exists_frozenPendingContinuation_of_componentwise_disjoint
    G hF hW hFfinite hWfinite hroof htrim hclean hU' hU'finite
      hU'start hU'cover hFW hFU

end SingularExtension

/-- The unconditional singular-cardinal extension clause.  The normalized
web's certified zeroth row is iterated by exact terminal-boundary quotient
composition, and the existing competitor-matrix limit then supplies the
full linkage. -/
theorem singularExtensionClauseAt
    (kappa : Cardinal.{u})
    (hkappa : Cardinal.aleph0 < kappa)
    (hsingular : kappa.IsSingular)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered) :
    ExtensionClauseAt Gamma kappa := by
  apply singularExtensionClauseAt_of_normalizedTargetRowMachine
    kappa hkappa hsingular Gamma
  intro A₀ hA₀ hcard fixed hfixed
  exact SingularExtension.singularTargetRowMachine
    hA₀ hcard hkappa hsingular hlower hGamma.normalized
      Gamma.normalized_isNormalized hfixed

end CardinalInduction
end Erdos599
