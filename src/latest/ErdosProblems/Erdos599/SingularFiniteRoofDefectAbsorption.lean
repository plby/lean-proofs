/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularFiniteTargetGapAbsorption
import ErdosProblems.Erdos599.RegularCleanExchange
import ErdosProblems.Erdos599.HalfwayRetainedLaterLinkage
import ErdosProblems.Erdos599.SingularMarkedResidualTouchedPaths
import ErdosProblems.Erdos599.SingularFiniteExactBoundaryRepair

/-!
# Absorbing a finite defect in a wave separator

Suppose a finite-character warp starts at source vertices and its terminal
frontier, together with a finite set `F`, roofs the whole source.  Cutting the
warp at its first visit to `terminalFrontier W ∪ F` loses only finitely many
of its old terminal vertices: a lost component has to meet `F`, and a
disjoint family has only finitely many such components.

The first-hit family is terminal-clean.  We therefore retype it, without
changing a single vertex, in the normalized retargeted web.  Finite target-gap
absorption there produces a wave retaining all old initial vertices.  Lifting
normalization and composing separators gives the desired wave in the original
web.  This is the finite freed-carrier correction needed by the singular
exchange argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularFiniteRoofDefectAbsorption

open DWeb
open SliceCandidate
open SliceSpliceSource
open SingularContinuation
open SingularMarkedResidualTouchedPaths
open SingularFiniteExactBoundaryRepair
open SingularFiniteTargetGapAbsorption
open _root_.Erdos599.Blueprint.LinkageBlueprint

universe u

variable {V : Type u}

/-- A finite-character warp is a linkage between its own two endpoint sets. -/
theorem isLinkageBetween_own_endpoints
    {G : DWeb V} {W : Set G.DPath}
    (hW : G.IsWarp W) (hfinite : G.HasFiniteCharacter W) :
    IsLinkageBetween G (G.initialSet W) (G.terminalFrontier W) W := by
  refine ⟨hW, hfinite, rfl, Set.Subset.rfl, ?_⟩
  intro p hp
  obtain ⟨q, rfl⟩ := hfinite hp
  have hsource : q.support ∩ G.initialSet W = {q.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxq, hxinitial⟩
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
        ⟨(Sum.inl q : G.DPath), hp, rfl⟩⟩
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

/-- Retype an endpoint-clean finite member in the normalized graph without
truncating it. -/
noncomputable def normalizeEndpointCleanMember
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target)
    (p : Y) : K.normalized.DPath := by
  let q := K.finiteMemberPath Y hfinite p
  have hpq : p.1 = (.inl q : K.DPath) := K.finiteMemberPath_eq Y hfinite p
  let hs : ∀ {z}, z ∈ q.walk.support.tail → z ∉ K.source := by
    intro z hz hzA
    have hzSupport : z ∈ q.support := List.mem_of_mem_tail hz
    have hzInitial := hsource p.1 p.2 (by
      rw [hpq]
      exact ⟨hzSupport, hzA⟩)
    have hzeq : z = q.start := by
      have hzeq' : z = p.1.initial := Set.mem_singleton_iff.mp hzInitial
      rw [hpq] at hzeq'
      exact hzeq'
    exact DWeb.walk_start_not_mem_tail2 q.walk q.isPath (hzeq ▸ hz)
  let ht : ∀ {z}, z ∈ q.walk.support.dropLast → z ∉ K.target := by
    intro z hz hzB
    have hzSupport : z ∈ q.support := List.mem_of_mem_dropLast hz
    have hzSupport' : z ∈ p.1.support := by
      rw [hpq]
      exact hzSupport
    have hzTerminal := htarget p.1 p.2 z hzSupport' hzB
    have hzeq : z = q.finish := by
      rw [hpq] at hzTerminal
      exact (Option.some.inj hzTerminal).symm
    exact DWeb.walk_finish_not_mem_dropLast2 q.walk q.isPath (hzeq ▸ hz)
  exact .inl
    { start := q.start
      finish := q.finish
      walk := K.normalizeWalk q.walk hs ht
      isPath := by
        change (K.normalizeWalk q.walk hs ht).support.Nodup
        rw [K.support_normalizeWalk]
        exact q.isPath }

@[simp] theorem support_normalizeEndpointCleanMember
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) (p : Y) :
    (normalizeEndpointCleanMember K hfinite hsource htarget p).support =
      p.1.support := by
  let q := K.finiteMemberPath Y hfinite p
  have hpq : p.1 = (.inl q : K.DPath) := K.finiteMemberPath_eq Y hfinite p
  ext x
  change x ∈ (K.normalizeWalk q.walk _ _).support ↔ x ∈ p.1.support
  rw [K.support_normalizeWalk, hpq]
  rfl

@[simp] theorem initial_normalizeEndpointCleanMember
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) (p : Y) :
    (normalizeEndpointCleanMember K hfinite hsource htarget p).initial =
      p.1.initial := by
  let q := K.finiteMemberPath Y hfinite p
  have hpq : p.1 = (.inl q : K.DPath) := K.finiteMemberPath_eq Y hfinite p
  change q.start = p.1.initial
  rw [hpq]
  rfl

@[simp] theorem terminal_normalizeEndpointCleanMember
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) (p : Y) :
    K.normalized.terminal?
        (normalizeEndpointCleanMember K hfinite hsource htarget p) =
      K.terminal? p.1 := by
  let q := K.finiteMemberPath Y hfinite p
  have hpq : p.1 = (.inl q : K.DPath) := K.finiteMemberPath_eq Y hfinite p
  change some q.finish = K.terminal? p.1
  rw [hpq]
  rfl

/-- The vertex-preserving normalized copy of an endpoint-clean family. -/
noncomputable def normalizeEndpointCleanFamily
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) :
    Set K.normalized.DPath :=
  normalizeEndpointCleanMember K hfinite hsource htarget '' Set.univ

theorem normalizeEndpointCleanFamily_isWarp
    (K : DWeb V) {Y : Set K.DPath}
    (hY : K.IsWarp Y) (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) :
    K.normalized.IsWarp
      (normalizeEndpointCleanFamily K hfinite hsource htarget) := by
  rintro _ ⟨p, _hp, rfl⟩ _ ⟨q, _hq, rfl⟩ hpq
  change Disjoint
    (normalizeEndpointCleanMember K hfinite hsource htarget p).support
    (normalizeEndpointCleanMember K hfinite hsource htarget q).support
  rw [support_normalizeEndpointCleanMember,
    support_normalizeEndpointCleanMember]
  apply hY p.2 q.2
  intro hpqval
  have hpqsub : p = q := Subtype.ext hpqval
  subst q
  exact hpq rfl

theorem normalizeEndpointCleanFamily_finiteCharacter
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) :
    K.normalized.HasFiniteCharacter
      (normalizeEndpointCleanFamily K hfinite hsource htarget) := by
  rintro _ ⟨p, _hp, rfl⟩
  simp only [normalizeEndpointCleanMember]
  exact ⟨_, rfl⟩

@[simp] theorem initialSet_normalizeEndpointCleanFamily
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) :
    K.normalized.initialSet
        (normalizeEndpointCleanFamily K hfinite hsource htarget) =
      K.initialSet Y := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpx⟩
    exact ⟨p.1, p.2, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    let pY : Y := ⟨p, hp⟩
    exact ⟨normalizeEndpointCleanMember K hfinite hsource htarget pY,
      ⟨pY, Set.mem_univ pY, rfl⟩, by simpa using hpx⟩

@[simp] theorem terminalFrontier_normalizeEndpointCleanFamily
    (K : DWeb V) {Y : Set K.DPath}
    (hfinite : K.HasFiniteCharacter Y)
    (hsource : ∀ p ∈ Y, p.support ∩ K.source ⊆ {p.initial})
    (htarget : TerminalCleanAt K Y K.target) :
    K.normalized.terminalFrontier
        (normalizeEndpointCleanFamily K hfinite hsource htarget) =
      K.terminalFrontier Y := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpx⟩
    exact ⟨p.1, p.2, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    let pY : Y := ⟨p, hp⟩
    exact ⟨normalizeEndpointCleanMember K hfinite hsource htarget pY,
      ⟨pY, Set.mem_univ pY, rfl⟩, by simpa using hpx⟩

/-- A finite addition to the terminal frontier of a source-starting warp can
be absorbed into a genuine wave without losing any old initial vertex. -/
theorem exists_wave_initialSet_superset_of_finite_roof_defect
    {H : DWeb V} (hNorm : H.IsNormalized)
    {W : Set H.DPath} (hW : H.IsWarp W)
    (hfinite : H.HasFiniteCharacter W)
    (hinitial : H.initialSet W ⊆ H.source)
    {F : Set V} (hFfinite : F.Finite)
    (hroof : H.source ⊆ H.roof (H.terminalFrontier W ∪ F)) :
    ∃ U : Set H.DPath, H.IsWave U ∧
      H.initialSet W ⊆ H.initialSet U := by
  let S := H.terminalFrontier W
  let D := S ∪ F
  let hL : IsLinkageBetween H (H.initialSet W) S W :=
    isLinkageBetween_own_endpoints hW hfinite
  let hsep : RelationalRoof.Separates H.graph.Adj
      (H.initialSet W) S D := by
    intro r t p _hr ht
    exact ⟨t, p.end_mem_support, Set.mem_union_left F ht⟩
  let Y := firstHitPrefixFamily hL hsep
  have hY : IsLinkageBetween H (H.initialSet W) D Y :=
    firstHitPrefixFamily_isLinkageBetween hL hsep
  have hYclean : TerminalCleanAt H Y D :=
    RegularCleanExchange.firstHitPrefixFamily_terminalClean hL hsep
  let PM := pathsMeetingVertices H W F
  have hPMfinite : PM.Finite :=
    pathsMeetingVertices_finite_of_isWarp hW hFfinite
  have hAvoidTight : MeetsOnlyAtTerminal H (W \ PM) D := by
    intro p hp x hxp hxD
    rcases hxD with hxS | hxF
    · exact H.fd_terminal_eq_of_mem_support_frontier
        hW hfinite hp.1 hxp hxS
    · exact False.elim (hp.2 ⟨hp.1, ⟨x, hxp, hxF⟩⟩)
  have hAvoidY : W \ PM ⊆ Y :=
    firstHitPrefixFamily_contains_of_subset_of_meetsOnlyAtTerminal
      hL hsep Set.sdiff_subset hAvoidTight
  have hgapFinite : (D \ H.terminalFrontier Y).Finite := by
    apply (hFfinite.union
      (terminalFrontier_finite_of_family_finite hPMfinite)).subset
    rintro x ⟨hxD, hxnotY⟩
    by_cases hxF : x ∈ F
    · exact Set.mem_union_left _ hxF
    · have hxS : x ∈ S := hxD.resolve_right hxF
      obtain ⟨p, hpW, hpTerminal⟩ := hxS
      by_cases hpPM : p ∈ PM
      · exact Set.mem_union_right _ ⟨p, hpPM, hpTerminal⟩
      · have hpY : p ∈ Y := hAvoidY ⟨hpW, hpPM⟩
        exact False.elim (hxnotY ⟨p, hpY, hpTerminal⟩)
  let K := H.retarget D
  let YK : Set K.DPath := Y
  have hYK : IsLinkageBetween K (H.initialSet W) D YK := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change H.IsWarp Y
      exact hY.isWarp
    · change H.HasFiniteCharacter Y
      exact hY.finiteCharacter
    · change H.initialSet Y = H.initialSet W
      exact hY.initialSet_eq
    · change H.terminalFrontier Y ⊆ D
      exact hY.terminalFrontier_subset
    · intro p hp
      change IsPathBetween H (H.initialSet W) D p
      exact hY.2.2.2.2 p hp
  have hYKclean : TerminalCleanAt K YK K.target := by
    intro p hp x hxp hxD
    change H.terminal? p = some x
    exact hYclean p hp x hxp hxD
  have hYsourceClean :
      ∀ p ∈ YK, p.support ∩ K.source ⊆ {p.initial} := by
    intro p hp x hx
    exact Set.mem_singleton_iff.mpr
      (hNorm.eq_initial_of_mem_path p hx.1 hx.2)
  let Yn := normalizeEndpointCleanFamily K hYK.finiteCharacter
    hYsourceClean hYKclean
  have hYnWarp : K.normalized.IsWarp Yn :=
    normalizeEndpointCleanFamily_isWarp K hYK.isWarp hYK.finiteCharacter
      hYsourceClean hYKclean
  have hYnFinite : K.normalized.HasFiniteCharacter Yn :=
    normalizeEndpointCleanFamily_finiteCharacter K hYK.finiteCharacter
      hYsourceClean hYKclean
  have hYnInitialEq :
      K.normalized.initialSet Yn = H.initialSet Y := by
    rw [show K.normalized.initialSet Yn = K.initialSet YK by
      exact initialSet_normalizeEndpointCleanFamily K hYK.finiteCharacter
        hYsourceClean hYKclean]
    ext x
    rfl
  have hYnTerminalEq :
      K.normalized.terminalFrontier Yn = H.terminalFrontier Y := by
    rw [show K.normalized.terminalFrontier Yn = K.terminalFrontier YK by
      exact terminalFrontier_normalizeEndpointCleanFamily K
        hYK.finiteCharacter hYsourceClean hYKclean]
    ext x
    rfl
  have hYnInitial : K.normalized.initialSet Yn ⊆ K.normalized.source := by
    rw [hYnInitialEq]
    change H.initialSet Y ⊆ H.source
    exact hY.initialSet_eq.symm ▸ hinitial
  have hYnTerminal :
      K.normalized.terminalFrontier Yn ⊆ K.normalized.target := by
    rw [hYnTerminalEq]
    change H.terminalFrontier Y ⊆ D
    exact hY.terminalFrontier_subset
  have hYnClean : K.normalized.IsCleanFiniteWarp Yn :=
    AlternativeMaximalLinkage.cleanFiniteWarp_of_normalized
      K.normalized_isNormalized hYnWarp hYnFinite hYnInitial hYnTerminal
  have hgapNormalized :
      (K.normalized.target \
        K.normalized.terminalFrontier Yn).Finite := by
    rw [hYnTerminalEq]
    change (D \ H.terminalFrontier Y).Finite
    exact hgapFinite
  obtain ⟨Un, hUn, hYnUn⟩ :=
    exists_wave_initialSet_superset_of_finite_target_gap
      K.normalized_isNormalized hYnClean hgapNormalized
  let U := K.liftNormalizedFamily Un
  have hUK : K.IsWave U := hUn.liftNormalizedFamily
  have hUH : H.IsWave U := DWeb.IsWave.of_retarget H hUK hroof
  refine ⟨U, hUH, ?_⟩
  intro x hxW
  have hxY : x ∈ H.initialSet Y := by
    rw [hY.initialSet_eq]
    exact hxW
  have hxYn : x ∈ K.normalized.initialSet Yn := by
    rw [hYnInitialEq]
    exact hxY
  have hxUn : x ∈ K.normalized.initialSet Un := hYnUn hxYn
  change x ∈ K.initialSet (K.liftNormalizedFamily Un)
  rw [K.initialSet_liftNormalizedFamily]
  exact hxUn

#print axioms exists_wave_initialSet_superset_of_finite_roof_defect

end SingularFiniteRoofDefectAbsorption
end CardinalInduction
end Erdos599
