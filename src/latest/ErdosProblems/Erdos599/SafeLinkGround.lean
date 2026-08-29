/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CommonQuotient
import ErdosProblems.Erdos599.SafeLink

/-!
# Bringing a countable Section 6 wave to the ground

This file contains the limit bookkeeping used after the finite deletion
stages in the proof of Aharoni--Berger Theorem 6.1.  The substantial
stage-local statements are `SafeLink.assertion_6_5`,
`SafeLink.assertion_6_6_stage`, and `SafeLink.assertion_6_8_stage`.  What is
missing from those statements is the passage through the concrete countable
up-arrow.

The key point is stronger than mere support containment: if a path in a
direct limit has a terminal vertex, then one of the finite accumulated
stages already has a path with that terminal.  This makes Assertion 6.5
stable at the limit.  Support containment makes Assertion 6.6 stable at the
limit.  Both arguments use the actual `waveChainUpper` construction rather
than an abstract limit postulate.
-/

namespace Erdos599
namespace SafeLinkGround

open Set DirectedPath

universe u

variable {V : Type u}

namespace DirectedPath
namespace FinitePath

/-- If a prefix of a finite simple path already contains the latter path's
last vertex, the prefix is the whole path (at the level of ordered support).
-/
theorem support_eq_of_isPrefixOf_of_finish_mem
    {D : Digraph V} {p q : FinitePath D} (hpq : p.IsPrefixOf q)
    (hfinish : q.finish ∈ p.support) :
    p.walk.support = q.walk.support := by
  rcases hpq with ⟨tail, htail⟩
  by_cases hempty : tail = []
  · simpa [hempty] using htail
  · exfalso
    have hnodup : (p.walk.support ++ tail).Nodup := by
      rw [htail]
      exact q.isPath
    have hdisjoint := hnodup.disjoint
    have hlast : (p.walk.support ++ tail).getLast
        (by rw [htail]; exact q.walk.support_ne_nil) = q.finish := by
      simpa only [htail] using q.walk.getLast_support
    have hlastTail : (p.walk.support ++ tail).getLast
        (by rw [htail]; exact q.walk.support_ne_nil) =
          tail.getLast hempty :=
      List.getLast_append_of_ne_nil _ hempty
    have hfinishTail : q.finish ∈ tail := by
      have heq : tail.getLast hempty = q.finish := hlastTail.symm.trans hlast
      rw [← heq]
      exact List.getLast_mem hempty
    exact List.disjoint_left.1 hdisjoint hfinish hfinishTail

/-- A finite member of an extension chain which contains the terminal of a
finite upper path already terminates there. -/
theorem terminal_eq_of_extends_of_mem_finish
    {D : Digraph V} {p : Path D} {q : FinitePath D}
    (hpq : Path.Extends p (.inl q)) (hfinish : q.finish ∈ p.support) :
    Path.terminal? p = some q.finish := by
  rcases p with p | r
  · have hsupp := support_eq_of_isPrefixOf_of_finish_mem hpq hfinish
    have hfinishEq : p.finish = q.finish := by
      calc
        p.finish = p.walk.support.getLast p.walk.support_ne_nil :=
          p.walk.getLast_support.symm
        _ = q.walk.support.getLast q.walk.support_ne_nil := by
          simpa only [hsupp]
        _ = q.finish := q.walk.getLast_support
    simpa only [Path.terminal?_finite, hfinishEq]
  · exact False.elim hpq

end FinitePath
end DirectedPath

namespace DWeb

variable (G : DWeb V)

/-- Transport terminal-frontier disjointness back across an equality of
webs.  Keeping the equality abstract is important: it lets dependent path
families reduce before a concrete deletion equality is substituted. -/
theorem disjoint_terminalFrontier_of_transport
    {H K : DWeb V} (h : H = K) {T : Set V} (W : H.Wave)
    (hdisj : Disjoint T (K.terminalFrontier (h ▸ W).1)) :
    Disjoint T (H.terminalFrontier W.1) := by
  subst K
  exact hdisj

/-- Every terminal of a concrete direct-limit wave is already a terminal
of one wave in the underlying chain.  This is the converse direction to the
eventual-terminal lemma needed for the Section 6 disjointness argument. -/
theorem terminalFrontier_waveChainUpper_subset_iUnion
    (c : Set G.Wave) (hcne : c.Nonempty) (hc : IsChain (· ≤ ·) c) :
    G.terminalFrontier (G.waveChainUpper c hcne hc) ⊆
      ⋃ U : c, G.terminalFrontier U.1.1 := by
  rintro x ⟨q, ⟨a, hqa⟩, hqterm⟩
  subst q
  let C := G.waveThread c a.1
  have hxSupport : x ∈ (G.waveThreadLimit c hcne hc a).support :=
    G.terminal_mem_support hqterm
  have hxUnion : x ∈ ⋃ p ∈ C, p.support := by
    simpa only [Erdos599.DWeb.waveThreadLimit,
      DirectedPath.Path.support_chainLimit]
      using hxSupport
  simp only [Set.mem_iUnion] at hxUnion ⊢
  obtain ⟨p, hpC, hxp⟩ := hxUnion
  obtain ⟨U, hUc, hpU, _hpInitial⟩ := hpC
  rcases hlimit : G.waveThreadLimit c hcne hc a with q | r
  · have hqx : q.finish = x := by
      simpa only [hlimit, DWeb.terminal?_finite, Option.some.injEq] using hqterm
    have hpExt : DirectedPath.Path.Extends p (.inl q) := by
      have := DirectedPath.Path.extends_chainLimit C
        (G.waveThread_nonempty (G.waveChainBase_mem c hcne) a.2)
        (G.waveThread_isChain hc a.1) ⟨U, hUc, hpU, _hpInitial⟩
      change DirectedPath.Path.Extends p
        (G.waveThreadLimit c hcne hc a) at this
      rw [hlimit] at this
      exact this
    have hpterm : G.terminal? p = some x := by
      have := DirectedPath.FinitePath.terminal_eq_of_extends_of_mem_finish
        hpExt (hqx ▸ hxp)
      simpa only [DWeb.terminal?, hqx] using this
    exact ⟨⟨U, hUc⟩, p, hpU, hpterm⟩
  · rw [hlimit] at hqterm
    simp only [DWeb.terminal?_ray] at hqterm
    cases hqterm

/-- Specialized to the concrete countable up-arrow: a final terminal
already occurs at a finite accumulated-arrow stage. -/
theorem terminalFrontier_omegaArrow_subset_iUnion_stages
    (W : ℕ → G.Wave) :
    G.terminalFrontier (G.omegaArrow W).1 ⊆
      ⋃ n, G.terminalFrontier (G.omegaArrowStage W n).1 := by
  let c := Set.range (G.omegaArrowStage W)
  let hcne := G.omegaArrowStage_range_nonempty W
  let hc := G.omegaArrowStage_range_isChain W
  intro x hx
  have hx' : x ∈ ⋃ U : c, G.terminalFrontier U.1.1 :=
    terminalFrontier_waveChainUpper_subset_iUnion G c hcne hc (by
      simpa only [Erdos599.DWeb.omegaArrow,
        Erdos599.DWeb.waveChainUpperWave] using hx)
  simp only [Set.mem_iUnion] at hx' ⊢
  obtain ⟨U, hxU⟩ := hx'
  obtain ⟨n, hn⟩ := U.2
  exact ⟨n, hn ▸ hxU⟩

/-- Assertion 6.5 passes from all finite accumulated stages to their
countable up-arrow. -/
theorem terminal_disjoint_omegaArrow_of_stages
    (W : ℕ → G.Wave) {T : Set V}
    (hstage : ∀ n, Disjoint T
      (G.terminalFrontier (G.omegaArrowStage W n).1)) :
    Disjoint T (G.terminalFrontier (G.omegaArrow W).1) := by
  rw [Set.disjoint_left]
  intro x hxT hxTerm
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp
    (terminalFrontier_omegaArrow_subset_iUnion_stages G W hxTerm)
  exact Set.disjoint_left.1 (hstage n) hxT hxn

/-- Assertion 6.6 passes from all finite accumulated stages to their
countable up-arrow. -/
theorem vertexSet_disjoint_omegaArrow_of_stages
    (W : ℕ → G.Wave) {Q : Set V}
    (hstage : ∀ n, Disjoint
      (G.vertexSet (G.omegaArrowStage W n).1) Q) :
    Disjoint (G.vertexSet (G.omegaArrow W).1) Q := by
  rw [Set.disjoint_left]
  intro x hxVertex hxQ
  let c := Set.range (G.omegaArrowStage W)
  let hcne := G.omegaArrowStage_range_nonempty W
  let hc := G.omegaArrowStage_range_isChain W
  have hx' : x ∈ ⋃ U : c, G.vertexSet U.1.1 :=
    G.vertexSet_waveChainUpper_subset_iUnion c hcne hc (by
      simpa only [Erdos599.DWeb.omegaArrow,
        Erdos599.DWeb.waveChainUpperWave] using hxVertex)
  simp only [Set.mem_iUnion] at hx'
  obtain ⟨U, hxU⟩ := hx'
  obtain ⟨n, hn⟩ := U.2
  exact Set.disjoint_left.1 (hstage n) (hn ▸ hxU) hxQ

/-! ## The finite deletion recursion

The state below keeps the changing deleted web in a dependent field.  At a
successful enumeration step the new point is outside the current wave.  We
therefore restrict that wave through the new singleton deletion and take a
maximal forward extension in the new web.  This is the concrete
``delete--arrow--maximize'' step of the bring-down construction; maximal
extension absorbs the separate arrow with an arbitrary maximal wave.
-/

/-- One finite stage of the bring-down recursion. -/
structure GroundState (G : DWeb V) (a : V) (X : Set V) where
  removed : Set V
  removed_finite : removed.Finite
  removed_subset : removed ⊆ X
  wave : ((G.delete {a}).delete removed).Wave
  roofMaximal : ((G.delete {a}).delete removed).IsRoofMaximal wave

/-- The recursion starts with a roof-maximal wave after deleting the root.
-/
noncomputable def initialGroundState (G : DWeb V) (a : V) (X : Set V) :
    GroundState G a X := by
  let H := (G.delete {a}).delete ∅
  let M : H.Wave := Classical.choose H.exists_roofMaximal_wave
  have hM : H.IsRoofMaximal M :=
    Classical.choose_spec H.exists_roofMaximal_wave
  refine {
    removed := ∅
    removed_finite := Set.finite_empty
    removed_subset := Set.empty_subset X
    wave := M
    roofMaximal := hM }

/-- Add a vertex outside the current wave and maximize again in the
enlarged deletion. -/
noncomputable def GroundState.add
    {G : DWeb V} {a : V} {X : Set V} (s : GroundState G a X)
    (x : V) (hxX : x ∈ X)
    (hxWave : x ∉ ((G.delete {a}).delete s.removed).vertexSet s.wave.1) :
    GroundState G a X := by
  let H := (G.delete {a}).delete s.removed
  have hAvoid : Disjoint (H.vertexSet s.wave.1) ({x} : Set V) := by
    rw [Set.disjoint_singleton_right]
    exact hxWave
  let restricted : (H.delete {x}).Wave :=
    ⟨H.restrictDeleteFamily {x} s.wave.1 hAvoid,
      DWeb.IsWave.restrictDeleteFamily H s.wave.2 hAvoid⟩
  have heq : H.delete {x} =
      (G.delete {a}).delete (insert x s.removed) := by
    simpa only [H] using
      (G.delete {a}).delete_delete_singleton s.removed x
  let restricted' : ((G.delete {a}).delete (insert x s.removed)).Wave :=
    heq ▸ restricted
  let target := (G.delete {a}).delete (insert x s.removed)
  let M : target.Wave := Classical.choose
    (target.exists_maximal_wave_extending restricted')
  have hMspec : restricted' ≤ M ∧ IsMax M :=
    Classical.choose_spec (target.exists_maximal_wave_extending restricted')
  exact {
    removed := insert x s.removed
    removed_finite := s.removed_finite.insert x
    removed_subset := Set.insert_subset hxX s.removed_subset
    wave := M
    roofMaximal :=
      ((G.delete {a}).delete (insert x s.removed)).isRoofMaximal_of_isMax
        hMspec.2 }

/-- Process one enumerated vertex.  A point is deleted exactly when it is
in `X`, has not already been deleted, and does not lie on the current
accumulated wave. -/
noncomputable def GroundState.next
    {G : DWeb V} {a : V} {X : Set V} (s : GroundState G a X) (x : V) :
    GroundState G a X := by
  classical
  exact if h : x ∈ X ∧ x ∉ s.removed ∧
      x ∉ ((G.delete {a}).delete s.removed).vertexSet s.wave.1 then
    s.add x h.1 h.2.2
  else s

/-- The countable finite-deletion recursion driven by an enumeration. -/
noncomputable def groundState (G : DWeb V) (a : V) (X : Set V)
    (e : ℕ → V) : ℕ → GroundState G a X
  | 0 => initialGroundState G a X
  | n + 1 => (groundState G a X e n).next (e n)

@[simp]
theorem groundState_zero (G : DWeb V) (a : V) (X : Set V)
    (e : ℕ → V) :
    groundState G a X e 0 = initialGroundState G a X :=
  rfl

@[simp]
theorem groundState_succ (G : DWeb V) (a : V) (X : Set V)
    (e : ℕ → V) (n : ℕ) :
    groundState G a X e (n + 1) =
      (groundState G a X e n).next (e n) :=
  rfl

theorem GroundState.removed_subset_next
    {G : DWeb V} {a : V} {X : Set V} (s : GroundState G a X) (x : V) :
    s.removed ⊆ (s.next x).removed := by
  classical
  unfold GroundState.next
  split
  · exact Set.subset_insert x s.removed
  · exact Set.Subset.rfl

/-- The deleted finite sets increase with the stage number. -/
theorem groundState_removed_monotone
    (G : DWeb V) (a : V) (X : Set V) (e : ℕ → V) :
    Monotone (fun n ↦ (groundState G a X e n).removed) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [groundState_succ]
  exact (groundState G a X e n).removed_subset_next (e n)

/-- If the enumerated point is still absent from both the deletion and the
current wave, it is inserted at the next stage. -/
theorem groundState_mem_removed_succ_of_available
    (G : DWeb V) (a : V) (X : Set V) (e : ℕ → V) (n : ℕ)
    (hxX : e n ∈ X)
    (hxR : e n ∉ (groundState G a X e n).removed)
    (hxWave : e n ∉ ((G.delete {a}).delete
      (groundState G a X e n).removed).vertexSet
        (groundState G a X e n).wave.1) :
    e n ∈ (groundState G a X e (n + 1)).removed := by
  classical
  rw [groundState_succ]
  have h : e n ∈ X ∧
      e n ∉ (groundState G a X e n).removed ∧
      e n ∉ ((G.delete {a}).delete
        (groundState G a X e n).removed).vertexSet
          (groundState G a X e n).wave.1 := ⟨hxX, hxR, hxWave⟩
  rw [GroundState.next, dif_pos h]
  change e n ∈ insert (e n) (groundState G a X e n).removed
  exact Set.mem_insert _ _

/-- Every point of `X` covered by the enumeration is eventually either
deleted or lies on the current stage wave.  This is the exact scheduling
invariant used when passing to the final deletion union. -/
theorem eventually_removed_or_mem_stageWave
    (G : DWeb V) (a : V) {X : Set V} {e : ℕ → V}
    (henum : X ⊆ Set.range e) {x : V} (hxX : x ∈ X) :
    ∃ n, x ∈ (groundState G a X e n).removed ∨
      x ∈ ((G.delete {a}).delete
        (groundState G a X e n).removed).vertexSet
          (groundState G a X e n).wave.1 := by
  obtain ⟨n, hn⟩ := henum hxX
  subst x
  by_cases hxR : e n ∈ (groundState G a X e n).removed
  · exact ⟨n, Or.inl hxR⟩
  by_cases hxWave : e n ∈ ((G.delete {a}).delete
      (groundState G a X e n).removed).vertexSet
        (groundState G a X e n).wave.1
  · exact ⟨n, Or.inr hxWave⟩
  · exact ⟨n + 1, Or.inl
      (groundState_mem_removed_succ_of_available G a X e n hxX hxR hxWave)⟩

/-- Assertion 6.5 applies at every finite recursion stage. -/
theorem groundState_terminal_disjoint_tree
    (G : DWeb V) {a : V} {T X : Set V} (hT : G.IsTreeSet a T)
    (hXT : X ⊆ T \ {a}) (e : ℕ → V) (n : ℕ) :
    Disjoint T (((G.delete {a}).delete
      (groundState G a X e n).removed).terminalFrontier
        (groundState G a X e n).wave.1) := by
  let R := (groundState G a X e n).removed
  have heq : (G.delete {a}).delete R = G.delete (insert a R) := by
    rw [G.delete_delete]
    rfl
  let W' : (G.delete (insert a R)).Wave :=
    heq ▸ (groundState G a X e n).wave
  have hdisj : Disjoint T
      ((G.delete (insert a R)).terminalFrontier W'.1) :=
    SafeLink.assertion_6_5 G hT
    (groundState G a X e n).removed_finite
    ((groundState G a X e n).removed_subset.trans hXT) W'.2
  change Disjoint T (((G.delete {a}).delete R).terminalFrontier
    (groundState G a X e n).wave.1)
  exact disjoint_terminalFrontier_of_transport heq
    (groundState G a X e n).wave hdisj

/-- Assertion 6.6 applies at every finite recursion stage once `Q` is the
set of non-bounded tree vertices. -/
theorem groundState_vertexSet_disjoint_nonBounded
    (G : DWeb V) (hG : G.IsNormalized) {a : V} (ha : a ∈ G.source)
    {T X : Set V} (hT : G.IsTreeSet a T) (hXT : X ⊆ T \ {a})
    (e : ℕ → V) (n : ℕ) :
    Disjoint (((G.delete {a}).delete
      (groundState G a X e n).removed).vertexSet
        (groundState G a X e n).wave.1)
      (SafeLink.nonBoundedTreeVertices G a T) := by
  let R := (groundState G a X e n).removed
  have hterminal : Disjoint (SafeLink.nonBoundedTreeVertices G a T)
      (((G.delete {a}).delete R).terminalFrontier
        (groundState G a X e n).wave.1) := by
    rw [Set.disjoint_left]
    intro q hqQ hqTerminal
    exact Set.disjoint_left.1
      (groundState_terminal_disjoint_tree G hT hXT e n)
      (SafeLink.nonBoundedTreeVertices_subset_tree G a T hqQ) hqTerminal
  exact SafeLink.assertion_6_6_stage G hG ha hT
    (groundState G a X e n).removed_finite.countable
    ((groundState G a X e n).removed_subset.trans hXT)
    (groundState G a X e n).wave.2 hterminal rfl

end DWeb

end SafeLinkGround
end Erdos599
