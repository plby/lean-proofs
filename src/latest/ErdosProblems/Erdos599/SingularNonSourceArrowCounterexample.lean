/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularNonSourceArrowProfile
import ErdosProblems.Erdos599.RegularRightBoundary

/-!
# The non-source arrow loses deleted target coordinates

Splitting a linkage carrier into its source and non-source parts is not by
itself a complete maximal-wave restoration.  The non-source part still
contains the selected target endpoints.  In the quotient those endpoints
are new sources as well as old targets, so every quotient wave has a
component supported at such an endpoint.  That component cannot meet a
deleted-web roof at a retained vertex.

The branching-stage safe edge gives a minimal counterexample.  Its carrier
is `{u,b}` and its non-source part is `{b}`.  Deleting the whole carrier is
safe (indeed, it deletes the only source), but `NonSourceArrowExchange`
fails.  Thus a sound unconditional producer must keep or reroute the target
colour simultaneously with the residual wave; a bare deletion--quotient
arrow over the entire non-source carrier is too strong.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularNonSourceArrowCounterexample

open DirectedPath SingularNonSourceArrowProfile
open RegularRightBoundary.BranchingStage.Vertex

abbrev G : DWeb RegularRightBoundary.BranchingStage.Vertex :=
  RegularRightBoundary.BranchingStage.web

abbrev P : Set G.DPath :=
  RegularRightBoundary.BranchingStage.targetFamily

abbrev X : Set RegularRightBoundary.BranchingStage.Vertex :=
  G.vertexSet P

@[simp] theorem vertexSet_targetFamily : X = ({u, b} : Set
    RegularRightBoundary.BranchingStage.Vertex) := by
  ext x
  simp only [X, P, DWeb.mem_vertexSet,
    RegularRightBoundary.BranchingStage.targetFamily]
  constructor
  · rintro ⟨p, rfl, hxp⟩
    change x ∈ RegularRightBoundary.BranchingStage.ub.support at hxp
    simpa only [RegularRightBoundary.BranchingStage.ub_support] using hxp
  · intro hx
    refine ⟨Sum.inl RegularRightBoundary.BranchingStage.ub, rfl, ?_⟩
    change x ∈ RegularRightBoundary.BranchingStage.ub.support
    simpa only [RegularRightBoundary.BranchingStage.ub_support] using hx

@[simp] theorem nonSourceCarrier_eq : X \ G.source = {b} := by
  rw [vertexSet_targetFamily]
  ext x
  cases x <;> simp [G, RegularRightBoundary.BranchingStage.web]

@[simp] theorem residual_source_eq_empty : (G.delete X).source = ∅ := by
  rw [vertexSet_targetFamily]
  ext x
  cases x <;> simp [G, RegularRightBoundary.BranchingStage.web]

/-- The empty residual family is a wave because deleting the selected
carrier deletes the unique source. -/
def residualWave : (G.delete X).Wave := by
  refine ⟨∅, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact hp.elim
  · intro x hx
    obtain ⟨p, hp, _⟩ := hx
    exact hp.elim
  · rw [residual_source_eq_empty]
    exact Set.empty_subset _

/-- Since every residual wave has empty family, the displayed residual wave
is forward-extension maximal. -/
theorem residualWave_isMax : IsMax residualWave := by
  intro W _hresidualW
  have hWempty : W.1 = ∅ := by
    ext p
    constructor
    · intro hp
      have hpInitial : p.initial ∈ (G.delete X).initialSet W.1 :=
        ⟨p, hp, rfl⟩
      have hpSource := W.2.2.1 hpInitial
      rw [residual_source_eq_empty] at hpSource
      exact hpSource.elim
    · intro hp
      exact hp.elim
  have hWeq : W = residualWave := Subtype.ext hWempty
  subst W
  exact le_rfl

/-- No quotient edge can enter the commitment set.  Hence a quotient walk
which finishes in that set must already have started there. -/
private theorem quotientWalk_start_eq_finish_of_finish_mem
    (K : DWeb RegularRightBoundary.BranchingStage.Vertex)
    (Q : Set RegularRightBoundary.BranchingStage.Vertex)
    {x y : RegularRightBoundary.BranchingStage.Vertex}
    (p : Walk (K.quotient Q).graph x y) (hy : y ∈ Q) : x = y := by
  induction p with
  | nil => rfl
  | @cons x z y h p ih =>
      have hzy : z = y := ih hy
      subst z
      exact False.elim (h.2.2.2 hy)

/-- A simple walk with equal endpoints has singleton support. -/
private theorem walk_support_eq_singleton_of_endpoints_eq
    {D : Digraph RegularRightBoundary.BranchingStage.Vertex}
    {x y : RegularRightBoundary.BranchingStage.Vertex}
    (p : Walk D x y) (hp : p.IsPath) (h : x = y) :
    p.support = [x] := by
  induction p with
  | nil => rfl
  | @cons x z y e q ih =>
      have hxq : x ∉ q.support := (List.nodup_cons.mp hp).1
      exact False.elim (hxq (h ▸ q.end_mem_support))

/-- A finite simple path with equal endpoints has singleton support. -/
private theorem finitePath_support_eq_singleton_of_start_eq_finish
    {D : Digraph RegularRightBoundary.BranchingStage.Vertex}
    (p : FinitePath D) (h : p.start = p.finish) :
    p.support = {p.start} := by
  have hwalk : p.walk.support = [p.start] :=
    walk_support_eq_singleton_of_endpoints_eq p.walk p.isPath h
  apply Set.Subset.antisymm
  · intro x hx
    change x ∈ p.walk.support at hx
    rw [hwalk] at hx
    simpa using hx
  · intro x hx
    have hxstart : x = p.start := by simpa using hx
    subst x
    exact p.start_mem_support

/-- The target endpoint `b` is a source of the quotient by `{b}`. -/
theorem b_mem_quotient_source : b ∈ (G.quotient {b}).source := by
  change b ∈ G.essential (G.source ∪ {b})
  exact target_mem_essential (by simp [G, RegularRightBoundary.BranchingStage.web])
    (by simp)

/-- Every quotient wave contains a member supported only at `b`. -/
theorem exists_quotientWave_member_support_eq_b
    (W : (G.quotient {b}).Wave) :
    ∃ q ∈ W.1, q.support = {b} := by
  let t : FinitePath (G.quotient {b}).graph :=
    FinitePath.trivial (G.quotient {b}).graph b
  obtain ⟨x, hxt, hxfrontier⟩ := W.2.2.2 b_mem_quotient_source t
    ⟨rfl, show b ∈ G.target by
      simp [G, RegularRightBoundary.BranchingStage.web]⟩
  have hxb : x = b := by simpa [t] using hxt
  subst x
  obtain ⟨q, hqW, hqterminal⟩ := hxfrontier
  refine ⟨q, hqW, ?_⟩
  rcases q with q | r
  · have hfinish : q.finish = b := by simpa using hqterminal
    have hstart : q.start = q.finish := by
      exact quotientWalk_start_eq_finish_of_finish_mem G {b} q.walk
        (by rw [hfinish]; exact Set.mem_singleton b)
    have hstartb : q.start = b := hstart.trans hfinish
    change q.support = {b}
    simpa only [hstartb] using
      finitePath_support_eq_singleton_of_start_eq_finish q hstart
  · simp at hqterminal

/-- Equality-transported form used for the actual non-source carrier. -/
theorem exists_quotientWave_member_support_eq_b_of_eq
    {Q : Set RegularRightBoundary.BranchingStage.Vertex}
    (hQ : Q = {b}) (W : (G.quotient Q).Wave) :
    ∃ q ∈ W.1, q.support = {b} := by
  subst Q
  exact exists_quotientWave_member_support_eq_b W

/-- The source/non-source arrow condition is false even though the selected
edge is safely deletable. -/
theorem safeTargetPath_not_nonSourceArrowExchange :
    G.IsSafeTargetPath u RegularRightBoundary.BranchingStage.ub ∧
      ¬ NonSourceArrowExchange G X := by
  refine ⟨?_, ?_⟩
  · refine ⟨rfl, by simp [G, RegularRightBoundary.BranchingStage.web,
      RegularRightBoundary.BranchingStage.ub], ?_⟩
    have hsupport : RegularRightBoundary.BranchingStage.ub.support = X := by
      rw [RegularRightBoundary.BranchingStage.ub_support, vertexSet_targetFamily]
    have hsafe : (G.delete X).IsUnhindered := by
      intro hhindered
      obtain ⟨W, hW, hne⟩ := hhindered
      apply hne
      exact Set.Subset.antisymm hW.2.1 (by
        intro x hx
        rw [residual_source_eq_empty] at hx
        exact hx.elim)
    exact hsupport.symm ▸ hsafe
  intro hexchange
  obtain ⟨W, hmeet⟩ := hexchange residualWave residualWave_isMax
  have hQ : X \ G.source = {b} := nonSourceCarrier_eq
  obtain ⟨q, hqW, hqsupport⟩ :=
    exists_quotientWave_member_support_eq_b_of_eq hQ W
  obtain ⟨z, hzq, hzoutside, _hzroof⟩ := hmeet q hqW
  rw [hqsupport] at hzq
  apply hzoutside
  rw [hQ]
  simpa using hzq

#print axioms safeTargetPath_not_nonSourceArrowExchange

end SingularNonSourceArrowCounterexample
end CardinalInduction
end Erdos599
