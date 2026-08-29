/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedRouteCore
import ErdosProblems.Erdos599.GroundingRelaxedEscape

/-!
# Representation-independent finite-source duplicate exchange

This file isolates the part of the finite-source exchange which depends only
on a `PopularAuxiliary.Input`.  In particular it does not import the legacy
ordinary-ladder wrapper whose former `groundedRecords` field is no longer a
part of `Input`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingFiniteSourceDuplicateExchangeCore

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

theorem CE_diff_singleton_old
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :
    GroundingCut.CE L (C \ {(.old x : LV L)}) = GroundingCut.CE L C := by
  ext e
  simp

theorem fragments_diff_singleton_old
    (L : Input Gamma I) (C : Set (LV L)) (x : V) :
    GroundingCut.fragments L (C \ {(.old x : LV L)}) =
      GroundingCut.fragments L C := by
  have hCE := CE_diff_singleton_old L C x
  ext P
  simp only [GroundingCut.fragments, Set.mem_setOf_eq,
    GroundingCut.IsDeletedFragment, GroundingCut.SurvivingConnected, hCE]

private def relaxedEscape_mono
    (L : Input Gamma I) {C D : Set (LV L)} {x : V}
    (hDC : D ⊆ C) (E : L.RelaxedEscape C x) :
    L.RelaxedEscape D x :=
  { route := E.route
    start_eq := E.start_eq
    target := E.target
    avoids := E.avoids.mono_right hDC
    old_not_mem := fun hxD => E.old_not_mem (hDC hxD) }

theorem exists_private_reverse_to_relaxedEscape
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {b x : V} (hbx : GroundingCut.Before P.path b x)
    (hxC : (.old x : LV L) ∈ C)
    (E : L.RelaxedEscape C b) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old x ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r (C \ {(.old x : LV L)}) ∧
        r.support ∩ C = {(.old x : LV L)} := by
  let D : Set (LV L) := C \ {(.old x : LV L)}
  have hP' : P ∈ GroundingCut.fragments L D := by
    simpa only [D, fragments_diff_singleton_old L C x] using hP
  have hxNotD : (.old x : LV L) ∉ D := by
    intro hxD
    exact hxD.2 rfl
  let E' : L.RelaxedEscape D b :=
    relaxedEscape_mono L Set.diff_subset E
  obtain ⟨r, hrStart, hrTarget, hrAvoid⟩ :=
    GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
      L D P hP' hbx hxNotD E'
  refine ⟨r, hrStart, hrTarget, hrAvoid, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    have hzEq : z = (.old x : LV L) := by
      by_contra hne
      exact Set.disjoint_left.1 hrAvoid hz.1 ⟨hz.2, hne⟩
    simpa only [Set.mem_singleton_iff] using hzEq
  · intro z hz
    have hzEq : z = (.old x : LV L) := by
      simpa only [Set.mem_singleton_iff] using hz
    subst z
    exact ⟨hrStart ▸ r.start_mem_support, hxC⟩

theorem exists_private_path_of_blockingPoint_ne_terminal
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {c : V} (hcTerminal : P.path.terminal? = some c)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (hcC : (.old c : LV L) ∈ C)
    (hne : GroundingCut.blockingPoint L C P ≠ c) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old c ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r (C \ {(.old c : LV L)}) ∧
        r.support ∩ C = {(.old c : LV L)} := by
  let b := GroundingCut.blockingPoint L C P
  have hbSupport : b ∈ P.path.support :=
    GroundingCut.blockingPoint_mem_support L C P
      (Or.inl hescape)
  have hbcEq : GroundingCut.BeforeEq P.path b c :=
    GroundingCut.beforeEq_terminal hcTerminal hbSupport
  have hbc : GroundingCut.Before P.path b c := ⟨hbcEq, hne⟩
  have hbEscape : b ∈ L.escapeRegion C :=
    GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      L C P hescape
  obtain ⟨E⟩ := hbEscape
  exact exists_private_reverse_to_relaxedEscape L C P hP hbc hcC E

theorem erasedCompression_terminal_not_forward_source
    {J : Type u} {L : Input Gamma J}
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p) {z : V} :
    (T.terminal, z) ∉
      T.erasedCompression.path.directionEdges .forward := by
  intro hz
  let E := T.runs.erasedSignedRoute
  have hvalid : ∀ {s : PopularAuxiliary.Input.SignedEdge V},
      s ∈ E.steps →
      PopularAuxiliary.Input.SignedEdge.Valid (Gamma := Gamma) s :=
    fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs)
  obtain ⟨s, hs, hsForward, hsEdge⟩ :=
    E.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      hvalid .forward hz
  obtain ⟨n, rfl⟩ := List.get_of_mem hs
  have hnForward : (E.steps.get n).direction = .forward := hsForward
  have hnEdge : (E.steps.get n).edge = (T.terminal, z) := hsEdge
  have hsource : E.routeVertex n = T.terminal := by
    have hroute := E.step_edge_eq_routeVertices_forward n hnForward
    exact (congrArg Prod.fst (hnEdge.symm.trans hroute)).symm
  have hrouteEq : E.routeVertex n = E.routeVertex E.steps.length :=
    hsource.trans E.routeVertex_last.symm
  have hnChain : n.1 < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  have hlastChain : E.steps.length < E.vertexChain.length := by
    rw [E.vertexChain_length]
    omega
  have hget :
      E.vertexChain.get ⟨n.1, hnChain⟩ =
        E.vertexChain.get ⟨E.steps.length, hlastChain⟩ := by
    unfold PopularAuxiliary.Input.ErasedSignedRoute.routeVertex at hrouteEq
    rw [List.getD_eq_get E.vertexChain T.terminal ⟨n.1, hnChain⟩,
      List.getD_eq_get E.vertexChain T.terminal
        ⟨E.steps.length, hlastChain⟩] at hrouteEq
    exact hrouteEq
  have hindex :
      (⟨n.1, hnChain⟩ : Fin E.vertexChain.length) =
        ⟨E.steps.length, hlastChain⟩ :=
    E.vertexChain_nodup.get_inj_iff.mp hget
  have : n.1 = E.steps.length := congrArg Fin.val hindex
  omega

/-- The private path has a canonical loop-erased alternating decode. -/
theorem exists_private_decoded_exchange_of_finiteSource_duplicate
    {J : Type u} (L : Input Gamma J) (C : Set (LV L))
    (P : L.Fragment) (hP : P ∈ GroundingCut.fragments L C)
    {c : V} (hcTerminal : P.path.terminal? = some c)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (hcFinite : c ∈ L.finiteSource)
    (hcCV : c ∈ GroundingCut.CV L C)
    (hne : GroundingCut.blockingPoint L C P ≠ c) :
    ∃ (q : FinitePath L.lambda.graph)
        (A : Alternating.AltPath Gamma.graph) (y : V),
      q.start = .old c ∧ q.finish ∈ L.lambda.target ∧
        L.lambda.Avoids q (C \ {(.old c : LV L)}) ∧
        q.support ∩ C = {(.old c : LV L)} ∧
        q.support ∩ L.lambda.target ⊆ {q.finish} ∧
        A.initial = c ∧ A.terminal? = some y ∧
        y ∈ L.targetMarkers ∧
        (∀ z, (y, z) ∉ A.directionEdges .forward) ∧
        Alternating.BackwardLinksOn L.ladder.paths A := by
  obtain ⟨q, hqStart, hqTarget, hqAvoid, hqPrivate⟩ :=
    exists_private_path_of_blockingPoint_ne_terminal
      L C P hP hcTerminal hescape (GroundingCut.mem_CV.mp hcCV) hne
  let hmeet : q.walk.Meets L.lambda.target :=
    ⟨q.finish, q.finish_mem_support, hqTarget⟩
  let q0 := q.firstHit L.lambda.target hmeet
  have hq0Start : q0.start = .old c := hqStart
  have hq0Target : q0.finish ∈ L.lambda.target :=
    q.firstHit_finish_mem L.lambda.target hmeet
  have hq0Subset : q0.support ⊆ q.support :=
    q.firstHit_support_subset L.lambda.target hmeet
  have hq0Avoid : L.lambda.Avoids q0 (C \ {(.old c : LV L)}) :=
    hqAvoid.mono hq0Subset Set.Subset.rfl
  have hq0Private : q0.support ∩ C = {(.old c : LV L)} := by
    apply Set.Subset.antisymm
    · intro z hz
      exact hqPrivate ▸ ⟨hq0Subset hz.1, hz.2⟩
    · intro z hz
      have hzc : z = (.old c : LV L) := by simpa using hz
      subst z
      exact ⟨hq0Start ▸ q0.start_mem_support,
        GroundingCut.mem_CV.mp hcCV⟩
  have hq0Pure : q0.support ∩ L.lambda.target ⊆ {q0.finish} := by
    intro z hz
    apply Set.mem_singleton_iff.2
    by_contra hzf
    have hzlast : z ≠ q0.walk.support.getLast q0.walk.support_ne_nil := by
      intro h
      apply hzf
      exact h.trans q0.walk.getLast_support
    have hzdrop : z ∈ q0.walk.support.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hz.1 hzlast
    exact (q.firstHit_no_mem_before L.lambda.target hmeet hzdrop) hz.2
  have hqSource : q0.start ∈ L.lambda.source := by
    rw [hq0Start, L.mem_lambda_source_old]
    exact hcFinite
  let T := L.decodeFinitePath q0 hqSource hq0Target
  let A := T.erasedCompression.path
  have hTInitial : T.initial = c := by
    classical
    simp only [T]
    unfold PopularAuxiliary.Input.decodeFinitePath
    split
    · rename_i x hx
      exact PopularAuxiliary.Input.LambdaVertex.old.inj
        (x.2.2.symm.trans hq0Start)
    · rename_i i hi
      exact False.elim (by
        have hproxy :
            (PopularAuxiliary.Input.LambdaVertex.proxy i.1 : LV L) =
              .old c := i.2.symm.trans hq0Start
        cases hproxy)
  have hback : Alternating.BackwardLinksOn L.ladder.paths A := by
    apply T.runs.erasedSignedRoute.compressionOfValid_backwardLinksOn
      (fun {_s} hs ↦ T.valid _
        (T.runs.erasedSignedRoute.steps_sublist.subset hs))
      L.ladder.disjoint
    intro s hs hdir
    simpa [PopularAuxiliary.Input.familyEdges,
      Alternating.familyEdges] using
      T.backward_on_ladder s
        (T.runs.erasedSignedRoute.steps_sublist.subset hs) hdir
  refine ⟨q0, A, T.terminal, hq0Start, hq0Target, hq0Avoid,
    hq0Private, hq0Pure, ?_, ?_, T.target_endpoint, ?_, hback⟩
  · exact T.erasedCompression.initial_eq.trans hTInitial
  · exact T.erasedCompression.terminal_eq
  · intro z
    exact erasedCompression_terminal_not_forward_source T

end GroundingFiniteSourceDuplicateExchangeCore
end Erdos599

#print axioms
  Erdos599.GroundingFiniteSourceDuplicateExchangeCore.exists_private_decoded_exchange_of_finiteSource_duplicate
