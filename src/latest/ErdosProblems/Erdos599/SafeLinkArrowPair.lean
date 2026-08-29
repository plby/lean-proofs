/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CommonQuotient
import ErdosProblems.Erdos599.SafeSwitchingAssembly

/-!
# Pair provenance through accumulated arrows

This file records the generic support-cofinality calculus used by the
Section 6 closing construction.  It is independent of the particular
dependent recurrence: if consecutive input waves support-contain one
another, every finite accumulated-arrow path is support-contained in one
path of the newest input wave.  Consequently two marked vertices on a
countable up-arrow path occur together in a sufficiently late input wave.

The final theorem supplies the component-level criterion used by the full
Definition 2.29 quotient.  Inclusion of both the vertex set and directed
edge union forces every old finite or ray component into a single component
of the new warp.
-/

noncomputable section

namespace Erdos599

open Set DirectedPath
open Alternating

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- Every member of `U` is support-contained in one member of `W`. -/
def SupportCofinal (U W : Set G.DPath) : Prop :=
  ∀ p ∈ U, ∃ q ∈ W, p.support ⊆ q.support

theorem supportCofinal_refl (U : Set G.DPath) : G.SupportCofinal U U := by
  intro p hp
  exact ⟨p, hp, Subset.rfl⟩

theorem SupportCofinal.trans {U W Z : Set G.DPath}
    (hUW : G.SupportCofinal U W) (hWZ : G.SupportCofinal W Z) :
    G.SupportCofinal U Z := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hUW p hp
  obtain ⟨r, hr, hqr⟩ := hWZ q hq
  exact ⟨r, hr, hpq.trans hqr⟩

theorem SupportCofinal.of_forwardExtension {U W : Set G.DPath}
    (hUW : G.ForwardExtension U W) : G.SupportCofinal U W := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := hUW.1 p hp
  exact ⟨q, hq, G.support_mono_of_extends hpq⟩

/-- If the left paths are support-contained in right paths, their arrow
does not escape the right family at support level. -/
theorem supportCofinal_arrow_right {U W : Set G.DPath}
    (hW : G.IsWarp W) (hUW : G.SupportCofinal U W) :
    G.SupportCofinal (G.arrow U W) W := by
  intro r hr
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, hqW, hpq⟩ := hUW p.1 p.2
  rcases hp : p.1 with f | ray
  · have hf : (Sum.inl f : G.DPath) ∈ U := by simpa [hp] using p.2
    have peq : p = ⟨Sum.inl f, hf⟩ := Subtype.ext hp
    subst p
    rcases G.arrowPath_finite_cases U W f hf with harrow | ⟨c, harrow⟩
    · refine ⟨q, hqW, ?_⟩
      simpa [harrow] using hpq
    · have hfinishq : f.finish ∈ q.support :=
        hpq f.finish_mem_support
      have hcq : c.path = q := by
        by_contra hne
        exact Set.disjoint_left.1 (hW c.mem_path hqW hne)
          c.finish_mem hfinishq
      refine ⟨q, hqW, ?_⟩
      rw [harrow, DirectedPath.Path.support_appendAt]
      apply Set.union_subset
      · exact hpq
      · have hs := c.path.support_suffixFrom_subset f.finish c.finish_mem
        simpa only [hcq] using hs
  · have hray : (Sum.inr ray : G.DPath) ∈ U := by
      simpa [hp] using p.2
    have peq : p = ⟨Sum.inr ray, hray⟩ := Subtype.ext hp
    subst p
    refine ⟨q, hqW, ?_⟩
    simpa [G.arrowPath_ray U W ray hray] using hpq

/-- If successive input waves are support-cofinal, every finite accumulated
arrow stage is support-contained in its newest input wave. -/
theorem supportCofinal_omegaArrowStage_input
    (W : ℕ → G.Wave)
    (hstep : ∀ n, G.SupportCofinal (W n).1 (W (n + 1)).1) :
    ∀ n, G.SupportCofinal (G.omegaArrowStage W n).1 (W n).1
  | 0 => by
      simpa using G.supportCofinal_refl (W 0).1
  | n + 1 => by
      rw [G.omegaArrowStage_succ]
      apply G.supportCofinal_arrow_right (W (n + 1)).2.1
      exact SupportCofinal.trans G
        (supportCofinal_omegaArrowStage_input W hstep n) (hstep n)

/-- Both marked vertices of a final omega-arrow path occur together on one
actual input-wave path.  The input may be chosen after any prescribed
index. -/
theorem exists_later_input_path_containing_pair_of_supportCofinal
    (W : ℕ → G.Wave)
    (hstep : ∀ n, G.SupportCofinal (W n).1 (W (n + 1)).1)
    (k : ℕ) {q : G.DPath} (hq : q ∈ (G.omegaArrow W).1)
    {x y : V} (hxq : x ∈ q.support) (hyq : y ∈ q.support) :
    ∃ m, k ≤ m ∧ ∃ p ∈ (W m).1,
      x ∈ p.support ∧ y ∈ p.support := by
  obtain ⟨m, hkm, p, hpStage, hxp, hyp⟩ :=
    G.exists_later_omegaArrowStage_path_containing_pair W k hq hxq hyq
  obtain ⟨r, hrW, hpr⟩ :=
    supportCofinal_omegaArrowStage_input G W hstep m p hpStage
  exact ⟨m, hkm, r, hrW, hpr hxp, hpr hyp⟩

private theorem Walk.support_eq_singleton_of_isPath_of_endpoints_eq
    {D : Digraph V} {u v : V} (w : Walk D u v)
    (hw : w.IsPath) (h : u = v) : w.support = [u] := by
  induction w with
  | nil => rfl
  | @cons u v w e q ih =>
      have hn : u ∉ q.support := (List.nodup_cons.1 hw).1
      exact (hn (h ▸ q.end_mem_support)).elim

private theorem exists_warp_path_supporting_finitePath
    {W : Set G.DPath} (hW : G.IsWarp W)
    (r : FinitePath G.graph)
    (hstart : r.start ∈ G.vertexSet W)
    (hedges : r.edgeSet ⊆ familyEdges W) :
    ∃ p ∈ W, r.support ⊆ p.support := by
  by_cases hne : r.start = r.finish
  · obtain ⟨p, hpW, hstartp⟩ := hstart
    refine ⟨p, hpW, ?_⟩
    have hs : r.walk.support = [r.start] :=
      Walk.support_eq_singleton_of_isPath_of_endpoints_eq r.walk r.isPath hne
    intro z hzr
    change z ∈ r.walk.support at hzr
    rw [hs] at hzr
    have hz : z = r.start := by simpa using hzr
    simpa [hz] using hstartp
  · obtain ⟨p, hpW, hrp⟩ :=
      SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
        hW r hne hedges
    exact ⟨p, hpW, hrp.1⟩

/-- Vertex and directed-edge inclusion between two component warps forces
each old component to lie in a single new component. -/
theorem supportCofinal_of_vertexSet_familyEdges
    {U W : Set G.DPath} (hW : G.IsWarp W)
    (hvertices : G.vertexSet U ⊆ G.vertexSet W)
    (hedges : familyEdges U ⊆ familyEdges W) :
    G.SupportCofinal U W := by
  intro p hpU
  rcases p with f | r
  · apply G.exists_warp_path_supporting_finitePath hW f
    · apply hvertices
      exact ⟨Sum.inl f, hpU, f.start_mem_support⟩
    · intro e he
      apply hedges
      simp only [familyEdges, Set.mem_iUnion]
      exact ⟨Sum.inl f, hpU, he⟩
  · have hr0U : r 0 ∈ G.vertexSet U :=
      ⟨Sum.inr r, hpU, r.initial_mem_support⟩
    obtain ⟨q, hqW, hr0q⟩ := hvertices hr0U
    refine ⟨q, hqW, ?_⟩
    rintro x ⟨n, rfl⟩
    induction n with
    | zero => exact hr0q
    | succ n ih =>
        have hedgeU : (r n, r (n + 1)) ∈ familyEdges U := by
          simp only [familyEdges, Set.mem_iUnion]
          exact ⟨Sum.inr r, hpU, ⟨n, rfl⟩⟩
        have hedgeW : (r n, r (n + 1)) ∈ familyEdges W :=
          hedges hedgeU
        simp only [familyEdges, Set.mem_iUnion] at hedgeW
        obtain ⟨s, hsW, hrs⟩ := hedgeW
        have hrns : r n ∈ s.support :=
          (s.edgeSet_subset_support_prod hrs).1
        have hrnexts : r (n + 1) ∈ s.support :=
          (s.edgeSet_subset_support_prod hrs).2
        have hsq : s = q :=
          DWeb.IsWarp.eq_of_mem_support hW hsW hqW hrns ih
        exact hsq ▸ hrnexts

end DWeb
end Erdos599
