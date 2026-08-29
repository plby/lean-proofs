/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeWeakContinuation
import ErdosProblems.Erdos599.BlueprintImaginaryEdgeSubdivision

/-!
# Actual native weak-edge subdivision

The generic ordered finite/ray subdivision is applied to the unique member
of an arbitrary warp containing the represented edge. The native hammock
selection provides the fresh real path. The resulting warp has exact edge,
vertex, initial, and terminal identities, with no legacy hammock coercion.
-/

noncomputable section

namespace Erdos599.DWeb

open Set Cardinal Order _root_.Erdos599.DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Replace one represented edge by an actual finite path whose interior
misses the entire old warp. Finite and ray owners use the same ordered split. -/
theorem IsWarp.exists_edgeSubdivision_with_rayTrace
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {s t : V}
    (hedge : (s, t) ∈ familyEdges W)
    (p : FinitePath Gamma.graph) (hps : p.start = s) (hpt : p.finish = t)
    (hfresh : Gamma.vertexSet W ∩ p.support ⊆ {s, t}) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      Gamma.initialSet U = Gamma.initialSet W ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier W ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ p.support ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ p.edgeSet ∧
      ∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          r0.edgeSet \ {(s, t)} ⊆ r.edgeSet := by
  obtain ⟨q, hq, heq⟩ := Set.mem_iUnion.mp hedge |>.imp fun _ h ↦ Set.mem_iUnion.mp h
  have hqfresh : q.support ∩ p.support ⊆ {s, t} :=
    fun _ hx ↦ hfresh ⟨⟨q, hq, hx.1⟩, hx.2⟩
  let q' := Path.subdivide (q.edgeSplit heq) p hps hpt hqfresh
  let U : Set Gamma.DPath := insert q' (W \ {q})
  have hqI : q'.initial = q.initial := Path.subdivide_initial _ _ _ _ _
  have hqT : q'.terminal? = q.terminal? := Path.subdivide_terminal? _ _ _ _ _
  have hqV : q'.support = q.support ∪ p.support := Path.subdivide_support _ _ _ _ _
  have hqE : q'.edgeSet = (q.edgeSet \ {(s, t)}) ∪ p.edgeSet :=
    Path.subdivide_edgeSet _ _ _ _ _
  have hrest : ∀ r ∈ W \ {q}, Disjoint r.support p.support := by
    intro r hr
    apply Set.disjoint_left.mpr
    intro x hxr hxp
    have hx := hfresh ⟨⟨r, hr.1, hxr⟩, hxp⟩
    have hne : r ≠ q := by simpa only [Set.mem_singleton_iff] using hr.2
    have hdisj := hW hr.1 hq hne
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact Set.disjoint_left.mp hdisj hxr (q.edgeSet_subset_support_prod heq).1
    · have hxt : x = t := Set.mem_singleton_iff.mp hx
      exact Set.disjoint_left.mp hdisj hxr (hxt.symm ▸ (q.edgeSet_subset_support_prod heq).2)
  have hU : Gamma.IsWarp U := by
    intro r hr v hv hrv
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · rcases Set.mem_insert_iff.mp hv with rfl | hv
      · exact False.elim (hrv rfl)
      · change Disjoint q'.support v.support
        rw [hqV, Set.disjoint_union_left]
        exact ⟨hW hq hv.1 (fun he ↦ hv.2 (Set.mem_singleton_iff.mpr he.symm)),
          (hrest v hv).symm⟩
    · rcases Set.mem_insert_iff.mp hv with rfl | hv
      · change Disjoint r.support q'.support
        rw [hqV, Set.disjoint_union_right]
        exact ⟨hW hr.1 hq (fun he ↦ hr.2 (Set.mem_singleton_iff.mpr he)), hrest r hr⟩
      · exact hW hr.1 hv.1 hrv
  have hUI : Gamma.initialSet U = Gamma.initialSet W := by
    ext x
    constructor
    · rintro ⟨r, hr, hrx⟩
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · exact ⟨q, hq, hqI.symm.trans hrx⟩
      · exact ⟨r, hr.1, hrx⟩
    · rintro ⟨r, hr, hrx⟩
      by_cases hrq : r = q
      · subst r
        exact ⟨q', Set.mem_insert _ _, hqI.trans hrx⟩
      · exact ⟨r, Set.mem_insert_of_mem _ ⟨hr, hrq⟩, hrx⟩
  have hUT : Gamma.terminalFrontier U = Gamma.terminalFrontier W := by
    ext x
    constructor
    · rintro ⟨r, hr, hrx⟩
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · exact ⟨q, hq, hqT.symm.trans hrx⟩
      · exact ⟨r, hr.1, hrx⟩
    · rintro ⟨r, hr, hrx⟩
      by_cases hrq : r = q
      · subst r
        exact ⟨q', Set.mem_insert _ _, hqT.trans hrx⟩
      · exact ⟨r, Set.mem_insert_of_mem _ ⟨hr, hrq⟩, hrx⟩
  have hUV : Gamma.vertexSet U = Gamma.vertexSet W ∪ p.support := by
    ext x
    constructor
    · rintro ⟨r, hr, hxr⟩
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · rw [hqV] at hxr
        exact hxr.elim (fun hx ↦ Or.inl ⟨q, hq, hx⟩) Or.inr
      · exact Or.inl ⟨r, hr.1, hxr⟩
    · rintro (⟨r, hr, hxr⟩ | hxp)
      · by_cases hrq : r = q
        · subst r
          exact ⟨q', Set.mem_insert _ _, hqV.symm ▸ Or.inl hxr⟩
        · exact ⟨r, Set.mem_insert_of_mem _ ⟨hr, hrq⟩, hxr⟩
      · exact ⟨q', Set.mem_insert _ _, hqV.symm ▸ Or.inr hxp⟩
  have hUE : familyEdges U = (familyEdges W \ {(s, t)}) ∪ p.edgeSet := by
    ext e
    simp only [familyEdges, Set.mem_iUnion, Set.mem_union, Set.mem_sdiff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨r, hr, her⟩
      rcases Set.mem_insert_iff.mp hr with rfl | hr
      · rw [hqE] at her
        exact her.elim (fun he ↦ Or.inl ⟨⟨q, hq, he.1⟩, he.2⟩) Or.inr
      · left
        refine ⟨⟨r, hr.1, her⟩, ?_⟩
        rintro rfl
        have hrq := DWeb.IsWarp.eq_of_mem_support hW hr.1 hq
          (r.edgeSet_subset_support_prod her).1 (q.edgeSet_subset_support_prod heq).1
        exact hr.2 (Set.mem_singleton_iff.mpr hrq)
    · rintro (⟨⟨r, hr, her⟩, hene⟩ | hep)
      · by_cases hrq : r = q
        · subst r
          refine ⟨q', Set.mem_insert _ _, ?_⟩
          rw [hqE]
          exact Or.inl ⟨her, hene⟩
        · exact ⟨r, Set.mem_insert_of_mem _ ⟨hr, hrq⟩, her⟩
      · refine ⟨q', Set.mem_insert _ _, ?_⟩
        rw [hqE]
        exact Or.inr hep
  refine ⟨U, hU, hUI, hUT, hUV, hUE, ?_⟩
  intro r hr
  rcases Set.mem_insert_iff.mp hr with hr | hr
  · have hnone : q.terminal? = none := by
      rw [← hqT, ← hr]
      rfl
    rcases q with qf | r0
    · simp [Path.terminal?] at hnone
    · refine ⟨r0, hq, ?_⟩
      intro e he
      have heq' : e ∈ q'.edgeSet := by
        rw [hqE]
        exact Or.inl he
      simpa only [← hr, Path.edgeSet_ray] using heq'
  · exact ⟨r, hr.1, fun _ he ↦ he.1⟩

/-- The boundary and carrier interface of actual one-edge subdivision. -/
theorem IsWarp.exists_edgeSubdivision
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W) {s t : V}
    (hedge : (s, t) ∈ familyEdges W)
    (p : FinitePath Gamma.graph) (hps : p.start = s) (hpt : p.finish = t)
    (hfresh : Gamma.vertexSet W ∩ p.support ⊆ {s, t}) :
    ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧
      Gamma.initialSet U = Gamma.initialSet W ∧
      Gamma.terminalFrontier U = Gamma.terminalFrontier W ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ p.support ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ p.edgeSet := by
  obtain ⟨U, hU, hUI, hUT, hUV, hUE, _htrace⟩ :=
    hW.exists_edgeSubdivision_with_rayTrace hedge p hps hpt hfresh
  exact ⟨U, hU, hUI, hUT, hUV, hUE⟩

#print axioms IsWarp.exists_edgeSubdivision
#print axioms IsWarp.exists_edgeSubdivision_with_rayTrace

end Erdos599.DWeb

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating Ladder
open ColouredSafeAmbientOccurrence ColouredSafeHammock

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

/-- The native augmentation with the unchanged distinguished vertex sets. -/
def imaginaryWeb (Y : Set Gamma.DPath) (kappa : Cardinal.{u}) : DWeb V where
  graph := imaginaryGraph Y kappa
  source := Gamma.source
  target := Gamma.target

/-- One weak edge in a small roofed native warp is actually replaced by a
fresh finite real path. The old sources and finite terminals are unchanged. -/
theorem exists_weakEdgeSubdivision
    (C : LinkageBlueprint.ClubStageGeometry Gamma Y kappa (succ kappa))
    {a : Stage (succ kappa)}
    {W : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath}
    (hW : (imaginaryWeb C.ladder.limitWarp kappa).IsWarp W)
    (hWcard : #((imaginaryWeb C.ladder.limitWarp kappa).vertexSet W) ≤ kappa)
    (hWRoof : (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ⊆
      Gamma.roof (C.ladder.frontier a))
    {s t : V} (hedge : (s, t) ∈ familyEdges W)
    {extra : Occurrence C.ladder.limitWarp s → Prop}
    (h : HasCard C.ladder.limitWarp s (some t) extra (succ kappa))
    (hroof : ∀ A, extra A → A.vertexSet ⊆ Gamma.roof (C.ladder.frontier a))
    (hnot : ¬HasCard C.ladder.limitWarp s (some t)
      (fun A ↦ extra A ∧ ¬A.HasFiniteSwitchedPathTo t) (succ kappa)) :
    ∃ (p : FinitePath Gamma.graph)
      (U : Set (imaginaryWeb C.ladder.limitWarp kappa).DPath),
      p.start = s ∧ p.finish = t ∧
      (imaginaryWeb C.ladder.limitWarp kappa).IsWarp U ∧
      (imaginaryWeb C.ladder.limitWarp kappa).initialSet U =
        (imaginaryWeb C.ladder.limitWarp kappa).initialSet W ∧
      (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier U =
        (imaginaryWeb C.ladder.limitWarp kappa).terminalFrontier W ∧
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U =
        (imaginaryWeb C.ladder.limitWarp kappa).vertexSet W ∪ p.support ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ p.edgeSet ∧
      #((imaginaryWeb C.ladder.limitWarp kappa).vertexSet U) ≤ kappa ∧
      (imaginaryWeb C.ladder.limitWarp kappa).vertexSet U ⊆
        Gamma.roof (C.ladder.frontier a) := by
  let D := imaginaryWeb C.ladder.limitWarp kappa
  obtain ⟨_A, p, _hA, hps, hpt, _hpE, hpAvoid, hpRoof⟩ :=
    C.native_global_weak_hasCard_exists_path_avoiding h hroof hnot hWcard
  let p' : FinitePath D.graph := p.lift (fun he ↦ Or.inl he)
  have hpV : p'.support = p.support := FinitePath.support_lift _ p
  have hpE : p'.edgeSet = p.edgeSet :=
    LinkageBlueprint.walk_edgeSet_lift _ p.walk
  have hfresh : D.vertexSet W ∩ p'.support ⊆ {s, t} := by
    intro x hx
    exact hpAvoid ⟨hpV ▸ hx.2, hx.1⟩
  obtain ⟨U, hU, hUI, hUT, hUV, hUE⟩ :=
    hW.exists_edgeSubdivision hedge p' hps hpt hfresh
  rw [hpV] at hUV
  rw [hpE] at hUE
  refine ⟨p, U, hps, hpt, hU, hUI, hUT, hUV, hUE, ?_, ?_⟩
  · rw [hUV]
    exact (Cardinal.mk_union_le _ _).trans
      (Cardinal.add_le_of_le C.capacity_infinite hWcard
        (p.support_finite.countable.le_aleph0.trans C.capacity_infinite))
  · rw [hUV]
    exact Set.union_subset hWRoof hpRoof

#print axioms exists_weakEdgeSubdivision

end Erdos599.Blueprint.ColouredSafeShortcutGraph
