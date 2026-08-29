/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeStrongTwoPortSplice

/-!
# Attaching a finite switch warp at one old terminal

Replace the unique finite member of `W` ending at `s` and the unique member
of a finite-character warp `K` starting at `s` by their concatenation.  All
other members of both families are retained literally.  The sole geometric
hypothesis is `V[K] ∩ V[W] ⊆ {s}`; uniqueness and all remaining endpoint
exclusions follow from the two warp conditions.

Unlike the two-port splice, the removed old owner is finite.  Consequently
every old ray is retained literally, so the finite-loss ray trace uses the
empty lost-edge set.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeOnePortSplice

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact data for a one-port attachment. -/
structure Data (W K : Set Gamma.DPath) (s : V) where
  W_isWarp : Gamma.IsWarp W
  switch_isWarp : Gamma.IsWarp K
  switch_finiteCharacter : Gamma.HasFiniteCharacter K
  old : FinitePath Gamma.graph
  old_mem : (Sum.inl old : Gamma.DPath) ∈ W
  old_finish : old.finish = s
  sourcePath : FinitePath Gamma.graph
  source_mem : (Sum.inl sourcePath : Gamma.DPath) ∈ K
  source_start : sourcePath.start = s
  carrier_inter :
    Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V)

namespace Data

variable {W K : Set Gamma.DPath} {s : V} (D : Data W K s)

theorem old_inter_source_subset :
    D.old.support ∩ D.sourcePath.support ⊆ ({s} : Set V) := by
  intro x hx
  exact D.carrier_inter
    ⟨⟨Sum.inl D.sourcePath, D.source_mem, hx.2⟩,
      ⟨Sum.inl D.old, D.old_mem, hx.1⟩⟩

/-- The concatenated replacement member. -/
def joined : FinitePath Gamma.graph :=
  D.old.appendFinite D.sourcePath
    (D.source_start.trans D.old_finish.symm)
    (by simpa only [D.old_finish] using D.old_inter_source_subset)

@[simp] theorem joined_start : D.joined.start = D.old.start := by
  exact FinitePath.appendFinite_start _ _ _ _

@[simp] theorem joined_finish :
    D.joined.finish = D.sourcePath.finish := by
  exact FinitePath.appendFinite_finish _ _ _ _

@[simp] theorem joined_support :
    D.joined.support = D.old.support ∪ D.sourcePath.support := by
  exact D.old.support_appendFinite_eq_union D.sourcePath _ _

@[simp] theorem joined_edgeSet :
    D.joined.edgeSet = D.old.edgeSet ∪ D.sourcePath.edgeSet := by
  exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite _ _ _ _

def oldRemainder : Set Gamma.DPath := W \ {Sum.inl D.old}

def switchRemainder : Set Gamma.DPath := K \ {Sum.inl D.sourcePath}

/-- The full one-port attachment family. -/
def paths : Set Gamma.DPath :=
  insert (Sum.inl D.joined : Gamma.DPath)
    (D.oldRemainder ∪ D.switchRemainder)

theorem old_other_avoids_port {p : Gamma.DPath}
    (hp : p ∈ D.oldRemainder) : s ∉ p.support := by
  intro hs
  have hsOld : s ∈ D.old.support := by
    simpa only [D.old_finish] using D.old.finish_mem_support
  have hpo : p = Sum.inl D.old := by
    by_contra hne
    exact Set.disjoint_left.mp (D.W_isWarp hp.1 D.old_mem hne) hs hsOld
  exact hp.2 (Set.mem_singleton_iff.mpr hpo)

theorem switch_other_avoids_port {p : Gamma.DPath}
    (hp : p ∈ D.switchRemainder) : s ∉ p.support := by
  intro hs
  have hsSource : s ∈ D.sourcePath.support := by
    simpa only [D.source_start] using D.sourcePath.start_mem_support
  have hpSource : p = Sum.inl D.sourcePath := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.switch_isWarp hp.1 D.source_mem hne) hs hsSource
  exact hp.2 (Set.mem_singleton_iff.mpr hpSource)

theorem old_other_disjoint_switch {p q : Gamma.DPath}
    (hp : p ∈ D.oldRemainder) (hq : q ∈ D.switchRemainder) :
    Disjoint p.support q.support := by
  apply Set.disjoint_left.mpr
  intro x hxp hxq
  have hxs := D.carrier_inter
    ⟨⟨q, hq.1, hxq⟩, ⟨p, hp.1, hxp⟩⟩
  exact D.old_other_avoids_port hp
    (Set.mem_singleton_iff.mp hxs ▸ hxp)

theorem joined_disjoint_old_other {p : Gamma.DPath}
    (hp : p ∈ D.oldRemainder) : Disjoint D.joined.support p.support := by
  rw [D.joined_support, Set.disjoint_union_left]
  refine ⟨?_, ?_⟩
  · exact D.W_isWarp D.old_mem hp.1 (fun h ↦
      hp.2 (Set.mem_singleton_iff.mpr h.symm))
  · apply Set.disjoint_left.mpr
    intro x hxSource hxp
    have hxs := D.carrier_inter
      ⟨⟨Sum.inl D.sourcePath, D.source_mem, hxSource⟩,
        ⟨p, hp.1, hxp⟩⟩
    exact D.old_other_avoids_port hp
      (Set.mem_singleton_iff.mp hxs ▸ hxp)

theorem joined_disjoint_switch_other {p : Gamma.DPath}
    (hp : p ∈ D.switchRemainder) :
    Disjoint D.joined.support p.support := by
  rw [D.joined_support, Set.disjoint_union_left]
  refine ⟨?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxOld hxp
    have hxs := D.carrier_inter
      ⟨⟨p, hp.1, hxp⟩, ⟨Sum.inl D.old, D.old_mem, hxOld⟩⟩
    exact D.switch_other_avoids_port hp
      (Set.mem_singleton_iff.mp hxs ▸ hxp)
  · exact D.switch_isWarp D.source_mem hp.1 (fun h ↦
      hp.2 (Set.mem_singleton_iff.mpr h.symm))

private theorem remainder_isWarp :
    Gamma.IsWarp (D.oldRemainder ∪ D.switchRemainder) := by
  intro p hp q hq hpq
  rcases hp with hpOld | hpSwitch <;> rcases hq with hqOld | hqSwitch
  · exact D.W_isWarp hpOld.1 hqOld.1 hpq
  · exact D.old_other_disjoint_switch hpOld hqSwitch
  · exact (D.old_other_disjoint_switch hqOld hpSwitch).symm
  · exact D.switch_isWarp hpSwitch.1 hqSwitch.1 hpq

theorem paths_isWarp : Gamma.IsWarp D.paths := by
  apply DWeb.IsWarp.insert_finite_of_disjoint Gamma D.remainder_isWarp D.joined
  apply Set.disjoint_left.mpr
  intro x hxJoined hxRemainder
  obtain ⟨p, hp, hxp⟩ := hxRemainder
  rcases hp with hpOld | hpSwitch
  · exact Set.disjoint_left.mp (D.joined_disjoint_old_other hpOld)
      hxJoined hxp
  · exact Set.disjoint_left.mp (D.joined_disjoint_switch_other hpSwitch)
      hxJoined hxp

theorem joined_mem_paths :
    (Sum.inl D.joined : Gamma.DPath) ∈ D.paths := Set.mem_insert _ _

theorem oldRemainder_subset_paths : D.oldRemainder ⊆ D.paths := by
  intro p hp
  exact Set.mem_insert_of_mem _ (Or.inl hp)

theorem switchRemainder_subset_paths : D.switchRemainder ⊆ D.paths := by
  intro p hp
  exact Set.mem_insert_of_mem _ (Or.inr hp)

theorem vertexSet_paths :
    Gamma.vertexSet D.paths = Gamma.vertexSet W ∪ Gamma.vertexSet K := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hpRemainder
    · change x ∈ D.joined.support at hxp
      rw [D.joined_support] at hxp
      rcases hxp with hxOld | hxSource
      · exact Or.inl ⟨Sum.inl D.old, D.old_mem, hxOld⟩
      · exact Or.inr ⟨Sum.inl D.sourcePath, D.source_mem, hxSource⟩
    · rcases hpRemainder with hpOld | hpSwitch
      · exact Or.inl ⟨p, hpOld.1, hxp⟩
      · exact Or.inr ⟨p, hpSwitch.1, hxp⟩
  · rintro (hxW | hxK)
    · obtain ⟨p, hpW, hxp⟩ := hxW
      by_cases hpOld : p = Sum.inl D.old
      · subst p
        refine ⟨Sum.inl D.joined, D.joined_mem_paths, ?_⟩
        change x ∈ D.joined.support
        rw [D.joined_support]
        exact Or.inl hxp
      · exact ⟨p, D.oldRemainder_subset_paths
          ⟨hpW, by simpa only [Set.mem_singleton_iff] using hpOld⟩, hxp⟩
    · obtain ⟨p, hpK, hxp⟩ := hxK
      by_cases hpSource : p = Sum.inl D.sourcePath
      · subst p
        refine ⟨Sum.inl D.joined, D.joined_mem_paths, ?_⟩
        change x ∈ D.joined.support
        rw [D.joined_support]
        exact Or.inr hxp
      · exact ⟨p, D.switchRemainder_subset_paths
          ⟨hpK, by simpa only [Set.mem_singleton_iff] using hpSource⟩, hxp⟩

/-- Every old and switch edge survives the one-port attachment, and the
output has no other edges.  Isolated members require no special case. -/
theorem familyEdges_paths :
    familyEdges D.paths = familyEdges W ∪ familyEdges K := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨p, hp, hep⟩ := Set.mem_iUnion.mp he |>.imp fun _ h ↦
      Set.mem_iUnion.mp h
    rcases Set.mem_insert_iff.mp hp with rfl | hpRemainder
    · change e ∈ D.joined.edgeSet at hep
      rw [D.joined_edgeSet] at hep
      rcases hep with heOld | heSource
      · exact Or.inl (Set.mem_iUnion.mpr ⟨Sum.inl D.old,
          Set.mem_iUnion.mpr ⟨D.old_mem, heOld⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl D.sourcePath,
          Set.mem_iUnion.mpr ⟨D.source_mem, heSource⟩⟩)
    · rcases hpRemainder with hpOld | hpSwitch
      · exact Or.inl (Set.mem_iUnion.mpr ⟨p,
          Set.mem_iUnion.mpr ⟨hpOld.1, hep⟩⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨p,
          Set.mem_iUnion.mpr ⟨hpSwitch.1, hep⟩⟩)
  · rintro e (heW | heK)
    · obtain ⟨p, hpW, hep⟩ := Set.mem_iUnion.mp heW |>.imp fun _ h ↦
        Set.mem_iUnion.mp h
      by_cases hpOld : p = Sum.inl D.old
      · subst p
        apply Set.mem_iUnion.mpr
        refine ⟨Sum.inl D.joined, Set.mem_iUnion.mpr
          ⟨D.joined_mem_paths, ?_⟩⟩
        change e ∈ D.joined.edgeSet
        rw [D.joined_edgeSet]
        exact Or.inl hep
      · exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
          ⟨D.oldRemainder_subset_paths ⟨hpW, by
            simpa only [Set.mem_singleton_iff] using hpOld⟩, hep⟩⟩
    · obtain ⟨p, hpK, hep⟩ := Set.mem_iUnion.mp heK |>.imp fun _ h ↦
        Set.mem_iUnion.mp h
      by_cases hpSource : p = Sum.inl D.sourcePath
      · subst p
        apply Set.mem_iUnion.mpr
        refine ⟨Sum.inl D.joined, Set.mem_iUnion.mpr
          ⟨D.joined_mem_paths, ?_⟩⟩
        change e ∈ D.joined.edgeSet
        rw [D.joined_edgeSet]
        exact Or.inr hep
      · exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
          ⟨D.switchRemainder_subset_paths ⟨hpK, by
            simpa only [Set.mem_singleton_iff] using hpSource⟩, hep⟩⟩

theorem initialSet_paths :
    Gamma.initialSet D.paths =
      Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hpRemainder
    · left
      exact ⟨Sum.inl D.old, D.old_mem, D.joined_start.symm.trans hpx⟩
    · rcases hpRemainder with hpOld | hpSwitch
      · exact Or.inl ⟨p, hpOld.1, hpx⟩
      · right
        refine ⟨⟨p, hpSwitch.1, hpx⟩, ?_⟩
        intro hxs
        exact D.switch_other_avoids_port hpSwitch (by
          have hxInitial := Path.initial_mem_support p
          simpa only [hpx, Set.mem_singleton_iff.mp hxs] using hxInitial)
  · rintro (hxW | hxK)
    · obtain ⟨p, hpW, hpx⟩ := hxW
      by_cases hpOld : p = Sum.inl D.old
      · subst p
        exact ⟨Sum.inl D.joined, D.joined_mem_paths,
          D.joined_start.trans hpx⟩
      · exact ⟨p, D.oldRemainder_subset_paths
          ⟨hpW, by simpa only [Set.mem_singleton_iff] using hpOld⟩, hpx⟩
    · obtain ⟨⟨p, hpK, hpx⟩, hxne⟩ := hxK
      by_cases hpSource : p = Sum.inl D.sourcePath
      · subst p
        exfalso
        apply hxne
        apply Set.mem_singleton_iff.mpr
        exact hpx.symm.trans D.source_start
      · exact ⟨p, D.switchRemainder_subset_paths
          ⟨hpK, by simpa only [Set.mem_singleton_iff] using hpSource⟩, hpx⟩

theorem terminalFrontier_paths :
    Gamma.terminalFrontier D.paths =
      (Gamma.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier K := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hpRemainder
    · right
      change some D.joined.finish = some x at hpx
      have hxFinish : D.sourcePath.finish = x :=
        Option.some.inj (by simpa only [D.joined_finish] using hpx)
      exact ⟨Sum.inl D.sourcePath, D.source_mem, congrArg some hxFinish⟩
    · rcases hpRemainder with hpOld | hpSwitch
      · left
        refine ⟨⟨p, hpOld.1, hpx⟩, ?_⟩
        intro hxs
        exact D.old_other_avoids_port hpOld (by
          have hxTerminal := Gamma.terminal_mem_support hpx
          simpa only [Set.mem_singleton_iff.mp hxs] using hxTerminal)
      · exact Or.inr ⟨p, hpSwitch.1, hpx⟩
  · rintro (hxW | hxK)
    · obtain ⟨⟨p, hpW, hpx⟩, hxne⟩ := hxW
      by_cases hpOld : p = Sum.inl D.old
      · subst p
        exfalso
        apply hxne
        apply Set.mem_singleton_iff.mpr
        change some D.old.finish = some x at hpx
        exact (Option.some.inj hpx).symm.trans D.old_finish
      · exact ⟨p, D.oldRemainder_subset_paths
          ⟨hpW, by simpa only [Set.mem_singleton_iff] using hpOld⟩, hpx⟩
    · obtain ⟨p, hpK, hpx⟩ := hxK
      by_cases hpSource : p = Sum.inl D.sourcePath
      · subst p
        change some D.sourcePath.finish = some x at hpx
        refine ⟨Sum.inl D.joined, D.joined_mem_paths, ?_⟩
        change some D.joined.finish = some x
        simpa only [D.joined_finish] using hpx
      · exact ⟨p, D.switchRemainder_subset_paths
          ⟨hpK, by simpa only [Set.mem_singleton_iff] using hpSource⟩, hpx⟩

/-- The displayed real source component survives as the terminal part of
the joined path, hence all its edges belong to the output relation. -/
theorem sourcePath_edgeSet_subset_familyEdges :
    D.sourcePath.edgeSet ⊆ familyEdges D.paths := by
  intro e he
  apply Set.mem_iUnion.mpr
  refine ⟨Sum.inl D.joined, Set.mem_iUnion.mpr ⟨D.joined_mem_paths, ?_⟩⟩
  change e ∈ D.joined.edgeSet
  rw [D.joined_edgeSet]
  exact Or.inr he

/-- Every output ray is literally an old ray; the finite switch family and
the joined replacement contribute no rays. -/
theorem ray_mem_old :
    ∀ r : Ray Gamma.graph, Sum.inr r ∈ D.paths → Sum.inr r ∈ W := by
  intro r hr
  rcases Set.mem_insert_iff.mp hr with hjoined | hrRemainder
  · cases hjoined
  · rcases hrRemainder with hrOld | hrSwitch
    · exact hrOld.1
    · obtain ⟨p, hp⟩ := D.switch_finiteCharacter hrSwitch.1
      cases hp

theorem finite_rayTrace :
    ∀ r : Ray Gamma.graph, Sum.inr r ∈ D.paths →
      ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
        ∃ lost : Set (V × V), lost.Finite ∧
          r0.edgeSet \ lost ⊆ r.edgeSet := by
  intro r hr
  exact ⟨r, D.ray_mem_old r hr, ∅, Set.finite_empty, by simp⟩

theorem paths_finiteCharacter (hWfinite : Gamma.HasFiniteCharacter W) :
    Gamma.HasFiniteCharacter D.paths := by
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hpRemainder
  · exact ⟨D.joined, rfl⟩
  · rcases hpRemainder with hpOld | hpSwitch
    · exact hWfinite hpOld.1
    · exact D.switch_finiteCharacter hpSwitch.1

#print axioms Data.paths_isWarp
#print axioms Data.vertexSet_paths
#print axioms Data.familyEdges_paths
#print axioms Data.initialSet_paths
#print axioms Data.terminalFrontier_paths
#print axioms Data.sourcePath_edgeSet_subset_familyEdges
#print axioms Data.finite_rayTrace

end Data

/-- Package the explicit real switch component together with the unique
finite old member ending at `s`. -/
theorem exists_data_of_port_with_path
    {W K : Set Gamma.DPath} {s : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hsW : s ∈ Gamma.terminalFrontier W)
    (sourcePath : FinitePath Gamma.graph)
    (hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K)
    (hstart : sourcePath.start = s)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V)) :
    ∃ D : Data W K s, D.sourcePath = sourcePath := by
  obtain ⟨p, hpW, hpterm⟩ := hsW
  rcases p with old | r
  · exact ⟨{
      W_isWarp := hW
      switch_isWarp := hK
      switch_finiteCharacter := hKfinite
      old := old
      old_mem := hpW
      old_finish := Option.some.inj hpterm
      sourcePath := sourcePath
      source_mem := hsource
      source_start := hstart
      carrier_inter := hinter }, rfl⟩
  · change none = some s at hpterm
    cases hpterm

/-- Public one-port splice preserving the caller's displayed real source
component. -/
theorem exists_onePortSplice_with_path
    {W K : Set Gamma.DPath} {s : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hsW : s ∈ Gamma.terminalFrontier W)
    (sourcePath : FinitePath Gamma.graph)
    (hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K)
    (hstart : sourcePath.start = s)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        (Gamma.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier K ∧
      sourcePath.edgeSet ⊆ familyEdges U ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨D, hDsource⟩ := exists_data_of_port_with_path hW hK hKfinite hsW
    sourcePath hsource hstart hinter
  exact ⟨D.paths, D.paths_isWarp, D.vertexSet_paths, D.initialSet_paths,
    D.terminalFrontier_paths, by
      simpa only [hDsource] using D.sourcePath_edgeSet_subset_familyEdges,
    D.finite_rayTrace⟩

/-- Exact-edge strengthening of `exists_onePortSplice_with_path`.  The old
API is intentionally retained unchanged; consumers which keep a predicate on
the underlying edges can use this version to transport it through the splice. -/
theorem exists_onePortSplice_with_path_exact
    {W K : Set Gamma.DPath} {s : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hsW : s ∈ Gamma.terminalFrontier W)
    (sourcePath : FinitePath Gamma.graph)
    (hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K)
    (hstart : sourcePath.start = s)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      familyEdges U = familyEdges W ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        (Gamma.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier K ∧
      sourcePath.edgeSet ⊆ familyEdges U ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨D, hDsource⟩ := exists_data_of_port_with_path hW hK hKfinite hsW
    sourcePath hsource hstart hinter
  exact ⟨D.paths, D.paths_isWarp, D.familyEdges_paths, D.vertexSet_paths,
    D.initialSet_paths, D.terminalFrontier_paths, by
      simpa only [hDsource] using D.sourcePath_edgeSet_subset_familyEdges,
    D.finite_rayTrace⟩

/-- The assumption `s ∈ I[K]` supplies a unique member of the
finite-character switch warp, hence a concrete finite source path for the
one-port splice. -/
theorem exists_onePortSplice
    {W K : Set Gamma.DPath} {s : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hsW : s ∈ Gamma.terminalFrontier W)
    (hsK : s ∈ Gamma.initialSet K)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s} : Set V)) :
    ∃ (sourcePath : FinitePath Gamma.graph) (U : Set Gamma.DPath),
      (Sum.inl sourcePath : Gamma.DPath) ∈ K ∧
      sourcePath.start = s ∧
      Gamma.IsWarp U ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        (Gamma.terminalFrontier W \ {s}) ∪ Gamma.terminalFrontier K ∧
      sourcePath.edgeSet ⊆ familyEdges U ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨p, hpK, hpstart⟩ := hsK
  obtain ⟨sourcePath, hsourceEq⟩ := hKfinite hpK
  have hsource : (Sum.inl sourcePath : Gamma.DPath) ∈ K := hsourceEq ▸ hpK
  have hstart : sourcePath.start = s := by
    rw [hsourceEq] at hpstart
    change sourcePath.start = s at hpstart
    exact hpstart
  obtain ⟨U, hU, hUV, hUI, hUT, hsourceEdges, htrace⟩ :=
    exists_onePortSplice_with_path hW hK hKfinite hsW sourcePath hsource hstart hinter
  exact ⟨sourcePath, U, hsource, hstart, hU, hUV, hUI, hUT,
    hsourceEdges, htrace⟩

#print axioms exists_onePortSplice_with_path
#print axioms exists_onePortSplice_with_path_exact
#print axioms exists_onePortSplice

end Erdos599.ColouredSafeOnePortSplice
