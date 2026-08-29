/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintSplice
import ErdosProblems.Erdos599.CyclowarpDecomposition
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# The source warp diamond

The diamond in Assertion 9.31 is not the union of the old warp with the
whole later row.  A later-row path meeting the old warp is attached at its
first (and, by compatibility, initial) contact, while a later-row path with
no such contact survives as a separate member.  Thus the printed operation
`W \diamond U` is exactly the source star together with the unattached
members of `U`.

This file implements that operation and proves its two source-level facts:
its carrier and edge relation are the literal unions of the input carriers
and edge relations, and no newly supplied edge enters the old carrier.
The path family nevertheless prunes the conflicting prefixes by using
`DWeb.star`; it is not the raw family union.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
open DirectedPath Alternating

namespace DWeb

universe u

variable {V : Type u}
variable (G : DWeb V)

/-- The later-row members which do not attach to an old terminal. -/
def unattachedNew (W U : Set G.DPath) : Set G.DPath :=
  {q | q ∈ U ∧ q.initial ∉ G.terminalFrontier W}

@[simp] theorem mem_unattachedNew {W U : Set G.DPath} {q : G.DPath} :
    q ∈ G.unattachedNew W U ↔
      q ∈ U ∧ q.initial ∉ G.terminalFrontier W :=
  Iff.rfl

/-- Source-faithful family diamond: attach every later path which meets the
old family and retain every later path which does not meet it. -/
def warpDiamond {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) : Set G.DPath :=
  G.star hcompat ∪ G.unattachedNew W U

@[simp] theorem mem_warpDiamond {W U : Set G.DPath}
    (hcompat : G.StarCompatible W U) {q : G.DPath} :
    q ∈ G.warpDiamond hcompat ↔
      q ∈ G.star hcompat ∨ q ∈ G.unattachedNew W U :=
  Iff.rfl

/-- A starred old path is disjoint from every unattached later-row path. -/
theorem disjoint_starPath_unattachedNew {W U : Set G.DPath}
    (hU : G.IsWarp U) (hcompat : G.StarCompatible W U)
    (p : W) {q : G.DPath} (hq : q ∈ G.unattachedNew W U) :
    Disjoint (G.starPath hcompat p).support q.support := by
  apply Set.disjoint_left.2
  intro x hxp hxq
  rcases G.mem_support_starPath_cases hcompat p hxp with hxold | hxnew
  · have hmeet := hcompat p.1 p.2 q hq.1 x hxold hxq
    apply hq.2
    exact ⟨p.1, p.2,
      hmeet.1.trans (congrArg some hmeet.2.symm)⟩
  · obtain ⟨t, r, hpterm, hrU, hrstart, hxr⟩ := hxnew
    by_cases hrq : r = q
    · subst r
      apply hq.2
      exact ⟨p.1, p.2,
        hpterm.trans (congrArg some hrstart.symm)⟩
    · exact Set.disjoint_left.1 (hU hrU hq.1 hrq) hxr hxq

/-- The source diamond is a warp. -/
theorem isWarp_warpDiamond {W U : Set G.DPath}
    (hW : G.IsWarp W) (hU : G.IsWarp U)
    (hcompat : G.StarCompatible W U) :
    G.IsWarp (G.warpDiamond hcompat) := by
  intro p hp q hq hpq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact G.isWarp_star hW hU hcompat hp hq hpq
  · obtain ⟨r, rfl⟩ := hp
    exact G.disjoint_starPath_unattachedNew hU hcompat r hq
  · obtain ⟨r, rfl⟩ := hq
    exact (G.disjoint_starPath_unattachedNew hU hcompat r hp).symm
  · exact hU hp.1 hq.1 hpq

/-- A finite-character old family and finite-character later row have a
finite-character source diamond. -/
theorem hasFiniteCharacter_warpDiamond {W U : Set G.DPath}
    (hWfinite : G.HasFiniteCharacter W)
    (hUfinite : G.HasFiniteCharacter U)
    (hcompat : G.StarCompatible W U) :
    G.HasFiniteCharacter (G.warpDiamond hcompat) := by
  intro p hp
  rcases hp with hp | hp
  · exact CardinalInduction.SliceSpliceSource.hasFiniteCharacter_star
      hWfinite hUfinite hcompat hp
  · exact hUfinite hp.1

private theorem edgeSet_appendFinite_subset_union_of_finite
    (fp : FinitePath G.graph) (q : G.DPath)
    (hstart : q.initial = fp.finish)
    (hinter : fp.support ∩ q.support ⊆ {fp.finish})
    (hqfinite : ∃ g : FinitePath G.graph, q = .inl g) :
    (Path.appendFinite fp q hstart hinter).edgeSet ⊆
      fp.edgeSet ∪ q.edgeSet := by
  rcases q with g | ray
  · intro e he
    change g.start = fp.finish at hstart
    change fp.support ∩ g.support ⊆ {fp.finish} at hinter
    change e ∈ (fp.appendFinite g hstart hinter).edgeSet at he
    rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite] at he
    exact he
  · obtain ⟨g, hg⟩ := hqfinite
    cases hg

private theorem edgeSet_right_subset_appendFinite_of_finite
    (fp : FinitePath G.graph) (q : G.DPath)
    (hstart : q.initial = fp.finish)
    (hinter : fp.support ∩ q.support ⊆ {fp.finish})
    (hqfinite : ∃ g : FinitePath G.graph, q = .inl g) :
    q.edgeSet ⊆ (Path.appendFinite fp q hstart hinter).edgeSet := by
  rcases q with g | ray
  · intro e he
    change g.start = fp.finish at hstart
    change fp.support ∩ g.support ⊆ {fp.finish} at hinter
    change e ∈ (fp.appendFinite g hstart hinter).edgeSet
    rw [Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite]
    exact Or.inr he
  · obtain ⟨g, hg⟩ := hqfinite
    cases hg

/-- Every star edge comes from one of the two input families.  This focused
version avoids importing the later club-stage attachment package. -/
theorem familyEdges_star_subset_union {W U : Set G.DPath}
    (hUfinite : G.HasFiniteCharacter U)
    (hcompat : G.StarCompatible W U) :
    familyEdges (G.star hcompat) ⊆
      familyEdges W ∪ familyEdges U := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he
  obtain ⟨r, ⟨p, rfl⟩, he⟩ := he
  rcases p with ⟨p, hpW⟩
  rcases p with fp | ray
  · simp only [starPath] at he
    split at he
    next h =>
      let q := Classical.choose h
      have hqU : q ∈ U := (Classical.choose_spec h).1
      have hqstart : q.initial = fp.finish :=
        (Classical.choose_spec h).2
      have hinter : fp.support ∩ q.support ⊆ {fp.finish} := by
        intro x hx
        have hx' := hcompat (.inl fp) hpW q hqU x hx.1 hx.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hx'.1).symm
      have he' := G.edgeSet_appendFinite_subset_union_of_finite
        fp q hqstart hinter (hUfinite hqU) he
      rcases he' with he | he
      · exact Or.inl (Set.mem_iUnion.2 ⟨(.inl fp : G.DPath),
          Set.mem_iUnion.2 ⟨hpW, he⟩⟩)
      · exact Or.inr (Set.mem_iUnion.2 ⟨q,
          Set.mem_iUnion.2 ⟨hqU, he⟩⟩)
    next _ => exact Or.inl (Set.mem_iUnion.2 ⟨(.inl fp : G.DPath),
      Set.mem_iUnion.2 ⟨hpW, he⟩⟩)
  · exact Or.inl (Set.mem_iUnion.2 ⟨(.inr ray : G.DPath),
      Set.mem_iUnion.2 ⟨hpW, he⟩⟩)

/-- The local, one-member form of coverage by source star.  Unlike the
older global lemma it assumes only that this particular later path begins
at an old terminal. -/
theorem mem_vertexSet_star_of_mem_new_at {W U : Set G.DPath}
    (hU : G.IsWarp U) (hcompat : G.StarCompatible W U)
    {q : G.DPath} (hqU : q ∈ U)
    (hqinitial : q.initial ∈ G.terminalFrontier W)
    {x : V} (hxq : x ∈ q.support) :
    x ∈ G.vertexSet (G.star hcompat) := by
  obtain ⟨p, hpW, hpterm⟩ := hqinitial
  rcases p with fp | r
  · have hfinish : fp.finish = q.initial := Option.some.inj hpterm
    let old : W := ⟨(.inl fp : G.DPath), hpW⟩
    refine ⟨G.starPath hcompat old, ⟨old, rfl⟩, ?_⟩
    dsimp only [old]
    simp only [starPath]
    split
    next h =>
      let q' := Classical.choose h
      have hq'U : q' ∈ U := (Classical.choose_spec h).1
      have hq'start : q'.initial = fp.finish :=
        (Classical.choose_spec h).2
      have hq'eq : q' = q := by
        by_contra hne
        apply Set.disjoint_left.1 (hU hq'U hqU hne)
          q'.initial_mem_support
        rw [hq'start, hfinish]
        exact q.initial_mem_support
      dsimp only [q'] at hq'eq ⊢
      have hxchoose : x ∈ (Classical.choose h).support := by
        simpa only [hq'eq] using hxq
      have hinter : fp.support ∩ (Classical.choose h).support ⊆
          {fp.finish} := by
        intro y hy
        have hy' := hcompat (.inl fp) hpW (Classical.choose h) hq'U
          y hy.1 hy.2
        exact Set.mem_singleton_iff.2 (Option.some.inj hy'.1).symm
      rw [Path.support_appendFinite fp (Classical.choose h) hq'start hinter]
      exact Or.inr hxchoose
    next h =>
      exfalso
      apply h
      exact ⟨q, hqU, hfinish.symm⟩
  · simp at hpterm

/-- The source diamond has exactly the union of the two input carriers. -/
theorem vertexSet_warpDiamond {W U : Set G.DPath}
    (hU : G.IsWarp U) (hcompat : G.StarCompatible W U) :
    G.vertexSet (G.warpDiamond hcompat) =
      G.vertexSet W ∪ G.vertexSet U := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hxp⟩
    rcases hp with hp | hp
    · exact CardinalInduction.SliceSpliceSource.vertexSet_star_subset_union
        hcompat ⟨p, hp, hxp⟩
    · exact Or.inr ⟨p, hp.1, hxp⟩
  · rintro x (hxW | hxU)
    · obtain ⟨p, hpW, hxp⟩ := hxW
      let old : W := ⟨p, hpW⟩
      exact ⟨G.starPath hcompat old, Or.inl ⟨old, rfl⟩,
        Path.support_mono_of_extends
          (G.extends_starPath hcompat old) hxp⟩
    · obtain ⟨q, hqU, hxq⟩ := hxU
      by_cases hqinitial : q.initial ∈ G.terminalFrontier W
      · obtain ⟨r, hrstar, hxr⟩ :=
          G.mem_vertexSet_star_of_mem_new_at hU hcompat hqU hqinitial hxq
        exact ⟨r, Or.inl hrstar, hxr⟩
      · exact ⟨q, Or.inr ⟨hqU, hqinitial⟩, hxq⟩

private theorem mem_familyEdges_star_of_mem_new_at {W U : Set G.DPath}
    (hU : G.IsWarp U) (hUfinite : G.HasFiniteCharacter U)
    (hcompat : G.StarCompatible W U)
    {q : G.DPath} (hqU : q ∈ U)
    (hqinitial : q.initial ∈ G.terminalFrontier W)
    {e : V × V} (heq : e ∈ q.edgeSet) :
    e ∈ familyEdges (G.star hcompat) := by
  rcases q with g | ray
  · obtain ⟨p, hpW, hpterm⟩ := hqinitial
    rcases p with fp | r
    · have hfinish : fp.finish = g.start := Option.some.inj hpterm
      let old : W := ⟨(.inl fp : G.DPath), hpW⟩
      refine Set.mem_iUnion.2 ⟨G.starPath hcompat old,
        Set.mem_iUnion.2 ⟨⟨old, rfl⟩, ?_⟩⟩
      dsimp only [old]
      simp only [starPath]
      split
      next h =>
        let q' := Classical.choose h
        have hq'U : q' ∈ U := (Classical.choose_spec h).1
        have hq'start : q'.initial = fp.finish :=
          (Classical.choose_spec h).2
        have hq'eq : q' = (.inl g : G.DPath) := by
          by_contra hne
          apply Set.disjoint_left.1 (hU hq'U hqU hne)
            q'.initial_mem_support
          rw [hq'start, hfinish]
          exact g.start_mem_support
        dsimp only [q'] at hq'eq ⊢
        have heq' : e ∈ (Classical.choose h).edgeSet := by
          simpa only [hq'eq] using heq
        exact G.edgeSet_right_subset_appendFinite_of_finite
          fp (Classical.choose h) hq'start _
            (hUfinite hq'U) heq'
      next h =>
        exfalso
        apply h
        exact ⟨(.inl g : G.DPath), hqU, hfinish.symm⟩
    · simp at hpterm
  · obtain ⟨g, hg⟩ := hUfinite hqU
    cases hg

/-- The source diamond has exactly the union of the two input edge
relations. -/
theorem familyEdges_warpDiamond {W U : Set G.DPath}
    (hU : G.IsWarp U) (hUfinite : G.HasFiniteCharacter U)
    (hcompat : G.StarCompatible W U) :
    familyEdges (G.warpDiamond hcompat) =
      familyEdges W ∪ familyEdges U := by
  apply Set.Subset.antisymm
  · intro e he
    simp only [familyEdges, Set.mem_iUnion] at he
    obtain ⟨p, hp, hep⟩ := he
    rcases hp with hp | hp
    · exact G.familyEdges_star_subset_union hUfinite hcompat
        (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hep⟩⟩)
    · exact Or.inr (Set.mem_iUnion.2 ⟨p,
        Set.mem_iUnion.2 ⟨hp.1, hep⟩⟩)
  · rintro e (heW | heU)
    · simp only [familyEdges, Set.mem_iUnion] at heW ⊢
      obtain ⟨p, hpW, hep⟩ := heW
      let old : W := ⟨p, hpW⟩
      exact ⟨G.starPath hcompat old, Or.inl ⟨old, rfl⟩,
        Path.edgeSet_mono_of_extends
          (G.extends_starPath hcompat old) hep⟩
    · simp only [familyEdges, Set.mem_iUnion] at heU ⊢
      obtain ⟨q, hqU, heq⟩ := heU
      by_cases hqinitial : q.initial ∈ G.terminalFrontier W
      · have heStar := G.mem_familyEdges_star_of_mem_new_at
          hU hUfinite hcompat hqU hqinitial heq
        simp only [familyEdges, Set.mem_iUnion] at heStar
        obtain ⟨r, hr, her⟩ := heStar
        exact ⟨r, Or.inl hr, her⟩
      · exact ⟨q, Or.inr ⟨hqU, hqinitial⟩, heq⟩

/-- No edge newly supplied by the later row enters the old carrier.  This is
the fresh-incidence fact used by the compressed 9.31 splice. -/
theorem warpDiamond_noNewIncomingOld {W U : Set G.DPath}
    (hU : G.IsWarp U) (hUfinite : G.HasFiniteCharacter U)
    (hcompat : G.StarCompatible W U) :
    ∀ {x y : V}, x ∈ G.vertexSet W →
      (y, x) ∈ familyEdges (G.warpDiamond hcompat) →
        (y, x) ∈ familyEdges W := by
  intro x y hxW hyx
  rw [G.familyEdges_warpDiamond hU hUfinite hcompat] at hyx
  rcases hyx with hyx | hyx
  · exact hyx
  · simp only [familyEdges, Set.mem_iUnion] at hyx
    obtain ⟨q, hqU, hyxq⟩ := hyx
    obtain ⟨p, hpW, hxp⟩ := hxW
    have hmeet := hcompat p hpW q hqU x hxp
      (q.edgeSet_subset_support_prod hyxq).2
    rw [← hmeet.2] at hyxq
    rcases q with q | r
    · exact False.elim
        (Alternating.FinitePath.no_incoming_edge_at_start q y hyxq)
    · obtain ⟨n, hn⟩ := hyxq
      have hzero : n + 1 = 0 := by
        apply r.injective
        exact (congrArg Prod.snd hn).symm
      omega

#print axioms isWarp_warpDiamond
#print axioms vertexSet_warpDiamond
#print axioms familyEdges_warpDiamond
#print axioms warpDiamond_noNewIncomingOld

end DWeb

namespace Blueprint
namespace LinkageBlueprint

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The blueprint-level form of the source warp diamond used in Assertion
9.31.  This is the formal `A \diamond W[X]`. -/
def sourceWarpDiamond
    (old later : LinkageBlueprint Gamma Y kappa)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    LinkageBlueprint Gamma Y kappa where
  paths := (imaginaryWeb Gamma Y kappa).warpDiamond hcompat
  isWarp := (imaginaryWeb Gamma Y kappa).isWarp_warpDiamond
    old.isWarp later.isWarp hcompat

@[simp] theorem paths_sourceWarpDiamond
    (old later : LinkageBlueprint Gamma Y kappa)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    (sourceWarpDiamond old later hcompat).paths =
      (imaginaryWeb Gamma Y kappa).warpDiamond hcompat :=
  rfl

@[simp] theorem vertexSet_sourceWarpDiamond
    (old later : LinkageBlueprint Gamma Y kappa)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    (sourceWarpDiamond old later hcompat).vertexSet =
      old.vertexSet ∪ later.vertexSet :=
  (imaginaryWeb Gamma Y kappa).vertexSet_warpDiamond
    later.isWarp hcompat

@[simp] theorem edgeSet_sourceWarpDiamond
    (old later : LinkageBlueprint Gamma Y kappa)
    (hlaterFinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      later.paths)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    (sourceWarpDiamond old later hcompat).edgeSet =
      old.edgeSet ∪ later.edgeSet :=
  (imaginaryWeb Gamma Y kappa).familyEdges_warpDiamond
    later.isWarp hlaterFinite hcompat

/-- At blueprint level, the source diamond retains every old vertex and
edge. -/
theorem sourceWarpDiamond_realPart_extends
    (old later : LinkageBlueprint Gamma Y kappa)
    (hlaterFinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      later.paths)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    old.realPart.Extends
      (sourceWarpDiamond old later hcompat).realPart := by
  constructor
  · simpa only [realPart_vertices] using
      (show old.vertexSet ⊆
          (sourceWarpDiamond old later hcompat).vertexSet by
        rw [vertexSet_sourceWarpDiamond]
        exact Set.subset_union_left)
  · simp only [realPart_edges]
    rw [edgeSet_sourceWarpDiamond old later hlaterFinite hcompat]
    rintro e ⟨he, hadj⟩
    exact ⟨Or.inl he, hadj⟩

/-- No edge introduced by the actual 9.31 source diamond enters the old
blueprint carrier. -/
theorem sourceWarpDiamond_noNewIncomingOld
    (old later : LinkageBlueprint Gamma Y kappa)
    (hlaterFinite : (imaginaryWeb Gamma Y kappa).HasFiniteCharacter
      later.paths)
    (hcompat : (imaginaryWeb Gamma Y kappa).StarCompatible
      old.paths later.paths) :
    ∀ {x y : V}, x ∈ old.vertexSet →
      (y, x) ∈ (sourceWarpDiamond old later hcompat).edgeSet →
        (y, x) ∈ old.edgeSet :=
  (imaginaryWeb Gamma Y kappa).warpDiamond_noNewIncomingOld
    later.isWarp hlaterFinite hcompat

#print axioms sourceWarpDiamond_realPart_extends
#print axioms sourceWarpDiamond_noNewIncomingOld

end LinkageBlueprint
end Blueprint
end Erdos599
