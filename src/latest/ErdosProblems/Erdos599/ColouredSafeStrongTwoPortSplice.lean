/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BlueprintImaginaryEdgeSubdivision

/-!
# Splicing a finite two-port switch into one edge of a warp

This file is graph-independent.  An edge `s → t` of one member of `W` is
cut into a finite prefix ending at `s` and a finite-or-ray suffix beginning
at `t`.  Two distinct finite members of a fresh finite-character warp `K`
are then attached crosswise: the member starting at `s` is appended to the
old prefix, while the member ending at `t` is prepended to the old suffix.

The only freshness hypothesis is the natural carrier statement
`V[K] ∩ V[W] ⊆ {s,t}`.  All endpoint exclusions needed by the two
concatenations follow from warp disjointness; in particular no separate
assumption that the other members of `K` avoid `s` or `t` is made.
-/

noncomputable section

open Set

namespace Erdos599.ColouredSafeStrongTwoPortSplice

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Exact input data for the graph-independent two-port splice. -/
structure Data (W K : Set Gamma.DPath) (s t : V) where
  old : Gamma.DPath
  old_mem : old ∈ W
  old_edge : (s, t) ∈ old.edgeSet
  W_isWarp : Gamma.IsWarp W
  switch_isWarp : Gamma.IsWarp K
  switch_finiteCharacter : Gamma.HasFiniteCharacter K
  fromTail : FinitePath Gamma.graph
  toHead : FinitePath Gamma.graph
  fromTail_mem : (Sum.inl fromTail : Gamma.DPath) ∈ K
  toHead_mem : (Sum.inl toHead : Gamma.DPath) ∈ K
  fromTail_ne_toHead :
    (Sum.inl fromTail : Gamma.DPath) ≠ Sum.inl toHead
  fromTail_start : fromTail.start = s
  toHead_finish : toHead.finish = t
  carrier_inter :
    Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V)

namespace Data

variable {W K : Set Gamma.DPath} {s t : V} (D : Data W K s t)

/-- The occurrence-aware split of the old owner at `s → t`. -/
def split : D.old.EdgeSplit s t := Path.edgeSplit D.old D.old_edge

include D in
theorem tail_ne_head : s ≠ t := by
  intro hst
  have hsfront : s ∈ (D.split).front.support := (D.split).front_finish_mem
  have htback : t ∈ (D.split).back.support := (D.split).back_initial_mem
  exact Set.disjoint_left.mp (D.split).support_disjoint hsfront
    (by simpa only [hst] using htback)

theorem switch_paths_disjoint :
    Disjoint D.fromTail.support D.toHead.support :=
  D.switch_isWarp D.fromTail_mem D.toHead_mem D.fromTail_ne_toHead

theorem fromTail_finish_ne_head : D.fromTail.finish ≠ t := by
  intro hfinish
  have htFrom : t ∈ D.fromTail.support := by
    simpa only [hfinish] using D.fromTail.finish_mem_support
  have htTo : t ∈ D.toHead.support := by
    simpa only [D.toHead_finish] using D.toHead.finish_mem_support
  exact Set.disjoint_left.mp D.switch_paths_disjoint htFrom htTo

theorem toHead_start_ne_tail : D.toHead.start ≠ s := by
  intro hstart
  have hsTo : s ∈ D.toHead.support := by
    simpa only [hstart] using D.toHead.start_mem_support
  have hsFrom : s ∈ D.fromTail.support := by
    simpa only [D.fromTail_start] using D.fromTail.start_mem_support
  exact Set.disjoint_left.mp D.switch_paths_disjoint hsFrom hsTo

theorem fromTail_avoids_head : t ∉ D.fromTail.support := by
  intro ht
  have htTo : t ∈ D.toHead.support := by
    simpa only [D.toHead_finish] using D.toHead.finish_mem_support
  exact Set.disjoint_left.mp D.switch_paths_disjoint ht htTo

theorem toHead_avoids_tail : s ∉ D.toHead.support := by
  intro hs
  have hsFrom : s ∈ D.fromTail.support := by
    simpa only [D.fromTail_start] using D.fromTail.start_mem_support
  exact Set.disjoint_left.mp D.switch_paths_disjoint hsFrom hs

theorem old_inter_fromTail_subset :
    D.old.support ∩ D.fromTail.support ⊆ ({s, t} : Set V) := by
  intro x hx
  exact D.carrier_inter
    ⟨⟨Sum.inl D.fromTail, D.fromTail_mem, hx.2⟩,
      ⟨D.old, D.old_mem, hx.1⟩⟩

theorem old_inter_toHead_subset :
    D.old.support ∩ D.toHead.support ⊆ ({s, t} : Set V) := by
  intro x hx
  exact D.carrier_inter
    ⟨⟨Sum.inl D.toHead, D.toHead_mem, hx.2⟩,
      ⟨D.old, D.old_mem, hx.1⟩⟩

theorem front_inter_fromTail_subset :
    D.split.front.support ∩ D.fromTail.support ⊆ ({s} : Set V) :=
  D.split.front_inter_insert_subset D.fromTail D.fromTail_start
    D.old_inter_fromTail_subset

theorem toHead_inter_back_subset :
    D.toHead.support ∩ D.split.back.support ⊆ ({t} : Set V) := by
  intro x hx
  have hxOld : x ∈ D.old.support := by
    rw [D.split.support_eq]
    exact Or.inr hx.2
  have hxEnds := D.old_inter_toHead_subset ⟨hxOld, hx.1⟩
  rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
  · exact False.elim (D.toHead_avoids_tail (hxs ▸ hx.1))
  · exact hxt

/-- The old prefix followed by the switch component that starts at `s`. -/
def left : FinitePath Gamma.graph :=
  D.split.front.appendFinite D.fromTail
    (D.fromTail_start.trans D.split.front_finish.symm)
    (by simpa only [D.split.front_finish] using D.front_inter_fromTail_subset)

/-- The terminal of the incoming switch component is the initial point of
the old suffix. -/
theorem right_hit : D.toHead.finish ∈ D.split.back.support := by
  have ht : t ∈ D.split.back.support := D.split.back_initial_mem
  exact Eq.mpr
    (congrArg (fun z : V ↦ z ∈ D.split.back.support) D.toHead_finish) ht

theorem right_appendable :
    Path.Appendable D.toHead D.split.back D.right_hit := by
  apply Set.disjoint_left.mpr
  intro x hxTo hxBack
  have hxBack' : x ∈ D.split.back.support :=
    D.split.back.support_suffixFrom_subset _ _ hxBack.1
  have hxt : x = t := Set.mem_singleton_iff.mp
    (D.toHead_inter_back_subset ⟨hxTo, hxBack'⟩)
  exact hxBack.2 (Set.mem_singleton_iff.mpr
    (hxt.trans D.toHead_finish.symm))

/-- The switch component ending at `t`, followed by the old suffix. -/
def right : Gamma.DPath :=
  Path.appendAt D.toHead D.split.back D.right_hit D.right_appendable

private theorem suffixFrom_right_hit :
    D.split.back.suffixFrom D.toHead.finish D.right_hit = D.split.back := by
  have hfinish : D.toHead.finish = D.split.back.initial := by
    exact D.toHead_finish.trans D.split.back_initial.symm
  simpa only [hfinish] using Path.suffixFrom_initial_eq D.split.back
    (Path.initial_mem_support D.split.back)

@[simp] theorem left_start : D.left.start = D.old.initial := by
  rw [left, FinitePath.appendFinite_start, D.split.front_start]

@[simp] theorem left_finish : D.left.finish = D.fromTail.finish := by
  rw [left, FinitePath.appendFinite_finish]

@[simp] theorem left_support :
    D.left.support = D.split.front.support ∪ D.fromTail.support := by
  exact D.split.front.support_appendFinite_eq_union D.fromTail _ _

@[simp] theorem left_edgeSet :
    D.left.edgeSet = D.split.front.edgeSet ∪ D.fromTail.edgeSet := by
  exact Blueprint.LinkageBlueprint.FinitePath.edgeSet_appendFinite _ _ _ _

@[simp] theorem right_initial : D.right.initial = D.toHead.start := by
  exact (Path.extends_initial
    (Path.extends_appendAt D.toHead D.split.back D.right_hit
      D.right_appendable)).symm

@[simp] theorem right_terminal :
    D.right.terminal? = D.old.terminal? := by
  rw [right, Path.terminal?_appendAt, D.split.back_terminal]

@[simp] theorem right_support :
    D.right.support = D.toHead.support ∪ D.split.back.support := by
  rw [right, Path.support_appendAt, D.suffixFrom_right_hit]

@[simp] theorem right_edgeSet :
    D.right.edgeSet = D.toHead.edgeSet ∪ D.split.back.edgeSet := by
  rw [right, Path.edgeSet_appendAt, D.suffixFrom_right_hit]

theorem left_right_disjoint : Disjoint D.left.support D.right.support := by
  apply Set.disjoint_left.mpr
  intro x hxLeft hxRight
  rw [D.left_support] at hxLeft
  rw [D.right_support] at hxRight
  rcases hxLeft with hxFront | hxFrom <;>
    rcases hxRight with hxTo | hxBack
  · have hxOld : x ∈ D.old.support := by
      rw [D.split.support_eq]
      exact Or.inl hxFront
    have hxEnds := D.old_inter_toHead_subset ⟨hxOld, hxTo⟩
    rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
    · exact D.toHead_avoids_tail (hxs ▸ hxTo)
    · exact Set.disjoint_left.mp D.split.support_disjoint hxFront
        (Set.mem_singleton_iff.mp hxt ▸ D.split.back_initial_mem)
  · exact Set.disjoint_left.mp D.split.support_disjoint hxFront hxBack
  · exact Set.disjoint_left.mp D.switch_paths_disjoint hxFrom hxTo
  · have hxOld : x ∈ D.old.support := by
      rw [D.split.support_eq]
      exact Or.inr hxBack
    have hxEnds := D.old_inter_fromTail_subset ⟨hxOld, hxFrom⟩
    rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
    · exact Set.disjoint_left.mp D.split.support_disjoint
        (hxs ▸ D.split.front_finish_mem) hxBack
    · exact D.fromTail_avoids_head
        (Set.mem_singleton_iff.mp hxt ▸ hxFrom)

/-- The old components other than the cut owner. -/
def oldRemainder : Set Gamma.DPath := W \ {D.old}

/-- The switch components other than the two components attached at the
ports. -/
def switchRemainder : Set Gamma.DPath :=
  K \ {Sum.inl D.fromTail, Sum.inl D.toHead}

/-- The two crosswise spliced paths. -/
def replacements : Set Gamma.DPath :=
  {Sum.inl D.left, D.right}

/-- The complete two-port splice family. -/
def paths : Set Gamma.DPath :=
  D.replacements ∪ (D.oldRemainder ∪ D.switchRemainder)

theorem old_other_avoids_tail {q : Gamma.DPath}
    (hq : q ∈ D.oldRemainder) : s ∉ q.support := by
  intro hs
  have hsOld : s ∈ D.old.support :=
    (D.old.edgeSet_subset_support_prod D.old_edge).1
  have hqo : q = D.old := by
    by_contra hne
    exact Set.disjoint_left.mp (D.W_isWarp hq.1 D.old_mem hne) hs hsOld
  exact hq.2 (Set.mem_singleton_iff.mpr hqo)

theorem old_other_avoids_head {q : Gamma.DPath}
    (hq : q ∈ D.oldRemainder) : t ∉ q.support := by
  intro ht
  have htOld : t ∈ D.old.support :=
    (D.old.edgeSet_subset_support_prod D.old_edge).2
  have hqo : q = D.old := by
    by_contra hne
    exact Set.disjoint_left.mp (D.W_isWarp hq.1 D.old_mem hne) ht htOld
  exact hq.2 (Set.mem_singleton_iff.mpr hqo)

theorem switch_other_avoids_tail {q : Gamma.DPath}
    (hq : q ∈ D.switchRemainder) : s ∉ q.support := by
  intro hs
  have hsFrom : s ∈ D.fromTail.support := by
    simpa only [D.fromTail_start] using D.fromTail.start_mem_support
  have hqFrom : q = Sum.inl D.fromTail := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.switch_isWarp hq.1 D.fromTail_mem hne) hs hsFrom
  exact hq.2 (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hqFrom,
    true_or])

theorem switch_other_avoids_head {q : Gamma.DPath}
    (hq : q ∈ D.switchRemainder) : t ∉ q.support := by
  intro ht
  have htTo : t ∈ D.toHead.support := by
    simpa only [D.toHead_finish] using D.toHead.finish_mem_support
  have hqTo : q = Sum.inl D.toHead := by
    by_contra hne
    exact Set.disjoint_left.mp
      (D.switch_isWarp hq.1 D.toHead_mem hne) ht htTo
  exact hq.2 (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hqTo,
    true_or, or_true])

theorem old_other_disjoint_switch_path {q : Gamma.DPath}
    (hq : q ∈ D.oldRemainder) {r : Gamma.DPath} (hr : r ∈ K) :
    Disjoint q.support r.support := by
  apply Set.disjoint_left.mpr
  intro x hxq hxr
  have hxEnds := D.carrier_inter
    ⟨⟨r, hr, hxr⟩, ⟨q, hq.1, hxq⟩⟩
  rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
  · exact D.old_other_avoids_tail hq (hxs ▸ hxq)
  · exact D.old_other_avoids_head hq
      (Set.mem_singleton_iff.mp hxt ▸ hxq)

theorem switch_other_disjoint_old {q : Gamma.DPath}
    (hq : q ∈ D.switchRemainder) : Disjoint q.support D.old.support := by
  apply Set.disjoint_left.mpr
  intro x hxq hxOld
  have hxEnds := D.carrier_inter
    ⟨⟨q, hq.1, hxq⟩, ⟨D.old, D.old_mem, hxOld⟩⟩
  rcases Set.mem_insert_iff.mp hxEnds with hxs | hxt
  · exact D.switch_other_avoids_tail hq (hxs ▸ hxq)
  · exact D.switch_other_avoids_head hq
      (Set.mem_singleton_iff.mp hxt ▸ hxq)

theorem left_disjoint_old_other {q : Gamma.DPath}
    (hq : q ∈ D.oldRemainder) : Disjoint D.left.support q.support := by
  rw [D.left_support, Set.disjoint_union_left]
  refine ⟨?_, ?_⟩
  · exact (D.W_isWarp D.old_mem hq.1 (fun h ↦ hq.2
      (Set.mem_singleton_iff.mpr h.symm))).mono_left (by
        intro x hx
        rw [D.split.support_eq]
        exact Or.inl hx)
  · exact (D.old_other_disjoint_switch_path hq D.fromTail_mem).symm

theorem right_disjoint_old_other {q : Gamma.DPath}
    (hq : q ∈ D.oldRemainder) : Disjoint D.right.support q.support := by
  rw [D.right_support, Set.disjoint_union_left]
  refine ⟨?_, ?_⟩
  · exact (D.old_other_disjoint_switch_path hq D.toHead_mem).symm
  · exact (D.W_isWarp D.old_mem hq.1 (fun h ↦ hq.2
      (Set.mem_singleton_iff.mpr h.symm))).mono_left (by
        intro x hx
        rw [D.split.support_eq]
        exact Or.inr hx)

theorem left_disjoint_switch_other {q : Gamma.DPath}
    (hq : q ∈ D.switchRemainder) : Disjoint D.left.support q.support := by
  rw [D.left_support, Set.disjoint_union_left]
  refine ⟨?_, ?_⟩
  · exact (D.switch_other_disjoint_old hq).symm.mono_left (by
      intro x hx
      rw [D.split.support_eq]
      exact Or.inl hx)
  · exact D.switch_isWarp D.fromTail_mem hq.1 (fun h ↦ hq.2 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h,
        true_or]))

theorem right_disjoint_switch_other {q : Gamma.DPath}
    (hq : q ∈ D.switchRemainder) : Disjoint D.right.support q.support := by
  rw [D.right_support, Set.disjoint_union_left]
  refine ⟨?_, ?_⟩
  · exact D.switch_isWarp D.toHead_mem hq.1 (fun h ↦ hq.2 (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, h,
        true_or, or_true]))
  · exact (D.switch_other_disjoint_old hq).symm.mono_left (by
      intro x hx
      rw [D.split.support_eq]
      exact Or.inr hx)

private theorem isWarp_union_of_cross
    {A B : Set Gamma.DPath} (hA : Gamma.IsWarp A) (hB : Gamma.IsWarp B)
    (hcross : ∀ p ∈ A, ∀ q ∈ B, Disjoint p.support q.support) :
    Gamma.IsWarp (A ∪ B) := by
  intro p hp q hq hpq
  rcases hp with hpA | hpB <;> rcases hq with hqA | hqB
  · exact hA hpA hqA hpq
  · exact hcross p hpA q hqB
  · exact (hcross q hqA p hpB).symm
  · exact hB hpB hqB hpq

theorem replacements_isWarp : Gamma.IsWarp D.replacements := by
  intro p hp q hq hpq
  simp only [replacements, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact False.elim (hpq rfl)
  · exact D.left_right_disjoint
  · exact D.left_right_disjoint.symm
  · exact False.elim (hpq rfl)

theorem remainder_isWarp :
    Gamma.IsWarp (D.oldRemainder ∪ D.switchRemainder) := by
  apply isWarp_union_of_cross
  · exact DWeb.IsWarp.sdiff_singleton Gamma D.W_isWarp D.old
  · exact fun _ hp _ hq hpq ↦ D.switch_isWarp hp.1 hq.1 hpq
  · intro p hp q hq
    exact D.old_other_disjoint_switch_path hp hq.1

theorem paths_isWarp : Gamma.IsWarp D.paths := by
  apply isWarp_union_of_cross D.replacements_isWarp D.remainder_isWarp
  intro p hp q hq
  simp only [replacements, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · rcases hq with hqOld | hqSwitch
    · exact D.left_disjoint_old_other hqOld
    · exact D.left_disjoint_switch_other hqSwitch
  · rcases hq with hqOld | hqSwitch
    · exact D.right_disjoint_old_other hqOld
    · exact D.right_disjoint_switch_other hqSwitch

theorem left_mem_paths : (Sum.inl D.left : Gamma.DPath) ∈ D.paths := by
  exact Or.inl (Set.mem_insert _ _)

theorem right_mem_paths : D.right ∈ D.paths := by
  exact Or.inl (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem oldRemainder_subset_paths : D.oldRemainder ⊆ D.paths := by
  intro q hq
  exact Or.inr (Or.inl hq)

theorem switchRemainder_subset_paths : D.switchRemainder ⊆ D.paths := by
  intro q hq
  exact Or.inr (Or.inr hq)

theorem cutEdge_not_mem_oldRemainder {q : Gamma.DPath}
    (hq : q ∈ D.oldRemainder) : (s, t) ∉ q.edgeSet := by
  intro he
  exact D.old_other_avoids_tail hq (q.edgeSet_subset_support_prod he).1

/-- The splice loses no vertex of either input family and introduces no
other vertex. -/
theorem vertexSet_paths :
    Gamma.vertexSet D.paths = Gamma.vertexSet W ∪ Gamma.vertexSet K := by
  ext x
  constructor
  · rintro ⟨p, hp, hxp⟩
    rcases hp with hpReplacement | hpRemainder
    · simp only [replacements, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpReplacement
      rcases hpReplacement with rfl | rfl
      · change x ∈ D.left.support at hxp
        rw [D.left_support] at hxp
        rcases hxp with hxFront | hxFrom
        · left
          exact ⟨D.old, D.old_mem, by
            rw [D.split.support_eq]
            exact Or.inl hxFront⟩
        · right
          exact ⟨Sum.inl D.fromTail, D.fromTail_mem, hxFrom⟩
      · rw [D.right_support] at hxp
        rcases hxp with hxTo | hxBack
        · right
          exact ⟨Sum.inl D.toHead, D.toHead_mem, hxTo⟩
        · left
          exact ⟨D.old, D.old_mem, by
            rw [D.split.support_eq]
            exact Or.inr hxBack⟩
    · rcases hpRemainder with hpOld | hpSwitch
      · exact Or.inl ⟨p, hpOld.1, hxp⟩
      · exact Or.inr ⟨p, hpSwitch.1, hxp⟩
  · rintro (hxW | hxK)
    · obtain ⟨p, hpW, hxp⟩ := hxW
      by_cases hpo : p = D.old
      · subst p
        rw [D.split.support_eq] at hxp
        rcases hxp with hxFront | hxBack
        · refine ⟨Sum.inl D.left, D.left_mem_paths, ?_⟩
          change x ∈ D.left.support
          rw [D.left_support]
          exact Or.inl hxFront
        · exact ⟨D.right, D.right_mem_paths,
            D.right_support.symm ▸ Or.inr hxBack⟩
      · exact ⟨p, D.oldRemainder_subset_paths ⟨hpW, by
          simpa only [Set.mem_singleton_iff] using hpo⟩, hxp⟩
    · obtain ⟨p, hpK, hxp⟩ := hxK
      by_cases hpFrom : p = Sum.inl D.fromTail
      · subst p
        refine ⟨Sum.inl D.left, D.left_mem_paths, ?_⟩
        change x ∈ D.left.support
        rw [D.left_support]
        exact Or.inr hxp
      · by_cases hpTo : p = Sum.inl D.toHead
        · subst p
          exact ⟨D.right, D.right_mem_paths,
            D.right_support.symm ▸ Or.inl hxp⟩
        · exact ⟨p, D.switchRemainder_subset_paths ⟨hpK, by
            simp [hpFrom, hpTo]⟩, hxp⟩

/-- Exact edge accounting for the two-port splice.  The represented old
edge `s → t` is the only old edge removed; every switch edge is retained. -/
theorem familyEdges_paths :
    familyEdges D.paths =
      (familyEdges W \ {(s, t)}) ∪ familyEdges K := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨p, hp, hep⟩ := Set.mem_iUnion.mp he |>.imp fun _ h ↦
      Set.mem_iUnion.mp h
    rcases hp with hpReplacement | hpRemainder
    · simp only [replacements, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpReplacement
      rcases hpReplacement with rfl | rfl
      · change e ∈ D.left.edgeSet at hep
        rw [D.left_edgeSet] at hep
        rcases hep with heFront | heFrom
        · left
          exact ⟨Set.mem_iUnion.mpr ⟨D.old, Set.mem_iUnion.mpr
            ⟨D.old_mem, by
              rw [D.split.edgeSet_eq]
              exact Or.inl (Or.inl heFront)⟩⟩,
            fun he ↦ D.split.cutEdge_not_mem_front
              (Set.mem_singleton_iff.mp he ▸ heFront)⟩
        · right
          exact Set.mem_iUnion.mpr ⟨Sum.inl D.fromTail,
            Set.mem_iUnion.mpr ⟨D.fromTail_mem, heFrom⟩⟩
      · rw [D.right_edgeSet] at hep
        rcases hep with heTo | heBack
        · right
          exact Set.mem_iUnion.mpr ⟨Sum.inl D.toHead,
            Set.mem_iUnion.mpr ⟨D.toHead_mem, heTo⟩⟩
        · left
          exact ⟨Set.mem_iUnion.mpr ⟨D.old, Set.mem_iUnion.mpr
            ⟨D.old_mem, by
              rw [D.split.edgeSet_eq]
              exact Or.inr heBack⟩⟩,
            fun he ↦ D.split.cutEdge_not_mem_back
              (Set.mem_singleton_iff.mp he ▸ heBack)⟩
    · rcases hpRemainder with hpOld | hpSwitch
      · left
        exact ⟨Set.mem_iUnion.mpr ⟨p,
          Set.mem_iUnion.mpr ⟨hpOld.1, hep⟩⟩,
          fun he ↦ D.cutEdge_not_mem_oldRemainder hpOld
            (Set.mem_singleton_iff.mp he ▸ hep)⟩
      · right
        exact Set.mem_iUnion.mpr ⟨p,
          Set.mem_iUnion.mpr ⟨hpSwitch.1, hep⟩⟩
  · rintro e (heW | heK)
    · obtain ⟨heW, heCut⟩ := heW
      obtain ⟨p, hpW, hep⟩ := Set.mem_iUnion.mp heW |>.imp fun _ h ↦
        Set.mem_iUnion.mp h
      by_cases hpOld : p = D.old
      · subst p
        rw [D.split.edgeSet_eq] at hep
        rcases hep with heFrontCut | heBack
        · rcases heFrontCut with heFront | heMiddle
          · apply Set.mem_iUnion.mpr
            refine ⟨Sum.inl D.left, Set.mem_iUnion.mpr
              ⟨D.left_mem_paths, ?_⟩⟩
            change e ∈ D.left.edgeSet
            rw [D.left_edgeSet]
            exact Or.inl heFront
          · exact False.elim (heCut heMiddle)
        · apply Set.mem_iUnion.mpr
          refine ⟨D.right, Set.mem_iUnion.mpr ⟨D.right_mem_paths, ?_⟩⟩
          rw [D.right_edgeSet]
          exact Or.inr heBack
      · exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
          ⟨D.oldRemainder_subset_paths ⟨hpW, by
            simpa only [Set.mem_singleton_iff] using hpOld⟩, hep⟩⟩
    · obtain ⟨p, hpK, hep⟩ := Set.mem_iUnion.mp heK |>.imp fun _ h ↦
        Set.mem_iUnion.mp h
      by_cases hpFrom : p = Sum.inl D.fromTail
      · subst p
        apply Set.mem_iUnion.mpr
        refine ⟨Sum.inl D.left, Set.mem_iUnion.mpr
          ⟨D.left_mem_paths, ?_⟩⟩
        change e ∈ D.left.edgeSet
        rw [D.left_edgeSet]
        exact Or.inr hep
      · by_cases hpTo : p = Sum.inl D.toHead
        · subst p
          apply Set.mem_iUnion.mpr
          refine ⟨D.right, Set.mem_iUnion.mpr ⟨D.right_mem_paths, ?_⟩⟩
          rw [D.right_edgeSet]
          exact Or.inl hep
        · exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr
            ⟨D.switchRemainder_subset_paths ⟨hpK, by
              simp [hpFrom, hpTo]⟩, hep⟩⟩

/-- Initial vertices are those of `W`, together with all switch initials
except the consumed port `s`. -/
theorem initialSet_paths :
    Gamma.initialSet D.paths =
      Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases hp with hpReplacement | hpRemainder
    · simp only [replacements, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpReplacement
      rcases hpReplacement with rfl | rfl
      · left
        exact ⟨D.old, D.old_mem, D.left_start.symm.trans hpx⟩
      · right
        refine ⟨⟨Sum.inl D.toHead, D.toHead_mem,
          D.right_initial.symm.trans hpx⟩, ?_⟩
        intro hxs
        exact D.toHead_start_ne_tail
          (D.right_initial.symm.trans hpx |>.trans
            (Set.mem_singleton_iff.mp hxs))
    · rcases hpRemainder with hpOld | hpSwitch
      · exact Or.inl ⟨p, hpOld.1, hpx⟩
      · right
        refine ⟨⟨p, hpSwitch.1, hpx⟩, ?_⟩
        intro hxs
        exact D.switch_other_avoids_tail hpSwitch
          (by simpa only [hpx, Set.mem_singleton_iff.mp hxs] using
            Path.initial_mem_support p)
  · rintro (hxW | hxK)
    · obtain ⟨p, hpW, hpx⟩ := hxW
      by_cases hpo : p = D.old
      · subst p
        exact ⟨Sum.inl D.left, D.left_mem_paths,
          D.left_start.trans hpx⟩
      · exact ⟨p, D.oldRemainder_subset_paths ⟨hpW, by
          simpa only [Set.mem_singleton_iff] using hpo⟩, hpx⟩
    · obtain ⟨⟨p, hpK, hpx⟩, hxne⟩ := hxK
      by_cases hpFrom : p = Sum.inl D.fromTail
      · subst p
        exfalso
        apply hxne
        apply Set.mem_singleton_iff.mpr
        exact hpx.symm.trans D.fromTail_start
      · by_cases hpTo : p = Sum.inl D.toHead
        · subst p
          exact ⟨D.right, D.right_mem_paths,
            D.right_initial.trans hpx⟩
        · exact ⟨p, D.switchRemainder_subset_paths ⟨hpK, by
            simp [hpFrom, hpTo]⟩, hpx⟩

/-- Finite terminal vertices are those of `W`, together with all switch
terminals except the consumed port `t`.  This also covers a ray old owner:
the right splice is then a ray and contributes no terminal. -/
theorem terminalFrontier_paths :
    Gamma.terminalFrontier D.paths =
      Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) := by
  ext x
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases hp with hpReplacement | hpRemainder
    · simp only [replacements, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hpReplacement
      rcases hpReplacement with rfl | rfl
      · right
        change some D.left.finish = some x at hpx
        have hxFinish : D.fromTail.finish = x := Option.some.inj
          (by simpa only [D.left_finish] using hpx)
        refine ⟨⟨Sum.inl D.fromTail, D.fromTail_mem,
          congrArg some hxFinish⟩, ?_⟩
        intro hxt
        exact D.fromTail_finish_ne_head
          (hxFinish.trans (Set.mem_singleton_iff.mp hxt))
      · left
        exact ⟨D.old, D.old_mem, D.right_terminal.symm.trans hpx⟩
    · rcases hpRemainder with hpOld | hpSwitch
      · exact Or.inl ⟨p, hpOld.1, hpx⟩
      · right
        refine ⟨⟨p, hpSwitch.1, hpx⟩, ?_⟩
        intro hxt
        exact D.switch_other_avoids_head hpSwitch
          (by
            have hxSupport := Gamma.terminal_mem_support hpx
            simpa only [Set.mem_singleton_iff.mp hxt] using hxSupport)
  · rintro (hxW | hxK)
    · obtain ⟨p, hpW, hpx⟩ := hxW
      by_cases hpo : p = D.old
      · subst p
        exact ⟨D.right, D.right_mem_paths,
          D.right_terminal.trans hpx⟩
      · exact ⟨p, D.oldRemainder_subset_paths ⟨hpW, by
          simpa only [Set.mem_singleton_iff] using hpo⟩, hpx⟩
    · obtain ⟨⟨p, hpK, hpx⟩, hxne⟩ := hxK
      by_cases hpFrom : p = Sum.inl D.fromTail
      · subst p
        change some D.fromTail.finish = some x at hpx
        refine ⟨Sum.inl D.left, D.left_mem_paths, ?_⟩
        change some D.left.finish = some x
        simpa only [D.left_finish] using hpx
      · by_cases hpTo : p = Sum.inl D.toHead
        · subst p
          exfalso
          apply hxne
          apply Set.mem_singleton_iff.mpr
          exact Option.some.inj hpx |>.symm.trans D.toHead_finish
        · exact ⟨p, D.switchRemainder_subset_paths ⟨hpK, by
            simp [hpFrom, hpTo]⟩, hpx⟩

/-- If the old family has finite character, so does the splice.  This is
separate from the basic construction because the intended limiting-row
application allows `W` itself to contain rays. -/
theorem paths_finiteCharacter (hWfinite : Gamma.HasFiniteCharacter W) :
    Gamma.HasFiniteCharacter D.paths := by
  intro p hp
  rcases hp with hpReplacement | hpRemainder
  · simp only [replacements, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hpReplacement
    rcases hpReplacement with rfl | hpRight
    · exact ⟨D.left, rfl⟩
    · obtain ⟨f, hf⟩ := hWfinite D.old_mem
      have holdTerm : D.old.terminal? = some f.finish := by
        rw [hf]
        rfl
      have hrightTerm : D.right.terminal? = some f.finish :=
        D.right_terminal.trans holdTerm
      cases hright : D.right with
      | inl g => exact ⟨g, hpRight.trans hright⟩
      | inr r =>
          rw [hright] at hrightTerm
          change none = some f.finish at hrightTerm
          cases hrightTerm
  · rcases hpRemainder with hpOld | hpSwitch
    · exact hWfinite hpOld.1
    · exact D.switch_finiteCharacter hpSwitch.1

/-- The finite set of old edges discarded when the old owner is a ray. -/
def lostOldEdges : Set (V × V) :=
  D.split.front.edgeSet ∪ {(s, t)}

theorem lostOldEdges_finite : D.lostOldEdges.Finite :=
  (Alternating.FinitePath.edgeSet_finite D.split.front).union
    (Set.finite_singleton (s, t))

/-- Every edge in the untouched old suffix survives in the right splice. -/
theorem back_edgeSet_subset_right :
    D.split.back.edgeSet ⊆ D.right.edgeSet := by
  rw [D.right_edgeSet]
  exact Set.subset_union_right

/-- If the right splice is a ray, its old owner was a ray and all but the
finite prefix-and-cut edge set of that owner survive in the new ray. -/
theorem right_rayTrace (r : Ray Gamma.graph) (hr : D.right = Sum.inr r) :
    ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
      ∃ lost : Set (V × V), lost.Finite ∧
        r0.edgeSet \ lost ⊆ r.edgeSet := by
  have holdNone : D.old.terminal? = none := by
    rw [← D.right_terminal, hr]
    rfl
  cases hold : D.old with
  | inl f =>
      rw [hold] at holdNone
      change some f.finish = none at holdNone
      cases holdNone
  | inr r0 =>
      refine ⟨r0, ?_, D.lostOldEdges, D.lostOldEdges_finite, ?_⟩
      · simpa only [hold] using D.old_mem
      · intro e he
        have heOld : e ∈ D.old.edgeSet := by
          rw [hold]
          change e ∈ r0.edgeSet
          exact he.1
        rw [D.split.edgeSet_eq] at heOld
        rcases heOld with heFrontCut | heBack
        · rcases heFrontCut with heFront | heCut
          · exact False.elim (he.2 (Or.inl heFront))
          · exact False.elim (he.2 (Or.inr heCut))
        · have heRight : e ∈ D.right.edgeSet :=
            D.back_edgeSet_subset_right heBack
          rw [hr] at heRight
          change e ∈ r.edgeSet at heRight
          exact heRight

/-- Every new ray traces an old ray after deletion of finitely many old
edges.  The finite-character switch contributes no rays, and every old ray
other than the cut owner is retained literally.  This is the exact input
shape of `DWeb.infinitelyManyMarkedEdges_of_finite_rayTrace`. -/
theorem finite_rayTrace :
    ∀ r : Ray Gamma.graph, Sum.inr r ∈ D.paths →
      ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
        ∃ lost : Set (V × V), lost.Finite ∧
          r0.edgeSet \ lost ⊆ r.edgeSet := by
  intro r hr
  rcases hr with hrReplacement | hrRemainder
  · simp only [replacements, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hrReplacement
    rcases hrReplacement with hleft | hright
    · cases hleft
    · exact D.right_rayTrace r hright.symm
  · rcases hrRemainder with hrOld | hrSwitch
    · exact ⟨r, hrOld.1, ∅, Set.finite_empty, by simp⟩
    · obtain ⟨f, hf⟩ := D.switch_finiteCharacter hrSwitch.1
      cases hf

#print axioms Data.left_right_disjoint
#print axioms Data.paths_isWarp
#print axioms Data.vertexSet_paths
#print axioms Data.familyEdges_paths
#print axioms Data.initialSet_paths
#print axioms Data.terminalFrontier_paths
#print axioms Data.paths_finiteCharacter
#print axioms Data.finite_rayTrace

end Data

/-- Choose the unique old owner of a represented edge and package the
two-port splice data.  Uniqueness itself is supplied by `hW`; downstream
users generally need only the chosen data and its proved output laws. -/
theorem exists_data_of_familyEdge
    {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (ps qt : FinitePath Gamma.graph)
    (hps : (Sum.inl ps : Gamma.DPath) ∈ K)
    (hqt : (Sum.inl qt : Gamma.DPath) ∈ K)
    (hpq : (Sum.inl ps : Gamma.DPath) ≠ Sum.inl qt)
    (hpsStart : ps.start = s) (hqtFinish : qt.finish = t)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V)) :
    Nonempty (Data W K s t) := by
  obtain ⟨old, hold⟩ := Set.mem_iUnion.mp hst
  obtain ⟨holdW, holdEdge⟩ := Set.mem_iUnion.mp hold
  exact ⟨{
    old := old
    old_mem := holdW
    old_edge := holdEdge
    W_isWarp := hW
    switch_isWarp := hK
    switch_finiteCharacter := hKfinite
    fromTail := ps
    toHead := qt
    fromTail_mem := hps
    toHead_mem := hqt
    fromTail_ne_toHead := hpq
    fromTail_start := hpsStart
    toHead_finish := hqtFinish
    carrier_inter := hinter }⟩

/-- Graph-independent existential form of the strong two-port splice.
It chooses the old edge owner internally and returns all boundary, carrier,
and ray-trace conclusions needed by the strong-switch assembly. -/
theorem exists_twoPortSplice
    {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (ps qt : FinitePath Gamma.graph)
    (hps : (Sum.inl ps : Gamma.DPath) ∈ K)
    (hqt : (Sum.inl qt : Gamma.DPath) ∈ K)
    (hpq : (Sum.inl ps : Gamma.DPath) ≠ Sum.inl qt)
    (hpsStart : ps.start = s) (hqtFinish : qt.finish = t)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨D⟩ := exists_data_of_familyEdge hW hK hKfinite hst ps qt
    hps hqt hpq hpsStart hqtFinish hinter
  exact ⟨D.paths, D.paths_isWarp, D.vertexSet_paths,
    D.initialSet_paths, D.terminalFrontier_paths, D.finite_rayTrace⟩

/-- Exact-edge strengthening of `exists_twoPortSplice`.  In particular, the
only old edge omitted from the displayed relation is the cut edge `(s,t)`. -/
theorem exists_twoPortSplice_exact
    {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hK : Gamma.IsWarp K)
    (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (ps qt : FinitePath Gamma.graph)
    (hps : (Sum.inl ps : Gamma.DPath) ∈ K)
    (hqt : (Sum.inl qt : Gamma.DPath) ∈ K)
    (hpq : (Sum.inl ps : Gamma.DPath) ≠ Sum.inl qt)
    (hpsStart : ps.start = s) (hqtFinish : qt.finish = t)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧
      familyEdges U = (familyEdges W \ {(s, t)}) ∪ familyEdges K ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) ∧
      (∀ r : Ray Gamma.graph, Sum.inr r ∈ U →
        ∃ r0 : Ray Gamma.graph, Sum.inr r0 ∈ W ∧
          ∃ lost : Set (V × V), lost.Finite ∧
            r0.edgeSet \ lost ⊆ r.edgeSet) := by
  obtain ⟨D⟩ := exists_data_of_familyEdge hW hK hKfinite hst ps qt
    hps hqt hpq hpsStart hqtFinish hinter
  exact ⟨D.paths, D.paths_isWarp, D.familyEdges_paths, D.vertexSet_paths,
    D.initialSet_paths, D.terminalFrontier_paths, D.finite_rayTrace⟩

/-- Finite-character specialization of `exists_twoPortSplice`. -/
theorem exists_finiteTwoPortSplice
    {W K : Set Gamma.DPath} {s t : V}
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hK : Gamma.IsWarp K) (hKfinite : Gamma.HasFiniteCharacter K)
    (hst : (s, t) ∈ familyEdges W)
    (ps qt : FinitePath Gamma.graph)
    (hps : (Sum.inl ps : Gamma.DPath) ∈ K)
    (hqt : (Sum.inl qt : Gamma.DPath) ∈ K)
    (hpq : (Sum.inl ps : Gamma.DPath) ≠ Sum.inl qt)
    (hpsStart : ps.start = s) (hqtFinish : qt.finish = t)
    (hinter : Gamma.vertexSet K ∩ Gamma.vertexSet W ⊆ ({s, t} : Set V)) :
    ∃ U : Set Gamma.DPath,
      Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
      Gamma.vertexSet U = Gamma.vertexSet W ∪ Gamma.vertexSet K ∧
      Gamma.initialSet U =
        Gamma.initialSet W ∪ (Gamma.initialSet K \ {s}) ∧
      Gamma.terminalFrontier U =
        Gamma.terminalFrontier W ∪ (Gamma.terminalFrontier K \ {t}) := by
  obtain ⟨D⟩ := exists_data_of_familyEdge hW hK hKfinite hst ps qt
    hps hqt hpq hpsStart hqtFinish hinter
  exact ⟨D.paths, D.paths_isWarp, D.paths_finiteCharacter hWfinite,
    D.vertexSet_paths, D.initialSet_paths, D.terminalFrontier_paths⟩

#print axioms exists_twoPortSplice
#print axioms exists_twoPortSplice_exact
#print axioms exists_finiteTwoPortSplice

end Erdos599.ColouredSafeStrongTwoPortSplice
