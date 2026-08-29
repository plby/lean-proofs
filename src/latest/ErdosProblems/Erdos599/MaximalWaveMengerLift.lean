/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AharoniBerger

/-!
# Lifting a Menger pair through a wave quotient

The usual maximal-wave splice asks for a linkage covering every vertex of
the retained wave frontier.  For recursive or componentwise decompositions
that is stronger than necessary.  A Menger pair in the quotient already has
the right global alternative: its packing chooses the frontier vertices that
are actually used, while its separator blocks paths from all the unused
frontier vertices.

This file proves that such a quotient Menger pair lifts to a Menger pair in
the original web.  It is the sound internal-separator gluing interface needed
by source/target-symmetric decompositions; there is no allocation of every
frontier vertex to a residual component.
-/

noncomputable section

namespace Erdos599
namespace AharoniBerger
namespace MaximalWaveMengerLift

open Set DirectedPath

universe u

variable {V : Type u}

abbrev Separator (G : DWeb V) (M : G.Wave) : Set V :=
  concreteMaximalSeparator G M

abbrev Quotient (G : DWeb V) (M : G.Wave) : DWeb V :=
  G.quotient (Separator G M)

abbrev QuotientABPath (G : DWeb V) (M : G.Wave) :=
  Bridge.DirectedABPath (Quotient G M).graph
    (Quotient G M).source (Quotient G M).target

/-- The retained frontier vertex at which a quotient path starts. -/
def startPort (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : Separator G M :=
  ⟨q.path.start, by
    change q.path.start ∈ concreteMaximalSeparator G M
    rw [← quotient_concreteMaximalSeparator_source G M]
    exact q.start_mem⟩

@[simp]
theorem startPort_val (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : (startPort G M q).1 = q.path.start :=
  rfl

/-- Lift one quotient path back to the original digraph. -/
def liftedRight (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : FinitePath G.graph :=
  q.path.lift (fun {_ _} h ↦ G.quotient_adj_imp h)

@[simp]
theorem liftedRight_start (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : (liftedRight G M q).start = q.path.start :=
  rfl

@[simp]
theorem liftedRight_finish (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : (liftedRight G M q).finish = q.path.finish :=
  rfl

@[simp]
theorem liftedRight_support (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) :
    (liftedRight G M q).support = q.path.support := by
  exact FinitePath.support_lift
    (fun {_ _} h ↦ G.quotient_adj_imp h) q.path

/-- Re-index the lifted quotient walk so that it begins at the terminal of
the selected old-wave prefix. -/
def rightWalk (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) :
    Walk G.graph (ConcreteSplicing.leftFinite G M (startPort G M q)).finish
      (liftedRight G M q).finish :=
  RelationalRoof.castStart G.graph.Adj
    ((liftedRight_start G M q).trans
      (ConcreteSplicing.leftFinite_finish G M (startPort G M q)).symm)
    (liftedRight G M q).walk

theorem rightWalk_isPath (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : (rightWalk G M q).IsPath := by
  rw [Walk.IsPath, rightWalk, RelationalRoof.support_castStart]
  exact (liftedRight G M q).isPath

@[simp]
theorem rightWalk_support (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) :
    (rightWalk G M q).support = q.path.walk.support := by
  rw [rightWalk, RelationalRoof.support_castStart]
  change (liftedRight G M q).walk.support = q.path.walk.support
  exact Walk.support_lift _ _

/-- Every old-wave prefix is disjoint from the noninitial portion of every
quotient path. -/
theorem left_support_disjoint_right_tail
    (G : DWeb V) (M : G.Wave)
    (s : Separator G M) (q : QuotientABPath G M) :
    (ConcreteSplicing.leftFinite G M s).walk.support.Disjoint
      (rightWalk G M q).support.tail := by
  rw [List.disjoint_left]
  intro x hxleft hxright
  have hxroof : x ∈ G.roof (Separator G M) := by
    apply (essentialWarpPart_isWave G M).self_roofing
    exact ⟨Sum.inl (ConcreteSplicing.leftFinite G M s),
      ConcreteSplicing.leftFinite_mem G M s, hxleft⟩
  have hxright' : x ∈ q.path.walk.support.tail := by
    simpa only [rightWalk_support] using hxright
  have havoid := ConcreteSplicing.quotientWalk_tail_avoids G
    q.path.walk hxright'
  by_cases hxessential : x ∈ G.essential (Separator G M)
  · exact havoid.2 (G.essential_subset (Separator G M) hxessential)
  · exact havoid.1 ⟨hxroof, hxessential⟩

/-- Splice the old-wave prefix at the quotient path's initial frontier
vertex to that quotient path. -/
def splicedFinitePath (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) : FinitePath G.graph :=
  (ConcreteSplicing.leftFinite G M (startPort G M q)).appendWalkOfDisjoint
    (rightWalk G M q) (rightWalk_isPath G M q)
    (left_support_disjoint_right_tail G M (startPort G M q) q)

theorem mem_splicedFinitePath_support_iff
    (G : DWeb V) (M : G.Wave) (q : QuotientABPath G M) (x : V) :
    x ∈ (splicedFinitePath G M q).support ↔
      x ∈ (ConcreteSplicing.leftFinite G M
        (startPort G M q)).walk.support ∨
        x ∈ q.path.walk.support.tail := by
  change x ∈ (splicedFinitePath G M q).walk.support ↔ _
  simp only [splicedFinitePath, FinitePath.appendWalkOfDisjoint,
    FinitePath.appendWalk_support, List.mem_append,
    rightWalk_support G M q]

/-- Distinct packed quotient paths have distinct initial frontier ports. -/
theorem startPort_ne_of_packed
    (G : DWeb V) (M : G.Wave)
    {P : Set (QuotientABPath G M)}
    (hP : Bridge.DirectedIsPathPacking P)
    {q r : QuotientABPath G M} (hq : q ∈ P) (hr : r ∈ P)
    (hqr : q ≠ r) : startPort G M q ≠ startPort G M r := by
  intro hport
  have hstart : q.path.start = r.path.start :=
    congrArg Subtype.val hport
  have hd := hP hq hr hqr
  exact Set.disjoint_left.1 hd q.start_mem_supportSet
    (hstart.symm ▸ r.start_mem_supportSet)

/-- Splices of two distinct packed quotient paths are vertex-disjoint. -/
theorem splicedFinitePath_disjoint
    (G : DWeb V) (M : G.Wave)
    {P : Set (QuotientABPath G M)}
    (hP : Bridge.DirectedIsPathPacking P)
    {q r : QuotientABPath G M} (hq : q ∈ P) (hr : r ∈ P)
    (hqr : q ≠ r) :
    Disjoint (splicedFinitePath G M q).support
      (splicedFinitePath G M r).support := by
  rw [Set.disjoint_left]
  intro x hxq hxr
  rw [mem_splicedFinitePath_support_iff G M q x] at hxq
  rw [mem_splicedFinitePath_support_iff G M r x] at hxr
  rcases hxq with hxq | hxq <;> rcases hxr with hxr | hxr
  · have hports := startPort_ne_of_packed G M hP hq hr hqr
    have hd := DWeb.IsWarp.disjoint G
      (M.property.1.essentialWarpPart)
      (ConcreteSplicing.leftFinite_mem G M (startPort G M q))
      (ConcreteSplicing.leftFinite_mem G M (startPort G M r))
      (ConcreteSplicing.leftFinite_ne G M hports)
    exact Set.disjoint_left.1 hd hxq hxr
  · have hd := left_support_disjoint_right_tail G M (startPort G M q) r
    rw [rightWalk_support G M r] at hd
    exact List.disjoint_left.1 hd hxq hxr
  · have hd := left_support_disjoint_right_tail G M (startPort G M r) q
    rw [rightWalk_support G M q] at hd
    exact List.disjoint_left.1 hd hxr hxq
  · have hd := hP hq hr hqr
    exact Set.disjoint_left.1 hd
      (List.mem_of_mem_tail hxq) (List.mem_of_mem_tail hxr)

/-- The bundled original-web source--target path obtained from a quotient
packing member. -/
def splicedABPath (G : DWeb V) (M : G.Wave)
    (q : QuotientABPath G M) :
    Bridge.DirectedABPath G.graph G.source G.target where
  path := splicedFinitePath G M q
  start_mem := by
    apply M.property.2.1
    exact ⟨Sum.inl (ConcreteSplicing.leftFinite G M (startPort G M q)),
      (ConcreteSplicing.leftFinite_mem G M (startPort G M q)).1, rfl⟩
  finish_mem := by
    change q.path.finish ∈ G.target
    simpa using q.finish_mem

/-- Splice exactly the paths selected by the quotient packing. -/
def splicedFamily (G : DWeb V) (M : G.Wave)
    (P : Set (QuotientABPath G M)) :
    Set (Bridge.DirectedABPath G.graph G.source G.target) :=
  splicedABPath G M '' P

theorem splicedFamily_isPacking
    (G : DWeb V) (M : G.Wave)
    {P : Set (QuotientABPath G M)}
    (hP : Bridge.DirectedIsPathPacking P) :
    Bridge.DirectedIsPathPacking (splicedFamily G M P) := by
  rintro p ⟨q, hq, rfl⟩ r ⟨s, hs, rfl⟩ hne
  apply splicedFinitePath_disjoint G M hP hq hs
  intro hqs
  subst s
  exact hne rfl

/-- A quotient separator also separates the original source from the
original target, since every original path meets the old wave frontier and
its suffix after the last hit is a quotient path. -/
theorem separator_lift
    (G : DWeb V) (M : G.Wave) {S : Set V}
    (hS : Bridge.DirectedIsABSeparator (Quotient G M).graph
      (Quotient G M).source (Quotient G M).target S) :
    Bridge.DirectedIsABSeparator G.graph G.source G.target S := by
  intro p
  have hmeet : G.Meets p.path (Separator G M) :=
    source_subset_roof_concreteMaximalSeparator G M p.start_mem p.path
      ⟨rfl, p.finish_mem⟩
  let hwMeet : p.path.walk.Meets (Separator G M) :=
    ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
  let L := Walk.lastHit p.path.walk (Separator G M) hwMeet
  obtain ⟨q, hqstart, hqfinish, hqsupport⟩ :=
    G.exists_quotientPath_from_lastHit (Separator G M) p.path
      ⟨rfl, p.finish_mem⟩ hmeet
  let q' : QuotientABPath G M :=
    { path := q
      start_mem := by
        rw [quotient_concreteMaximalSeparator_source G M, hqstart]
        exact L.startpoint_mem
      finish_mem := by simpa [hqfinish] using p.finish_mem }
  obtain ⟨v, hvS, hvq⟩ := hS q'
  refine ⟨v, hvS, ?_⟩
  have hvL : v ∈ L.walk.support := by
    change v ∈ q.support at hvq
    rw [hqsupport] at hvq
    exact hvq
  exact L.support_subset hvL

/-- A separator vertex lying on the old prefix of one splice must be the
initial vertex of that splice's quotient path. -/
theorem eq_start_of_mem_separator_of_mem_left
    (G : DWeb V) (M : G.Wave)
    {P : Set (QuotientABPath G M)} {S : Set V}
    (horth : Bridge.DirectedIsOrthogonal P S)
    (q : QuotientABPath G M) {x : V}
    (hxS : x ∈ S)
    (hxleft : x ∈
      (ConcreteSplicing.leftFinite G M (startPort G M q)).support) :
    x = q.path.start := by
  have hxunion := horth.1 hxS
  simp only [Set.mem_iUnion] at hxunion
  obtain ⟨r, hr, hxr⟩ := hxunion
  have hxrSplit : x = r.path.start ∨ x ∈ r.path.walk.support.tail :=
    (RelationalRoof.mem_support_iff_start_or_mem_tail
      (Quotient G M).graph.Adj r.path.walk).1 hxr
  rcases hxrSplit with hxrStart | hxrTail
  · have hxC : x ∈ Separator G M := by
      rw [hxrStart]
      exact (startPort G M r).2
    have hxqStart := ConcreteSplicing.eq_separator_of_mem_left_support
      G M (startPort G M q) hxC hxleft
    simpa using hxqStart
  · have hd := left_support_disjoint_right_tail
      G M (startPort G M q) r
    rw [rightWalk_support G M r] at hd
    exact False.elim (List.disjoint_left.1 hd hxleft hxrTail)

/-- Quotient orthogonality is preserved by the partial splice. -/
theorem splicedFamily_isOrthogonal
    (G : DWeb V) (M : G.Wave)
    {P : Set (QuotientABPath G M)} {S : Set V}
    (horth : Bridge.DirectedIsOrthogonal P S) :
    Bridge.DirectedIsOrthogonal (splicedFamily G M P) S := by
  constructor
  · intro x hxS
    have hxunion := horth.1 hxS
    simp only [Set.mem_iUnion] at hxunion ⊢
    obtain ⟨q, hq, hxq⟩ := hxunion
    refine ⟨splicedABPath G M q, ⟨q, hq, rfl⟩, ?_⟩
    change x ∈ (splicedFinitePath G M q).support
    rw [mem_splicedFinitePath_support_iff G M q x]
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      (Quotient G M).graph.Adj q.path.walk).1 hxq with hxstart | hxtail
    · left
      rw [hxstart]
      change q.path.start ∈
        (ConcreteSplicing.leftFinite G M (startPort G M q)).support
      have hfinish := (ConcreteSplicing.leftFinite G M
        (startPort G M q)).finish_mem_support
      simpa [ConcreteSplicing.leftFinite_finish G M (startPort G M q)]
        using hfinish
    · exact Or.inr hxtail
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := hp
    obtain ⟨v, hv, huniq⟩ := horth.2 q hq
    refine ⟨v, ⟨hv.1, ?_⟩, ?_⟩
    · change v ∈ (splicedFinitePath G M q).support
      rw [mem_splicedFinitePath_support_iff G M q v]
      rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
        (Quotient G M).graph.Adj q.path.walk).1 hv.2 with hvstart | hvtail
      · left
        rw [hvstart]
        change q.path.start ∈
          (ConcreteSplicing.leftFinite G M (startPort G M q)).support
        have hfinish := (ConcreteSplicing.leftFinite G M
          (startPort G M q)).finish_mem_support
        simpa [ConcreteSplicing.leftFinite_finish G M (startPort G M q)]
          using hfinish
      · exact Or.inr hvtail
    · intro w hw
      apply huniq w
      refine ⟨hw.1, ?_⟩
      have hwsplice : w ∈ (splicedFinitePath G M q).support := hw.2
      rw [mem_splicedFinitePath_support_iff G M q w] at hwsplice
      rcases hwsplice with hwleft | hwtail
      · have hwstart := eq_start_of_mem_separator_of_mem_left
          G M horth q hw.1 hwleft
        rw [hwstart]
        exact q.start_mem_supportSet
      · exact List.mem_of_mem_tail hwtail

/-- Main internal-separator gluing theorem: an exact Menger conclusion in
the quotient by a wave frontier lifts to an exact Menger conclusion in the
original web.  The quotient packing need not cover the whole frontier. -/
theorem directedMengerConclusion_of_quotient
    (G : DWeb V) (M : G.Wave)
    (h : Bridge.DirectedMengerConclusion (Quotient G M).graph
      (Quotient G M).source (Quotient G M).target) :
    Bridge.DirectedMengerConclusion G.graph G.source G.target := by
  obtain ⟨P, S, hP, hsep, horth⟩ := h
  exact ⟨splicedFamily G M P, S, splicedFamily_isPacking G M hP,
    separator_lift G M hsep,
    splicedFamily_isOrthogonal G M horth⟩

#print axioms directedMengerConclusion_of_quotient

end MaximalWaveMengerLift
end AharoniBerger
end Erdos599
