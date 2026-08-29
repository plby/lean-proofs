/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ConcreteWave

/-!
# Finite deletion of vertices in a web

This file contains the two finite-deletion results used in Section 6 of
Aharoni--Berger.  The small lemmas at the beginning make explicit a point
which is easy to suppress on paper: a family of paths in a deleted web has
to be transported to the original path type, and all of its warp, initial,
and terminal-frontier data have to survive that transport.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

namespace DWeb

variable {V : Type u} (Γ : DWeb V)

/-- A web is hindered when it contains a hindrance. -/
def IsHindered : Prop :=
  ∃ W : Set Γ.DPath, Γ.IsHindrance W

theorem not_isUnhindered_iff_isHindered :
    ¬ Γ.IsUnhindered ↔ Γ.IsHindered := by
  simp only [IsUnhindered, IsHindered, IsHindrance, not_not]

theorem isUnhindered_iff_not_isHindered :
    Γ.IsUnhindered ↔ ¬ Γ.IsHindered := by
  rfl

/-- Transport a whole path family from a deleted web to the original web. -/
def liftDeleteFamily (X : Set V) (W : Set (Γ.delete X).DPath) : Set Γ.DPath :=
  Γ.liftDeletePath X '' W

@[simp]
theorem mem_liftDeleteFamily_iff (X : Set V) (W : Set (Γ.delete X).DPath)
    (p : Γ.DPath) :
    p ∈ Γ.liftDeleteFamily X W ↔
      ∃ q ∈ W, Γ.liftDeletePath X q = p := by
  rfl

@[simp]
theorem terminal?_liftDeletePath (X : Set V) (p : (Γ.delete X).DPath) :
    Γ.terminal? (Γ.liftDeletePath X p) = (Γ.delete X).terminal? p := by
  rcases p with p | r <;> rfl

theorem IsWarp.liftDeleteFamily {X : Set V} {W : Set (Γ.delete X).DPath}
    (hW : (Γ.delete X).IsWarp W) :
    Γ.IsWarp (Γ.liftDeleteFamily X W) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint (Γ.liftDeletePath X p₀).support
    (Γ.liftDeletePath X q₀).support
  rw [Γ.support_liftDeletePath, Γ.support_liftDeletePath]
  apply hW hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

@[simp]
theorem initialSet_liftDeleteFamily (X : Set V)
    (W : Set (Γ.delete X).DPath) :
    Γ.initialSet (Γ.liftDeleteFamily X W) = (Γ.delete X).initialSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨Γ.liftDeletePath X q, ⟨q, hq, rfl⟩, by simpa using hqx⟩

@[simp]
theorem terminalFrontier_liftDeleteFamily (X : Set V)
    (W : Set (Γ.delete X).DPath) :
    Γ.terminalFrontier (Γ.liftDeleteFamily X W) =
      (Γ.delete X).terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨Γ.liftDeletePath X q, ⟨q, hq, rfl⟩, by simpa using hqx⟩

/-- Every lifted member of a deleted warp avoids the deleted set, provided
its initial vertex is retained. -/
theorem liftDeleteFamily_member_avoids {X : Set V}
    {W : Set (Γ.delete X).DPath} {p : Γ.DPath}
    (hp : p ∈ Γ.liftDeleteFamily X W)
    (hinitial : p.initial ∉ X) :
    Disjoint p.support X := by
  obtain ⟨q, _hq, rfl⟩ := hp
  apply Γ.liftDeletePath_avoids X q
  simpa using hinitial

/-- A lifted deletion warp uses only retained vertices when all its paths
start in the retained source. -/
theorem vertexSet_liftDeleteFamily_disjoint {X : Set V}
    {W : Set (Γ.delete X).DPath}
    (hstart : (Γ.delete X).initialSet W ⊆ (Γ.delete X).source) :
    Disjoint (Γ.vertexSet (Γ.liftDeleteFamily X W)) X := by
  apply Set.disjoint_left.2
  rintro x ⟨p, hp, hxp⟩ hxX
  have hpinitial : p.initial ∉ X := by
    obtain ⟨q, hq, rfl⟩ := hp
    have hqi : q.initial ∈ (Γ.delete X).initialSet W := ⟨q, hq, rfl⟩
    simpa using (hstart hqi).2
  exact Set.disjoint_left.1
    (Γ.liftDeleteFamily_member_avoids hp hpinitial) hxp hxX

/-- The structural part of lifting a wave out of a deleted web.  Only the
separator assertion can fail after vertices are restored. -/
theorem IsWave.liftDeleteFamily_structural {X : Set V}
    {W : Set (Γ.delete X).DPath} (hW : (Γ.delete X).IsWave W) :
    Γ.IsWarp (Γ.liftDeleteFamily X W) ∧
      Γ.initialSet (Γ.liftDeleteFamily X W) ⊆ Γ.source := by
  refine ⟨hW.1.liftDeleteFamily, ?_⟩
  rw [Γ.initialSet_liftDeleteFamily]
  exact hW.2.1.trans Set.sdiff_subset

/-- If restoring the deleted vertices does not destroy the separator, the
lifted family is a wave in the original web. -/
theorem IsWave.liftDeleteFamily
    {X : Set V} {W : Set (Γ.delete X).DPath}
    (hW : (Γ.delete X).IsWave W)
    (hsep : Γ.source ⊆
      Γ.roof ((Γ.delete X).terminalFrontier W)) :
    Γ.IsWave (Γ.liftDeleteFamily X W) := by
  refine ⟨hW.liftDeleteFamily_structural.1,
    hW.liftDeleteFamily_structural.2, ?_⟩
  simpa using hsep

/-! ## Restricting a family which already avoids the deleted vertices -/

/-- The support of a member of an avoiding family consists of retained
vertices. -/
private theorem member_support_subset_compl (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) (p : W) : p.1.support ⊆ Xᶜ := by
  intro x hxp
  exact fun hxX ↦
    Set.disjoint_left.1 havoid (Γ.mem_vertexSet.mpr ⟨p.1, p.2, hxp⟩) hxX

/-- Restrict one member of an avoiding family to the deleted graph. -/
def restrictDeleteMember (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) (p : W) : (Γ.delete X).DPath :=
  Γ.restrictDeletePath X p.1 (Γ.member_support_subset_compl X W havoid p)

@[simp]
theorem support_restrictDeleteMember (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) (p : W) :
    (Γ.restrictDeleteMember X W havoid p).support = p.1.support := by
  exact Γ.support_restrictDeletePath X p.1 _

@[simp]
theorem initial_restrictDeleteMember (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) (p : W) :
    (Γ.restrictDeleteMember X W havoid p).initial = p.1.initial := by
  exact Γ.initial_restrictDeletePath X p.1 _

@[simp]
theorem terminal?_restrictDeletePath (X : Set V) (p : Γ.DPath)
    (hretain : p.support ⊆ Xᶜ) :
    (Γ.delete X).terminal? (Γ.restrictDeletePath X p hretain) = Γ.terminal? p := by
  rcases p with p | r <;> rfl

@[simp]
theorem terminal?_restrictDeleteMember (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) (p : W) :
    (Γ.delete X).terminal? (Γ.restrictDeleteMember X W havoid p) =
      Γ.terminal? p.1 := by
  exact Γ.terminal?_restrictDeletePath X p.1 _

/-- Restrict every member of a family to the deleted graph. -/
def restrictDeleteFamily (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) : Set (Γ.delete X).DPath :=
  Γ.restrictDeleteMember X W havoid '' Set.univ

theorem IsWarp.restrictDeleteFamily {X : Set V} {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) (havoid : Disjoint (Γ.vertexSet W) X) :
    (Γ.delete X).IsWarp (Γ.restrictDeleteFamily X W havoid) := by
  rintro _ ⟨p, _hp, rfl⟩ _ ⟨q, _hq, rfl⟩ hpq
  change Disjoint
    (Γ.restrictDeleteMember X W havoid p).support
    (Γ.restrictDeleteMember X W havoid q).support
  simpa only [Γ.support_restrictDeleteMember] using
    (hW p.2 q.2 (fun hpq' ↦ hpq <| congrArg
      (Γ.restrictDeleteMember X W havoid) (Subtype.ext hpq')))

@[simp]
theorem initialSet_restrictDeleteFamily (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) :
    (Γ.delete X).initialSet (Γ.restrictDeleteFamily X W havoid) =
      Γ.initialSet W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, _hp, rfl⟩, hqx⟩
    exact ⟨p.1, p.2, by simpa using hqx⟩
  · rintro ⟨p, hp, hpx⟩
    let pW : W := ⟨p, hp⟩
    exact ⟨Γ.restrictDeleteMember X W havoid pW,
      ⟨pW, Set.mem_univ pW, rfl⟩, by simpa using hpx⟩

@[simp]
theorem terminalFrontier_restrictDeleteFamily (X : Set V) (W : Set Γ.DPath)
    (havoid : Disjoint (Γ.vertexSet W) X) :
    (Γ.delete X).terminalFrontier (Γ.restrictDeleteFamily X W havoid) =
      Γ.terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, _hp, rfl⟩, hqx⟩
    exact ⟨p.1, p.2, by simpa using hqx⟩
  · rintro ⟨p, hp, hpx⟩
    let pW : W := ⟨p, hp⟩
    exact ⟨Γ.restrictDeleteMember X W havoid pW,
      ⟨pW, Set.mem_univ pW, rfl⟩, by simpa using hpx⟩

/-- A wave which uses no deleted vertex restricts to a wave in the deleted
web.  This is the no-repair case of the finite-deletion argument. -/
theorem IsWave.restrictDeleteFamily {X : Set V} {W : Set Γ.DPath}
    (hW : Γ.IsWave W) (havoid : Disjoint (Γ.vertexSet W) X) :
    (Γ.delete X).IsWave (Γ.restrictDeleteFamily X W havoid) := by
  refine ⟨DWeb.IsWarp.restrictDeleteFamily Γ hW.1 havoid, ?_, ?_⟩
  · rw [Γ.initialSet_restrictDeleteFamily]
    intro a ha
    refine ⟨hW.2.1 ha, ?_⟩
    obtain ⟨p, hp, rfl⟩ := ha
    exact Set.disjoint_left.1 havoid
      ⟨p, hp, DirectedPath.Path.initial_mem_support p⟩
  · intro a ha p hp
    let q : DirectedPath.FinitePath Γ.graph :=
      p.lift Γ.delete_adj_imp
    have hq : Γ.IsTargetPathFrom a q := by
      exact ⟨hp.1, hp.2.1⟩
    obtain ⟨x, hxq, hxT⟩ := hW.2.2 ha.1 q hq
    refine ⟨x, ?_, ?_⟩
    · have hsupport : q.support = p.support := by
        dsimp [q]
        exact DirectedPath.FinitePath.support_lift _ p
      rw [hsupport] at hxq
      exact hxq
    · simpa using hxT

private theorem delete_source_eq_of_subset_compl {X : Set V}
    (hXA : X ⊆ Γ.sourceᶜ) : (Γ.delete X).source = Γ.source := by
  ext x
  simp only [delete_source, Set.mem_sdiff]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, fun hxX ↦ hXA hxX hx⟩

/-- No repair is required when the witnessing hindrance already avoids the
deleted set. -/
theorem IsHindrance.restrictDeleteFamily {X : Set V} {W : Set Γ.DPath}
    (hW : Γ.IsHindrance W) (havoid : Disjoint (Γ.vertexSet W) X)
    (hXA : X ⊆ Γ.sourceᶜ) :
    (Γ.delete X).IsHindrance (Γ.restrictDeleteFamily X W havoid) := by
  refine ⟨DWeb.IsWave.restrictDeleteFamily Γ hW.1 havoid, ?_⟩
  rw [Γ.initialSet_restrictDeleteFamily,
    Γ.delete_source_eq_of_subset_compl hXA]
  exact hW.2

/-! ## Finite and source-normalized hindrances -/

/-- Discarding the ray members of a hindrance preserves the hindrance.
This is the first normalization used in the finite-deletion argument: its
terminal frontier is unchanged, while its initial set can only shrink. -/
theorem IsHindrance.essentialWarpPart {W : Set Γ.DPath}
    (hW : Γ.IsHindrance W) :
    Γ.IsHindrance (Γ.essentialWarpPart W) := by
  refine ⟨hW.1.essentialWarpPart, ?_⟩
  intro heq
  apply hW.2
  apply Set.Subset.antisymm hW.1.2.1
  intro a ha
  have ha' : a ∈ Γ.initialSet (Γ.essentialWarpPart W) := by
    rw [heq]
    exact ha
  obtain ⟨p, hp, hpa⟩ := ha'
  exact ⟨p, hp.1, hpa⟩

/-- The essential part of every path family has finite character. -/
theorem hasFiniteCharacter_essentialWarpPart (W : Set Γ.DPath) :
    Γ.HasFiniteCharacter (Γ.essentialWarpPart W) := by
  intro p hp
  rcases p with p | r
  · exact ⟨p, rfl⟩
  · obtain ⟨t, ht, _⟩ := hp.2
    simp at ht

/-- The finite path underlying a member of a finite-character family. -/
noncomputable def finiteMemberPath (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W) (p : W) :
    DirectedPath.FinitePath Γ.graph :=
  Classical.choose (hfin p.2)

@[simp]
theorem finiteMemberPath_eq (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W) (p : W) :
    p.1 = .inl (Γ.finiteMemberPath W hfin p) :=
  Classical.choose_spec (hfin p.2)

/-- Replace a finite member by the suffix beginning at its last source
vertex.  This is the standard source-normalization of a warp. -/
noncomputable def sourceNormalizeMember (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) (p : W) : Γ.DPath := by
  let q := Γ.finiteMemberPath W hfin p
  have hqA : q.start ∈ Γ.source := by
    have hpA : p.1.initial ∈ Γ.source :=
      hstart ⟨p.1, p.2, rfl⟩
    rw [Γ.finiteMemberPath_eq W hfin p] at hpA
    exact hpA
  let hm : q.walk.Meets Γ.source :=
    ⟨q.start, q.start_mem_support, hqA⟩
  exact .inl (q.lastHit Γ.source hm)

/-- Source-normalize every member of a finite-character family. -/
noncomputable def sourceNormalizeFamily (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) : Set Γ.DPath :=
  Γ.sourceNormalizeMember W hfin hstart '' Set.univ

theorem support_sourceNormalizeMember_subset (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) (p : W) :
    (Γ.sourceNormalizeMember W hfin hstart p).support ⊆ p.1.support := by
  let q := Γ.finiteMemberPath W hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq W hfin p
  have hqA : q.start ∈ Γ.source := by
    have hpA : p.1.initial ∈ Γ.source := hstart ⟨p.1, p.2, rfl⟩
    rw [hpq] at hpA
    exact hpA
  let hm : q.walk.Meets Γ.source :=
    ⟨q.start, q.start_mem_support, hqA⟩
  change (q.lastHit Γ.source hm).support ⊆ p.1.support
  rw [hpq]
  exact q.lastHit_support_subset Γ.source hm

@[simp]
theorem terminal?_sourceNormalizeMember (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) (p : W) :
    Γ.terminal? (Γ.sourceNormalizeMember W hfin hstart p) =
      Γ.terminal? p.1 := by
  let q := Γ.finiteMemberPath W hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq W hfin p
  have hqA : q.start ∈ Γ.source := by
    have hpA : p.1.initial ∈ Γ.source := hstart ⟨p.1, p.2, rfl⟩
    rw [hpq] at hpA
    exact hpA
  let hm : q.walk.Meets Γ.source :=
    ⟨q.start, q.start_mem_support, hqA⟩
  change some (q.lastHit Γ.source hm).finish = Γ.terminal? p.1
  rw [hpq]
  rfl

theorem initial_sourceNormalizeMember_mem_source (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) (p : W) :
    (Γ.sourceNormalizeMember W hfin hstart p).initial ∈ Γ.source := by
  let q := Γ.finiteMemberPath W hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq W hfin p
  have hqA : q.start ∈ Γ.source := by
    have hpA : p.1.initial ∈ Γ.source := hstart ⟨p.1, p.2, rfl⟩
    rw [hpq] at hpA
    exact hpA
  let hm : q.walk.Meets Γ.source :=
    ⟨q.start, q.start_mem_support, hqA⟩
  exact q.lastHit_start_mem Γ.source hm

/-- A normalized member contains no source vertex after its initial
vertex. -/
theorem sourceNormalizeMember_source_only_initial (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) (p : W) :
    (Γ.sourceNormalizeMember W hfin hstart p).support ∩ Γ.source ⊆
      {(Γ.sourceNormalizeMember W hfin hstart p).initial} := by
  let q := Γ.finiteMemberPath W hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq W hfin p
  have hqA : q.start ∈ Γ.source := by
    have hpA : p.1.initial ∈ Γ.source := hstart ⟨p.1, p.2, rfl⟩
    rw [hpq] at hpA
    exact hpA
  let hm : q.walk.Meets Γ.source :=
    ⟨q.start, q.start_mem_support, hqA⟩
  intro x hx
  have hxsupport := hx.1
  change x ∈ (q.lastHit Γ.source hm).walk.support at hxsupport
  change x = (q.lastHit Γ.source hm).start
  rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
    Γ.graph.Adj (q.lastHit Γ.source hm).walk).1 hxsupport with h | h
  · exact h
  · exact False.elim (q.lastHit_no_mem_after Γ.source hm h hx.2)

/-- Source normalization still consists entirely of finite paths. -/
theorem hasFiniteCharacter_sourceNormalizeFamily (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) :
    Γ.HasFiniteCharacter (Γ.sourceNormalizeFamily W hfin hstart) := by
  rintro _ ⟨p, _hp, rfl⟩
  let q := Γ.finiteMemberPath W hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq W hfin p
  have hqA : q.start ∈ Γ.source := by
    have hpA : p.1.initial ∈ Γ.source := hstart ⟨p.1, p.2, rfl⟩
    rw [hpq] at hpA
    exact hpA
  let hm : q.walk.Meets Γ.source :=
    ⟨q.start, q.start_mem_support, hqA⟩
  exact ⟨q.lastHit Γ.source hm, rfl⟩

/-- A finite member of a warp meets the warp's terminal frontier only at
its own terminal vertex. -/
theorem IsWarp.finite_support_inter_terminalFrontier {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {p : DirectedPath.FinitePath Γ.graph}
    (hp : (.inl p : Γ.DPath) ∈ W) :
    p.support ∩ Γ.terminalFrontier W ⊆ {p.finish} := by
  intro x hx
  obtain ⟨q, hq, hqx⟩ := hx.2
  have hxq : x ∈ q.support := Γ.terminal_mem_support hqx
  have hpq : (.inl p : Γ.DPath) = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW hp hq hpq) hx.1 hxq
  subst q
  exact Option.some.inj hqx.symm

theorem IsWarp.sourceNormalizeFamily {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) :
    Γ.IsWarp (Γ.sourceNormalizeFamily W hfin hstart) := by
  rintro _ ⟨p, _hp, rfl⟩ _ ⟨q, _hq, rfl⟩ hpq
  have hpq' : p.1 ≠ q.1 := by
    intro heq
    have : p = q := Subtype.ext heq
    exact hpq (congrArg (Γ.sourceNormalizeMember W hfin hstart) this)
  exact (hW p.2 q.2 hpq').mono
    (Γ.support_sourceNormalizeMember_subset W hfin hstart p)
    (Γ.support_sourceNormalizeMember_subset W hfin hstart q)

@[simp]
theorem terminalFrontier_sourceNormalizeFamily (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) :
    Γ.terminalFrontier (Γ.sourceNormalizeFamily W hfin hstart) =
      Γ.terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpx⟩
    exact ⟨p.1, p.2, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    let pW : W := ⟨p, hp⟩
    exact ⟨Γ.sourceNormalizeMember W hfin hstart pW,
      ⟨pW, Set.mem_univ pW, rfl⟩, by simpa using hpx⟩

theorem initialSet_sourceNormalizeFamily_subset (W : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter W)
    (hstart : Γ.initialSet W ⊆ Γ.source) :
    Γ.initialSet (Γ.sourceNormalizeFamily W hfin hstart) ⊆
      Γ.source := by
  rintro _ ⟨_, ⟨p, _hp, rfl⟩, rfl⟩
  exact Γ.initial_sourceNormalizeMember_mem_source W hfin hstart p

theorem IsWave.sourceNormalizeFamily {W : Set Γ.DPath}
    (hW : Γ.IsWave W) (hfin : Γ.HasFiniteCharacter W) :
    Γ.IsWave (Γ.sourceNormalizeFamily W hfin hW.2.1) := by
  refine ⟨DWeb.IsWarp.sourceNormalizeFamily Γ hW.1 hfin hW.2.1,
    Γ.initialSet_sourceNormalizeFamily_subset W hfin hW.2.1, ?_⟩
  rw [Γ.terminalFrontier_sourceNormalizeFamily]
  exact hW.2.2

/-- Source normalization preserves the fact that a wave is a hindrance.
Although a last-source suffix can acquire a previously missing source as its
new initial vertex, disjointness forces that member's old initial vertex to
become missing instead. -/
theorem IsHindrance.sourceNormalizeFamily {W : Set Γ.DPath}
    (hW : Γ.IsHindrance W) (hfin : Γ.HasFiniteCharacter W) :
    Γ.IsHindrance (Γ.sourceNormalizeFamily W hfin hW.1.2.1) := by
  refine ⟨DWeb.IsWave.sourceNormalizeFamily Γ hW.1 hfin, ?_⟩
  intro hinit
  apply hW.2
  apply Set.Subset.antisymm hW.1.2.1
  intro a haA
  have haN : a ∈ Γ.initialSet
      (Γ.sourceNormalizeFamily W hfin hW.1.2.1) := by
    rw [hinit]
    exact haA
  obtain ⟨_, ⟨p, _hp, rfl⟩, hpa⟩ := haN
  have hpA : p.1.initial ∈ Γ.source :=
    hW.1.2.1 ⟨p.1, p.2, rfl⟩
  have hpN : p.1.initial ∈ Γ.initialSet
      (Γ.sourceNormalizeFamily W hfin hW.1.2.1) := by
    rw [hinit]
    exact hpA
  obtain ⟨_, ⟨q, _hq, rfl⟩, hqstart⟩ := hpN
  have hqmem : p.1.initial ∈
      (Γ.sourceNormalizeMember W hfin hW.1.2.1 q).support := by
    have hi := DirectedPath.Path.initial_mem_support
      (Γ.sourceNormalizeMember W hfin hW.1.2.1 q)
    rw [hqstart] at hi
    exact hi
  have hqorig : p.1.initial ∈ q.1.support :=
    Γ.support_sourceNormalizeMember_subset W hfin hW.1.2.1 q hqmem
  have hpq : p.1 = q.1 := by
    by_contra hpq
    exact Set.disjoint_left.1 (hW.1.1 p.2 q.2 hpq)
      (DirectedPath.Path.initial_mem_support p.1) hqorig
  have hpqsub : p = q := Subtype.ext hpq
  subst q
  exact ⟨p.1, p.2, (hpa.symm.trans hqstart).symm⟩

/-- Every hindered web has a finite-character hindrance whose members meet
the source only at their initial vertices. -/
theorem exists_source_normalized_hindrance (hΓ : Γ.IsHindered) :
    ∃ U : Set Γ.DPath,
      Γ.IsHindrance U ∧ Γ.HasFiniteCharacter U ∧
        ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial} := by
  obtain ⟨W, hW⟩ := hΓ
  let E := Γ.essentialWarpPart W
  have hE : Γ.IsHindrance E := hW.essentialWarpPart
  have hEfin : Γ.HasFiniteCharacter E :=
    Γ.hasFiniteCharacter_essentialWarpPart W
  let U := Γ.sourceNormalizeFamily E hEfin hE.1.2.1
  refine ⟨U, DWeb.IsHindrance.sourceNormalizeFamily Γ hE hEfin,
    Γ.hasFiniteCharacter_sourceNormalizeFamily E hEfin hE.1.2.1, ?_⟩
  rintro _ ⟨p, _hp, rfl⟩
  exact Γ.sourceNormalizeMember_source_only_initial E hEfin hE.1.2.1 p

/-! ## Iterated deletion -/

@[simp]
theorem delete_delete (X Y : Set V) :
    (Γ.delete X).delete Y = Γ.delete (X ∪ Y) := by
  cases Γ with
  | mk graph source target =>
      rw [DWeb.mk.injEq]
      refine ⟨?_, ?_, ?_⟩
      · apply Digraph.ext
        funext u v
        simp only [DWeb.delete, DWeb.inducedGraph, Set.mem_compl_iff,
          Set.mem_union]
        apply propext
        tauto
      · ext v
        simp only [DWeb.delete, Set.mem_sdiff, Set.mem_union]
        tauto
      · ext v
        simp only [DWeb.delete, Set.mem_sdiff, Set.mem_union]
        tauto

@[simp]
theorem delete_delete_singleton (X : Set V) (v : V) :
    (Γ.delete X).delete {v} = Γ.delete (insert v X) := by
  rw [Γ.delete_delete]
  rw [Set.union_singleton]

/-! ## Retargeting and separator composition -/

/-- Change only the target set of a web. -/
def retarget (C : Set V) : DWeb V where
  graph := Γ.graph
  source := Γ.source
  target := C

@[simp] theorem retarget_graph (C : Set V) : (Γ.retarget C).graph = Γ.graph := rfl
@[simp] theorem retarget_source (C : Set V) : (Γ.retarget C).source = Γ.source := rfl
@[simp] theorem retarget_target (C : Set V) : (Γ.retarget C).target = C := rfl

/-- A source-starting warp whose terminal frontier is the whole target is
automatically a wave. -/
theorem isWave_retarget_of_terminalFrontier_eq {C : Set V}
    {W : Set Γ.DPath} (hwarp : Γ.IsWarp W)
    (hinit : Γ.initialSet W ⊆ Γ.source)
    (hterminal : Γ.terminalFrontier W = C) :
    (Γ.retarget C).IsWave W := by
  refine ⟨hwarp, hinit, ?_⟩
  intro a _ha p hp
  refine ⟨p.finish, p.finish_mem_support, ?_⟩
  change p.finish ∈ Γ.terminalFrontier W
  rw [hterminal]
  exact hp.2

/-- Separator composition: a wave aimed at an intermediate separator is a
wave for the original target. -/
theorem IsWave.of_retarget {C : Set V} {W : Set Γ.DPath}
    (hW : (Γ.retarget C).IsWave W)
    (hC : Γ.source ⊆ Γ.roof C) : Γ.IsWave W := by
  refine ⟨hW.1, hW.2.1, ?_⟩
  intro a ha p hp
  have hpMeet : Γ.Meets p C := hC ha p hp
  let q := p.firstHit C hpMeet
  have hq : (Γ.retarget C).IsTargetPathFrom a q := by
    constructor
    · exact hp.1
    · exact p.firstHit_finish_mem C hpMeet
  obtain ⟨x, hxq, hxT⟩ := hW.2.2 ha q hq
  exact ⟨x, p.firstHit_support_subset C hpMeet hxq, hxT⟩

/-- The hindrance inequality is unchanged by retargeting, since the source
set is unchanged. -/
theorem IsHindrance.of_retarget {C : Set V} {W : Set Γ.DPath}
    (hW : (Γ.retarget C).IsHindrance W)
    (hC : Γ.source ⊆ Γ.roof C) : Γ.IsHindrance W :=
  ⟨DWeb.IsWave.of_retarget Γ hW.1 hC, hW.2⟩

/-- Restoring one non-source vertex can only add that vertex to the
separator needed by a wave in the deleted web. -/
theorem roof_terminalFrontier_union_singleton_of_delete_wave
    {v : V} {W : Set (Γ.delete {v}).DPath}
    (hW : (Γ.delete {v}).IsWave W) (hvA : v ∉ Γ.source) :
    Γ.source ⊆ Γ.roof ((Γ.delete {v}).terminalFrontier W ∪ {v}) := by
  intro a ha p hp
  by_cases hvp : v ∈ p.support
  · exact ⟨v, hvp, Set.mem_union_right _ (Set.mem_singleton v)⟩
  · have hretain : p.support ⊆ ({v} : Set V)ᶜ := by
      intro x hx hxv
      exact hvp (Set.mem_singleton_iff.mp hxv ▸ hx)
    let q : DirectedPath.FinitePath (Γ.delete {v}).graph :=
      p.restrictGraphOnSupport fun e hu hv ↦ ⟨e, hretain hu, hretain hv⟩
    have haDelete : a ∈ (Γ.delete {v}).source := by
      exact ⟨ha, fun hav ↦ hvA (Set.mem_singleton_iff.mp hav ▸ ha)⟩
    have hfinish : p.finish ∉ ({v} : Set V) := by
      intro hfv
      exact hvp (Set.mem_singleton_iff.mp hfv ▸ p.finish_mem_support)
    have hq : (Γ.delete {v}).IsTargetPathFrom a q := by
      constructor
      · exact hp.1
      · exact ⟨hp.2, hfinish⟩
    obtain ⟨x, hxq, hxT⟩ := hW.2.2 haDelete q hq
    refine ⟨x, ?_, Set.mem_union_left _ hxT⟩
    have hs : q.support = p.support := by
      unfold q
      apply DirectedPath.FinitePath.support_restrictGraphOnSupport
    rw [hs] at hxq
    exact hxq

/-! ## Prefix warps and the zero-contact augmentation case -/

/-- Cut a finite member of a path family at a specified vertex of that
member. -/
noncomputable def prefixAtMember (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (p : J) (x : V)
    (hx : x ∈ p.1.support) : Γ.DPath := by
  let q := Γ.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq J hfin p
  have hxq : x ∈ q.walk.support := by
    rw [hpq] at hx
    exact hx
  let hm : q.walk.Meets ({x} : Set V) :=
    ⟨x, hxq, Set.mem_singleton x⟩
  exact .inl (q.firstHit {x} hm)

theorem support_prefixAtMember_subset (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (p : J) (x : V)
    (hx : x ∈ p.1.support) :
    (Γ.prefixAtMember J hfin p x hx).support ⊆ p.1.support := by
  let q := Γ.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq J hfin p
  have hxq : x ∈ q.walk.support := by
    rw [hpq] at hx
    exact hx
  let hm : q.walk.Meets ({x} : Set V) :=
    ⟨x, hxq, Set.mem_singleton x⟩
  change (q.firstHit {x} hm).support ⊆ p.1.support
  rw [hpq]
  exact q.firstHit_support_subset {x} hm

@[simp]
theorem initial_prefixAtMember (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (p : J) (x : V)
    (hx : x ∈ p.1.support) :
    (Γ.prefixAtMember J hfin p x hx).initial = p.1.initial := by
  let q := Γ.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq J hfin p
  have hxq : x ∈ q.walk.support := by
    rw [hpq] at hx
    exact hx
  let hm : q.walk.Meets ({x} : Set V) :=
    ⟨x, hxq, Set.mem_singleton x⟩
  change (q.firstHit {x} hm).start = p.1.initial
  rw [hpq]
  rfl

@[simp]
theorem terminal_prefixAtMember (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (p : J) (x : V)
    (hx : x ∈ p.1.support) :
    Γ.terminal? (Γ.prefixAtMember J hfin p x hx) = some x := by
  let q := Γ.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq J hfin p
  have hxq : x ∈ q.walk.support := by
    rw [hpq] at hx
    exact hx
  let hm : q.walk.Meets ({x} : Set V) :=
    ⟨x, hxq, Set.mem_singleton x⟩
  change some (q.firstHit {x} hm).finish = some x
  congr 1
  exact Set.mem_singleton_iff.mp (q.firstHit_finish_mem {x} hm)

/-- Prefix every member at the vertex prescribed by `cut`. -/
noncomputable def prefixFamily (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (cut : J → V)
    (hcut : ∀ p, cut p ∈ p.1.support) : Set Γ.DPath :=
  (fun p ↦ Γ.prefixAtMember J hfin p (cut p) (hcut p)) '' Set.univ

theorem IsWarp.prefixFamily {J : Set Γ.DPath}
    (hJ : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    (cut : J → V) (hcut : ∀ p, cut p ∈ p.1.support) :
    Γ.IsWarp (Γ.prefixFamily J hfin cut hcut) := by
  rintro _ ⟨p, _hp, rfl⟩ _ ⟨q, _hq, rfl⟩ hpq
  have hpq' : p.1 ≠ q.1 := by
    intro heq
    have hpqSub : p = q := Subtype.ext heq
    subst q
    exact hpq rfl
  exact (hJ p.2 q.2 hpq').mono
    (Γ.support_prefixAtMember_subset J hfin p (cut p) (hcut p))
    (Γ.support_prefixAtMember_subset J hfin q (cut q) (hcut q))

@[simp]
theorem initialSet_prefixFamily (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (cut : J → V)
    (hcut : ∀ p, cut p ∈ p.1.support) :
    Γ.initialSet (Γ.prefixFamily J hfin cut hcut) =
      Γ.initialSet J := by
  ext a
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpa⟩
    exact ⟨p.1, p.2, by simpa using hpa⟩
  · rintro ⟨p, hpJ, hpa⟩
    let pJ : J := ⟨p, hpJ⟩
    refine ⟨Γ.prefixAtMember J hfin pJ (cut pJ) (hcut pJ),
      ⟨pJ, Set.mem_univ pJ, rfl⟩, ?_⟩
    simpa using hpa

@[simp]
theorem terminalFrontier_prefixFamily (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (cut : J → V)
    (hcut : ∀ p, cut p ∈ p.1.support) :
    Γ.terminalFrontier (Γ.prefixFamily J hfin cut hcut) =
      Set.range cut := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpx⟩
    have : cut p = x := Option.some.inj
      ((Γ.terminal_prefixAtMember J hfin p (cut p) (hcut p)).symm.trans hpx)
    exact ⟨p, this⟩
  · rintro ⟨p, rfl⟩
    exact ⟨Γ.prefixAtMember J hfin p (cut p) (hcut p),
      ⟨p, Set.mem_univ p, rfl⟩,
      Γ.terminal_prefixAtMember J hfin p (cut p) (hcut p)⟩

/-- If the chosen cut vertices separate the source from the target, the
prefix family is a wave. -/
theorem IsWarp.isWave_prefixFamily {J : Set Γ.DPath}
    (hJ : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    (hstart : Γ.initialSet J ⊆ Γ.source)
    (cut : J → V) (hcut : ∀ p, cut p ∈ p.1.support)
    (hsep : Γ.source ⊆ Γ.roof (Set.range cut)) :
    Γ.IsWave (Γ.prefixFamily J hfin cut hcut) := by
  refine ⟨DWeb.IsWarp.prefixFamily Γ hJ hfin cut hcut, ?_, ?_⟩
  · simpa using hstart
  · simpa using hsep

/-- The initials are unchanged, so a proper initial set makes the prefix
wave a hindrance. -/
theorem IsWarp.isHindrance_prefixFamily {J : Set Γ.DPath}
    (hJ : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    (hstart : Γ.initialSet J ⊆ Γ.source)
    (hproper : Γ.initialSet J ≠ Γ.source)
    (cut : J → V) (hcut : ∀ p, cut p ∈ p.1.support)
    (hsep : Γ.source ⊆ Γ.roof (Set.range cut)) :
    Γ.IsHindrance (Γ.prefixFamily J hfin cut hcut) := by
  refine ⟨DWeb.IsWarp.isWave_prefixFamily Γ hJ hfin hstart cut hcut hsep, ?_⟩
  simpa using hproper

/-- Inserting a finite path disjoint from a warp preserves the warp
property. -/
theorem IsWarp.insert_finite_of_disjoint {J : Set Γ.DPath}
    (hJ : Γ.IsWarp J) (q : DirectedPath.FinitePath Γ.graph)
    (hq : Disjoint q.support (Γ.vertexSet J)) :
    Γ.IsWarp (insert (.inl q : Γ.DPath) J) := by
  rintro p hp r hr hpr
  simp only [Set.mem_insert_iff] at hp hr
  rcases hp with rfl | hpJ
  · rcases hr with h | hrJ
    · exact False.elim (hpr h.symm)
    · change Disjoint q.support r.support
      rw [Set.disjoint_left]
      intro x hxq hxr
      exact Set.disjoint_left.1 hq hxq ⟨r, hrJ, hxr⟩
  · rcases hr with rfl | hrJ
    · change Disjoint p.support q.support
      rw [Set.disjoint_left]
      intro x hxp hxq
      exact Set.disjoint_left.1 hq hxq ⟨p, hpJ, hxp⟩
    · exact hJ hpJ hrJ hpr

@[simp]
theorem initialSet_insert_finite (J : Set Γ.DPath)
    (q : DirectedPath.FinitePath Γ.graph) :
    Γ.initialSet (insert (.inl q : Γ.DPath) J) =
      insert q.start (Γ.initialSet J) := by
  ext x
  simp only [mem_initialSet, Set.mem_insert_iff]
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases hp with rfl | hpJ
    · exact Or.inl hpx.symm
    · exact Or.inr ⟨p, hpJ, hpx⟩
  · rintro (rfl | ⟨p, hpJ, hpx⟩)
    · exact ⟨.inl q, Set.mem_insert _ _, rfl⟩
    · exact ⟨p, Set.mem_insert_of_mem _ hpJ, hpx⟩

@[simp]
theorem terminalFrontier_insert_finite (J : Set Γ.DPath)
    (q : DirectedPath.FinitePath Γ.graph) :
    Γ.terminalFrontier (insert (.inl q : Γ.DPath) J) =
      insert q.finish (Γ.terminalFrontier J) := by
  ext x
  simp only [mem_terminalFrontier, Set.mem_insert_iff]
  constructor
  · rintro ⟨p, hp, hpx⟩
    rcases hp with rfl | hpJ
    · exact Or.inl (Option.some.inj hpx).symm
    · exact Or.inr ⟨p, hpJ, hpx⟩
  · rintro (rfl | ⟨p, hpJ, hpx⟩)
    · exact ⟨.inl q, Set.mem_insert _ _, rfl⟩
    · exact ⟨p, Set.mem_insert_of_mem _ hpJ, hpx⟩

/-- A disjoint path performs the zero-contact augmentation. -/
theorem exists_augmented_warp_of_disjoint_path {J : Set Γ.DPath}
    (hJ : Γ.IsWarp J) (q : DirectedPath.FinitePath Γ.graph)
    (hq : Disjoint q.support (Γ.vertexSet J)) :
    ∃ J' : Set Γ.DPath,
      Γ.IsWarp J' ∧
      Γ.initialSet J' = insert q.start (Γ.initialSet J) ∧
      Γ.terminalFrontier J' =
        insert q.finish (Γ.terminalFrontier J) := by
  exact ⟨insert (.inl q : Γ.DPath) J,
    DWeb.IsWarp.insert_finite_of_disjoint Γ hJ q hq,
    Γ.initialSet_insert_finite J q,
    Γ.terminalFrontier_insert_finite J q⟩

theorem hasFiniteCharacter_insert_finite {J : Set Γ.DPath}
    (hJ : Γ.HasFiniteCharacter J)
    (q : DirectedPath.FinitePath Γ.graph) :
    Γ.HasFiniteCharacter (insert (.inl q : Γ.DPath) J) := by
  intro p hp
  rcases Set.mem_insert_iff.1 hp with rfl | hpJ
  · exact ⟨q, rfl⟩
  · exact hJ hpJ

/-- The last vertex of `R` on a finite member, defaulting to that member's
initial vertex when it does not meet `R`. -/
noncomputable def lastHitCut (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (R : Set V) (p : J) : V := by
  let q := Γ.finiteMemberPath J hfin p
  if hm : q.walk.Meets R then
    exact (q.walk.lastHit R hm).startpoint
  else
    exact q.start

theorem lastHitCut_mem_support (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (R : Set V) (p : J) :
    Γ.lastHitCut J hfin R p ∈ p.1.support := by
  let q := Γ.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq J hfin p
  rw [hpq]
  dsimp only [lastHitCut]
  split_ifs with hm
  · exact (q.walk.lastHit R hm).support_subset
      (q.walk.lastHit R hm).walk.start_mem_support
  · exact q.start_mem_support

theorem lastHitCut_mem_or_eq_initial (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (R : Set V) (p : J) :
    Γ.lastHitCut J hfin R p ∈ R ∨
      Γ.lastHitCut J hfin R p = p.1.initial := by
  let q := Γ.finiteMemberPath J hfin p
  have hpq : p.1 = .inl q := Γ.finiteMemberPath_eq J hfin p
  dsimp only [lastHitCut]
  split_ifs with hm
  · exact Or.inl (q.walk.lastHit R hm).startpoint_mem
  · apply Or.inr
    rw [hpq]
    rfl

/-- The prefix warp cut at last visits to `R`, with initial vertices used on
members which never visit `R`. -/
noncomputable def lastHitPrefixFamily (J : Set Γ.DPath)
    (hfin : Γ.HasFiniteCharacter J) (R : Set V) : Set Γ.DPath :=
  Γ.prefixFamily J hfin (Γ.lastHitCut J hfin R)
    (Γ.lastHitCut_mem_support J hfin R)

theorem IsWarp.isHindrance_lastHitPrefixFamily {J : Set Γ.DPath}
    (hJ : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    (hstart : Γ.initialSet J ⊆ Γ.source)
    (hproper : Γ.initialSet J ≠ Γ.source) (R : Set V)
    (hsep : Γ.source ⊆
      Γ.roof (Set.range (Γ.lastHitCut J hfin R))) :
    Γ.IsHindrance (Γ.lastHitPrefixFamily J hfin R) := by
  exact DWeb.IsWarp.isHindrance_prefixFamily Γ hJ hfin hstart hproper
    (Γ.lastHitCut J hfin R)
    (Γ.lastHitCut_mem_support J hfin R) hsep

/-! ## Endpoint bookkeeping for the augmenting branch -/

private theorem target_eq_insert_of_subsingleton_gap
    {J : Set Γ.DPath} {b : V}
    (hb : b ∈ Γ.target \ Γ.terminalFrontier J)
    (hgap : (Γ.target \ Γ.terminalFrontier J).Subsingleton)
    (hterminal : Γ.terminalFrontier J ⊆ Γ.target) :
    Γ.target = insert b (Γ.terminalFrontier J) := by
  apply Set.Subset.antisymm
  · intro x hx
    by_cases hxJ : x ∈ Γ.terminalFrontier J
    · exact Set.mem_insert_of_mem b hxJ
    · exact Set.mem_insert_iff.2 <| Or.inl
        (hgap ⟨hx, hxJ⟩ hb)
  · intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hxJ
    · exact hb.1
    · exact hterminal hxJ

/-- When the target deficit is at most one, an augmentation which adds its
missing endpoint covers the whole target.  If another source remains
uncovered, the augmented warp is itself a hindrance. -/
theorem IsWarp.isHindrance_of_onePointAugmentation
    {J Jplus : Set Γ.DPath} {a b a' : V}
    (hJplus : Γ.IsWarp Jplus)
    (hJstart : Γ.initialSet J ⊆ Γ.source)
    (hJterminal : Γ.terminalFrontier J ⊆ Γ.target)
    (ha : a ∈ Γ.source \ Γ.initialSet J)
    (hb : b ∈ Γ.target \ Γ.terminalFrontier J)
    (ha' : a' ∈ Γ.source \ Γ.initialSet J) (haa' : a' ≠ a)
    (hgap : (Γ.target \ Γ.terminalFrontier J).Subsingleton)
    (hinit : Γ.initialSet Jplus = insert a (Γ.initialSet J))
    (hterminal : Γ.terminalFrontier Jplus =
      insert b (Γ.terminalFrontier J)) :
    Γ.IsHindrance Jplus := by
  have htarget : Γ.target = insert b (Γ.terminalFrontier J) :=
    Γ.target_eq_insert_of_subsingleton_gap hb hgap hJterminal
  have hinitSub : Γ.initialSet Jplus ⊆ Γ.source := by
    rw [hinit]
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hxJ
    · exact ha.1
    · exact hJstart hxJ
  have htermEq : Γ.terminalFrontier Jplus = Γ.target := by
    rw [hterminal, ← htarget]
  refine ⟨⟨hJplus, hinitSub, ?_⟩, ?_⟩
  · intro x _hx p hp
    refine ⟨p.finish, p.finish_mem_support, ?_⟩
    rw [htermEq]
    exact hp.2
  · intro heq
    have ha'Init : a' ∈ Γ.initialSet Jplus := heq.symm ▸ ha'.1
    rw [hinit] at ha'Init
    rcases Set.mem_insert_iff.1 ha'Init with h | h
    · exact haa' h
    · exact ha'.2 h

/-! ## The clean finite-warp interface for the one-hole dichotomy -/

/-- Endpoint cleanliness required by the finite alternating-trail proof.
The two equalities say that a warp meets the source and target only at its
respective endpoints. -/
def IsCleanFiniteWarp (J : Set Γ.DPath) : Prop :=
  Γ.IsWarp J ∧ Γ.HasFiniteCharacter J ∧
    Γ.vertexSet J ∩ Γ.source = Γ.initialSet J ∧
    Γ.vertexSet J ∩ Γ.target = Γ.terminalFrontier J

theorem IsCleanFiniteWarp.isWarp {J : Set Γ.DPath}
    (hJ : Γ.IsCleanFiniteWarp J) : Γ.IsWarp J :=
  hJ.1

theorem IsCleanFiniteWarp.hasFiniteCharacter {J : Set Γ.DPath}
    (hJ : Γ.IsCleanFiniteWarp J) : Γ.HasFiniteCharacter J :=
  hJ.2.1

theorem IsCleanFiniteWarp.initialSet_subset_source {J : Set Γ.DPath}
    (hJ : Γ.IsCleanFiniteWarp J) : Γ.initialSet J ⊆ Γ.source := by
  rw [← hJ.2.2.1]
  exact Set.inter_subset_right

theorem IsCleanFiniteWarp.terminalFrontier_subset_target
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J) :
    Γ.terminalFrontier J ⊆ Γ.target := by
  rw [← hJ.2.2.2]
  exact Set.inter_subset_right

theorem IsCleanFiniteWarp.source_gap_disjoint_vertexSet
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J) :
    Disjoint (Γ.source \ Γ.initialSet J) (Γ.vertexSet J) := by
  rw [Set.disjoint_left]
  intro a ha hav
  exact ha.2 (by
    rw [← hJ.2.2.1]
    exact ⟨hav, ha.1⟩)

theorem IsCleanFiniteWarp.target_gap_disjoint_vertexSet
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J) :
    Disjoint (Γ.target \ Γ.terminalFrontier J) (Γ.vertexSet J) := by
  rw [Set.disjoint_left]
  intro b hb hbv
  exact hb.2 (by
    rw [← hJ.2.2.2]
    exact ⟨hbv, hb.1⟩)

theorem IsCleanFiniteWarp.initialSet_ne_source_of_gap_nonempty
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J)
    (hgap : (Γ.source \ Γ.initialSet J).Nonempty) :
    Γ.initialSet J ≠ Γ.source := by
  rintro heq
  obtain ⟨a, ha⟩ := hgap
  exact ha.2 (heq.symm ▸ ha.1)

/-- The exact augmenting output used in the one-hole theorem. -/
def IsOnePointAugmentation (J Jplus : Set Γ.DPath) : Prop :=
  ∃ a ∈ Γ.source \ Γ.initialSet J,
    ∃ b ∈ Γ.target \ Γ.terminalFrontier J,
      Γ.IsWarp Jplus ∧ Γ.HasFiniteCharacter Jplus ∧
        Γ.initialSet Jplus = insert a (Γ.initialSet J) ∧
        Γ.terminalFrontier Jplus =
          insert b (Γ.terminalFrontier J)

/-- The precise output proposition of the finite alternating-trail
dichotomy. -/
def OneHoleDichotomy (J : Set Γ.DPath) : Prop :=
  (∃ Jplus, Γ.IsOnePointAugmentation J Jplus) ∨ Γ.IsHindered

/-- Base case of the alternating search: an uncovered source--target path
which avoids the old warp can simply be inserted. -/
theorem oneHoleDichotomy_of_disjoint_gap_path
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J)
    (q : DirectedPath.FinitePath Γ.graph)
    (hqstart : q.start ∈ Γ.source \ Γ.initialSet J)
    (hqfinish : q.finish ∈ Γ.target \ Γ.terminalFrontier J)
    (hqdisjoint : Disjoint q.support (Γ.vertexSet J)) :
    Γ.OneHoleDichotomy J := by
  left
  let Jplus : Set Γ.DPath := insert (.inl q : Γ.DPath) J
  refine ⟨Jplus, q.start, hqstart, q.finish, hqfinish, ?_, ?_, ?_, ?_⟩
  · exact DWeb.IsWarp.insert_finite_of_disjoint Γ hJ.isWarp q hqdisjoint
  · exact Γ.hasFiniteCharacter_insert_finite hJ.hasFiniteCharacter q
  · exact Γ.initialSet_insert_finite J q
  · exact Γ.terminalFrontier_insert_finite J q

/-- Zero-warp base case of the one-hole dichotomy. -/
theorem oneHoleDichotomy_empty (hsource : Γ.source.Nonempty)
    (_htarget : Γ.target.Nonempty) :
    Γ.OneHoleDichotomy (∅ : Set Γ.DPath) := by
  by_cases hp : ∃ a ∈ Γ.source, ∃ q : DirectedPath.FinitePath Γ.graph,
      Γ.IsTargetPathFrom a q
  · obtain ⟨a, ha, q, hq⟩ := hp
    have hclean : Γ.IsCleanFiniteWarp (∅ : Set Γ.DPath) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [IsWarp]
      · simp [HasFiniteCharacter]
      · simp [vertexSet, initialSet]
      · simp [vertexSet, terminalFrontier]
    exact Γ.oneHoleDichotomy_of_disjoint_gap_path hclean q
      (by simpa [hq.1] using ha) (by simpa using hq.2) (by simp [vertexSet])
  · right
    refine ⟨∅, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · simp [IsWarp]
    · simp [initialSet]
    · intro a ha q hq
      exact False.elim (hp ⟨a, ha, q, hq⟩)
    · intro heq
      obtain ⟨a, ha⟩ := hsource
      have hainit : a ∈ Γ.initialSet (∅ : Set Γ.DPath) := by
        rw [heq]
        exact ha
      simpa [initialSet] using hainit

/-- If no uncovered source has any target path, the family obtained by
cutting every old member at its initial vertex is already a hindrance.  This
is the zero-step blocking branch of the alternating search. -/
theorem oneHoleDichotomy_of_no_gap_target_path
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J)
    (hsourceGap : (Γ.source \ Γ.initialSet J).Nonempty)
    (hnopath : ∀ a ∈ Γ.source \ Γ.initialSet J,
      ¬ ∃ q : DirectedPath.FinitePath Γ.graph, Γ.IsTargetPathFrom a q) :
    Γ.OneHoleDichotomy J := by
  right
  let cut : J → V := fun p ↦ p.1.initial
  have hcut : ∀ p : J, cut p ∈ p.1.support :=
    fun p ↦ DirectedPath.Path.initial_mem_support p.1
  refine ⟨Γ.prefixFamily J hJ.hasFiniteCharacter cut hcut, ?_⟩
  apply DWeb.IsWarp.isHindrance_prefixFamily Γ hJ.isWarp
    hJ.hasFiniteCharacter hJ.initialSet_subset_source
    (by
      rintro heq
      obtain ⟨a, ha⟩ := hsourceGap
      exact ha.2 (heq.symm ▸ ha.1)) cut hcut
  intro a ha q hq
  by_cases haJ : a ∈ Γ.initialSet J
  · refine ⟨a, by simpa [hq.1] using q.start_mem_support, ?_⟩
    rcases haJ with ⟨p, hpJ, hpa⟩
    refine ⟨⟨p, hpJ⟩, ?_⟩
    change p.initial = a
    exact hpa
  · exact False.elim (hnopath a ⟨ha, haJ⟩ ⟨q, hq⟩)

/-- The endpoint-counting corollary of the alternating dichotomy.  Two
uncovered sources and at most one uncovered target force a hindrance in
either branch. -/
theorem isHindered_of_oneHoleDichotomy_of_two_source_gaps
    {J : Set Γ.DPath} (hJ : Γ.IsCleanFiniteWarp J)
    (hgap : (Γ.target \ Γ.terminalFrontier J).Subsingleton)
    {a a' : V} (ha : a ∈ Γ.source \ Γ.initialSet J)
    (ha' : a' ∈ Γ.source \ Γ.initialSet J) (haa' : a' ≠ a)
    (hdichotomy : Γ.OneHoleDichotomy J) : Γ.IsHindered := by
  rcases hdichotomy with ⟨Jplus, hplus⟩ | hhindered
  · rcases hplus with ⟨c, hc, b, hb, hwarp, _hfinite, hinit, hterminal⟩
    refine ⟨Jplus, ?_⟩
    by_cases hca : c = a
    · subst c
      exact DWeb.IsWarp.isHindrance_of_onePointAugmentation Γ hwarp
        hJ.initialSet_subset_source hJ.terminalFrontier_subset_target
        hc hb ha' haa' hgap hinit hterminal
    · exact DWeb.IsWarp.isHindrance_of_onePointAugmentation Γ hwarp
        hJ.initialSet_subset_source hJ.terminalFrontier_subset_target
        hc hb ha (Ne.symm hca) hgap hinit hterminal
  · exact hhindered

/-! ## Removing one member from a finite warp -/

theorem IsWarp.eq_of_initial_eq {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {p q : Γ.DPath} (hp : p ∈ W) (hq : q ∈ W)
    (hpq : p.initial = q.initial) : p = q := by
  by_contra hne
  exact Set.disjoint_left.1 (hW hp hq hne)
    (DirectedPath.Path.initial_mem_support p)
    (hpq ▸ DirectedPath.Path.initial_mem_support q)

theorem IsWarp.eq_of_terminal_eq {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {p q : Γ.DPath} (hp : p ∈ W) (hq : q ∈ W)
    {t : V} (hpt : Γ.terminal? p = some t)
    (hqt : Γ.terminal? q = some t) : p = q := by
  by_contra hne
  exact Set.disjoint_left.1 (hW hp hq hne)
    (Γ.terminal_mem_support hpt) (Γ.terminal_mem_support hqt)

theorem IsWarp.sdiff_singleton {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) (p : Γ.DPath) :
    Γ.IsWarp (W \ {p}) := by
  intro q hq r hr hqr
  exact hW hq.1 hr.1 hqr

theorem IsWarp.initialSet_sdiff_singleton {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {p : Γ.DPath} (hp : p ∈ W) :
    Γ.initialSet (W \ {p}) = Γ.initialSet W \ {p.initial} := by
  ext a
  constructor
  · rintro ⟨q, hq, hqa⟩
    refine ⟨⟨q, hq.1, hqa⟩, ?_⟩
    intro hap
    have hinit : q.initial = p.initial := hqa.trans hap
    have hqp : q = p :=
      DWeb.IsWarp.eq_of_initial_eq Γ hW hq.1 hp hinit
    exact hq.2 (by simpa [hqp])
  · rintro ⟨⟨q, hqW, hqa⟩, hane⟩
    refine ⟨q, ⟨hqW, ?_⟩, hqa⟩
    intro hqp
    have : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    exact hane hqa.symm

theorem IsWarp.terminalFrontier_sdiff_singleton {W : Set Γ.DPath}
    (hW : Γ.IsWarp W) {p : Γ.DPath} (hp : p ∈ W)
    {t : V} (hpt : Γ.terminal? p = some t) :
    Γ.terminalFrontier (W \ {p}) = Γ.terminalFrontier W \ {t} := by
  ext x
  constructor
  · rintro ⟨q, hq, hqx⟩
    refine ⟨⟨q, hq.1, hqx⟩, ?_⟩
    intro hxt
    have hxt' : x = t := Set.mem_singleton_iff.mp hxt
    have hqt : Γ.terminal? q = some t := by simpa [hxt'] using hqx
    have hqp : q = p :=
      DWeb.IsWarp.eq_of_terminal_eq Γ hW hq.1 hp hqt hpt
    exact hq.2 (by simpa [hqp])
  · rintro ⟨⟨q, hqW, hqx⟩, hxne⟩
    refine ⟨q, ⟨hqW, ?_⟩, hqx⟩
    intro hqp
    have : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    have htx : t = x := Option.some.inj (hpt.symm.trans hqx)
    exact hxne (Set.mem_singleton_iff.2 htx.symm)

theorem hasFiniteCharacter_sdiff_singleton {W : Set Γ.DPath}
    (hW : Γ.HasFiniteCharacter W) (p : Γ.DPath) :
    Γ.HasFiniteCharacter (W \ {p}) := by
  intro q hq
  exact hW hq.1

theorem IsWarp.vertexSet_sdiff_singleton_disjoint_singleton
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) {p : Γ.DPath}
    (hp : p ∈ W) {v : V} (hvp : v ∈ p.support) :
    Disjoint (Γ.vertexSet (W \ {p})) ({v} : Set V) := by
  rw [Set.disjoint_left]
  rintro x ⟨q, hq, hxq⟩ hxv
  have hxv' : x = v := Set.mem_singleton_iff.mp hxv
  subst x
  have hqp : q = p := by
    by_contra hne
    exact Set.disjoint_left.1 (hW hq.1 hp hne) hxq hvp
  exact hq.2 (Set.mem_singleton_iff.2 hqp)

/-- Remove the unique member through `v` and restrict every remaining
member to the vertex-deleted graph. -/
noncomputable def eraseMemberRestrictFamily
    (W : Set Γ.DPath) (hW : Γ.IsWarp W) (p : W) {v : V}
    (hvp : v ∈ p.1.support) : Set (Γ.delete {v}).DPath :=
  let J := W \ {p.1}
  let havoid : Disjoint (Γ.vertexSet J) ({v} : Set V) :=
    DWeb.IsWarp.vertexSet_sdiff_singleton_disjoint_singleton Γ hW p.2 hvp
  Γ.restrictDeleteFamily {v} J havoid

theorem IsWarp.eraseMemberRestrictFamily
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) (p : W) {v : V}
    (hvp : v ∈ p.1.support) :
    (Γ.delete {v}).IsWarp
      (Γ.eraseMemberRestrictFamily W hW p hvp) := by
  let J := W \ {p.1}
  let havoid : Disjoint (Γ.vertexSet J) ({v} : Set V) :=
    DWeb.IsWarp.vertexSet_sdiff_singleton_disjoint_singleton Γ hW p.2 hvp
  exact DWeb.IsWarp.restrictDeleteFamily Γ
    (DWeb.IsWarp.sdiff_singleton Γ hW p.1) havoid

@[simp]
theorem initialSet_eraseMemberRestrictFamily
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) (p : W) {v : V}
    (hvp : v ∈ p.1.support) :
    (Γ.delete {v}).initialSet
      (Γ.eraseMemberRestrictFamily W hW p hvp) =
      Γ.initialSet W \ {p.1.initial} := by
  let J := W \ {p.1}
  let havoid : Disjoint (Γ.vertexSet J) ({v} : Set V) :=
    DWeb.IsWarp.vertexSet_sdiff_singleton_disjoint_singleton Γ hW p.2 hvp
  change (Γ.delete {v}).initialSet
    (Γ.restrictDeleteFamily {v} J havoid) = _
  rw [Γ.initialSet_restrictDeleteFamily]
  exact DWeb.IsWarp.initialSet_sdiff_singleton Γ hW p.2

@[simp]
theorem terminalFrontier_eraseMemberRestrictFamily
    {W : Set Γ.DPath} (hW : Γ.IsWarp W) (p : W) {v t : V}
    (hvp : v ∈ p.1.support) (hpt : Γ.terminal? p.1 = some t) :
    (Γ.delete {v}).terminalFrontier
      (Γ.eraseMemberRestrictFamily W hW p hvp) =
      Γ.terminalFrontier W \ {t} := by
  let J := W \ {p.1}
  let havoid : Disjoint (Γ.vertexSet J) ({v} : Set V) :=
    DWeb.IsWarp.vertexSet_sdiff_singleton_disjoint_singleton Γ hW p.2 hvp
  change (Γ.delete {v}).terminalFrontier
    (Γ.restrictDeleteFamily {v} J havoid) = _
  rw [Γ.terminalFrontier_restrictDeleteFamily]
  exact DWeb.IsWarp.terminalFrontier_sdiff_singleton Γ hW p.2 hpt

/-! ## Finite-character and endpoint-purity transport -/

theorem fd_avoids_sdiff_member {Z : Set Γ.DPath}
    (hZ : Γ.IsWarp Z) {p : Γ.DPath} (hp : p ∈ Z)
    {v : V} (hvp : v ∈ p.support) :
    Disjoint (Γ.vertexSet (Z \ {p})) {v} := by
  rw [Set.disjoint_singleton_right]
  rintro ⟨q, hq, hvq⟩
  apply hq.2
  by_contra hqp
  exact Set.disjoint_left.1 (hZ hq.1 hp hqp) hvq hvp

theorem fd_hasFiniteCharacter_restrictDeleteFamily {X : Set V}
    {Z : Set Γ.DPath} (hfin : Γ.HasFiniteCharacter Z)
    (havoid : Disjoint (Γ.vertexSet Z) X) :
    (Γ.delete X).HasFiniteCharacter
      (Γ.restrictDeleteFamily X Z havoid) := by
  rintro _ ⟨⟨p, hpZ⟩, _hp, rfl⟩
  rcases p with q | r
  · refine ⟨q.restrictGraphOnSupport ?_, rfl⟩
    intro x y hxy hx hy
    refine ⟨hxy, ?_, ?_⟩
    · exact fun hxX ↦ Set.disjoint_left.1 havoid
        ⟨.inl q, hpZ, hx⟩ hxX
    · exact fun hyX ↦ Set.disjoint_left.1 havoid
        ⟨.inl q, hpZ, hy⟩ hyX
  · obtain ⟨q, hq⟩ := hfin hpZ
    simp at hq

theorem fd_source_clean_restrictDeleteFamily {X : Set V}
    {Z : Set Γ.DPath} (havoid : Disjoint (Γ.vertexSet Z) X)
    (hXA : X ⊆ Γ.sourceᶜ)
    (hclean : ∀ p ∈ Z, p.support ∩ Γ.source ⊆ {p.initial}) :
    ∀ q ∈ Γ.restrictDeleteFamily X Z havoid,
      q.support ∩ (Γ.delete X).source ⊆ {q.initial} := by
  rintro _ ⟨p, _hp, rfl⟩ x hx
  have hx' : x ∈ p.1.support ∩ Γ.source := by
    refine ⟨?_, hx.2.1⟩
    simpa using hx.1
  have := hclean p.1 p.2 hx'
  simpa using this

theorem fd_isCleanFiniteWarp_of_endpoint_clean {J : Set Γ.DPath}
    (hwarp : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    (hinit : Γ.initialSet J ⊆ Γ.source)
    (hsource : ∀ p ∈ J, p.support ∩ Γ.source ⊆ {p.initial})
    (hterminal : Γ.terminalFrontier J ⊆ Γ.target)
    (htarget : ∀ p ∈ J, ∀ {x : V}, x ∈ p.support → x ∈ Γ.target →
      Γ.terminal? p = some x) :
    Γ.IsCleanFiniteWarp J := by
  refine ⟨hwarp, hfin, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hp, hxp⟩, hxA⟩
      have hx := hsource p hp ⟨hxp, hxA⟩
      exact ⟨p, hp, (Set.mem_singleton_iff.mp hx).symm⟩
    · rintro x ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp, p.initial_mem_support⟩, hinit ⟨p, hp, rfl⟩⟩
  · apply Set.Subset.antisymm
    · rintro x ⟨⟨p, hp, hxp⟩, hxB⟩
      exact ⟨p, hp, htarget p hp hxp hxB⟩
    · rintro x ⟨p, hp, hpx⟩
      exact ⟨⟨p, hp, Γ.terminal_mem_support hpx⟩,
        hterminal ⟨p, hp, hpx⟩⟩

theorem fd_delete_roof_frontier_sdiff {X : Set V} {U : Set Γ.DPath}
    (hU : Γ.IsWave U) :
    (Γ.delete X).source ⊆
      (Γ.delete X).roof (Γ.terminalFrontier U \ X) := by
  intro a ha p hp
  let q : DirectedPath.FinitePath Γ.graph := p.lift Γ.delete_adj_imp
  have hq : Γ.IsTargetPathFrom a q := ⟨hp.1, hp.2.1⟩
  obtain ⟨x, hxq, hxS⟩ := hU.2.2 ha.1 q hq
  have haX : a ∉ X := ha.2
  have havoid : Disjoint q.support X := by
    change Disjoint (Γ.liftDeletePath X (.inl p)).support X
    apply Γ.liftDeletePath_avoids X (.inl p)
    change p.start ∉ X
    rw [hp.1]
    exact haX
  have hxnot : x ∉ X := fun hxX ↦ Set.disjoint_left.1 havoid hxq hxX
  refine ⟨x, ?_, ⟨hxS, hxnot⟩⟩
  simpa [q] using hxq

theorem fd_terminal_eq_of_mem_support_frontier {J : Set Γ.DPath}
    (hwarp : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    {p : Γ.DPath} (hp : p ∈ J) {x : V} (hxp : x ∈ p.support)
    (hxT : x ∈ Γ.terminalFrontier J) :
    Γ.terminal? p = some x := by
  obtain ⟨q, hpq⟩ := hfin hp
  rw [hpq] at hp hxp ⊢
  have hx := DWeb.IsWarp.finite_support_inter_terminalFrontier
    Γ hwarp hp ⟨hxp, hxT⟩
  exact congrArg some (Set.mem_singleton_iff.mp hx).symm

theorem fd_isCleanFiniteWarp_of_single_target_gap {J : Set Γ.DPath}
    (hwarp : Γ.IsWarp J) (hfin : Γ.HasFiniteCharacter J)
    (hinit : Γ.initialSet J ⊆ Γ.source)
    (hsource : ∀ p ∈ J, p.support ∩ Γ.source ⊆ {p.initial})
    {b : V} (hb : b ∉ Γ.vertexSet J)
    (htarget : Γ.target = insert b (Γ.terminalFrontier J)) :
    Γ.IsCleanFiniteWarp J := by
  apply fd_isCleanFiniteWarp_of_endpoint_clean Γ hwarp hfin hinit hsource
  · rw [htarget]
    exact Set.subset_insert _ _
  · intro p hp x hxp hxT
    rw [htarget] at hxT
    rcases Set.mem_insert_iff.1 hxT with rfl | hxfront
    · exact False.elim (hb ⟨p, hp, hxp⟩)
    · exact fd_terminal_eq_of_mem_support_frontier
        Γ hwarp hfin hp hxp hxfront

theorem fd_hasFiniteCharacter_liftDeleteFamily {X : Set V}
    {U : Set (Γ.delete X).DPath}
    (hfin : (Γ.delete X).HasFiniteCharacter U) :
    Γ.HasFiniteCharacter (Γ.liftDeleteFamily X U) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hpq⟩ := hfin hp
  rw [hpq]
  exact ⟨q.lift Γ.delete_adj_imp, rfl⟩

theorem fd_source_clean_liftDeleteFamily {X : Set V}
    {U : Set (Γ.delete X).DPath}
    (hclean : ∀ p ∈ U,
      p.support ∩ (Γ.delete X).source ⊆ {p.initial})
    (hXA : X ⊆ Γ.sourceᶜ) :
    ∀ p ∈ Γ.liftDeleteFamily X U,
      p.support ∩ Γ.source ⊆ {p.initial} := by
  rintro _ ⟨q, hq, rfl⟩ x hx
  have hsourceEq : (Γ.delete X).source = Γ.source := by
    ext y
    simp only [DWeb.delete_source, Set.mem_sdiff]
    constructor
    · exact fun hy ↦ hy.1
    · intro hy
      exact ⟨hy, fun hyX ↦ hXA hyX hy⟩
  have hx' : x ∈ q.support ∩ (Γ.delete X).source := by
    rw [hsourceEq]
    simpa using hx
  have := hclean q hq hx'
  simpa using this

theorem fd_delete_source_eq_of_not_mem {v : V} (hv : v ∉ Γ.source) :
    (Γ.delete {v}).source = Γ.source := by
  ext x
  simp only [DWeb.delete_source, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · exact fun hx ↦ hx.1
  · intro hx
    exact ⟨hx, fun hxv ↦ hv (hxv ▸ hx)⟩

end DWeb

end Erdos599
