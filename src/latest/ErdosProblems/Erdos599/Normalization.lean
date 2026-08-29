/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Core
import ErdosProblems.Erdos599.FiniteDeletion
import ErdosProblems.Erdos599.SafeTree

/-!
# Normalizing directed webs

This file formalizes Aharoni--Berger Assumption 2.1 and the standard
reduction to it: delete arcs entering the source side or leaving the target
side, and truncate each source--target path at its last source vertex before
its first target hit.
-/

namespace Erdos599

open Set
open DirectedPath

universe u

namespace DWeb

variable {V : Type u} {Γ : DWeb V}

/-- Source Assumption 2.1: no directed edge enters the source side and no
directed edge leaves the target side. -/
def IsNormalized (Γ : DWeb V) : Prop :=
  ∀ {x y : V}, Γ.graph.Adj x y → y ∉ Γ.source ∧ x ∉ Γ.target

/-- Delete exactly the arcs entering the source side or leaving the target
side. -/
def normalizedGraph (Γ : DWeb V) : Digraph V where
  Adj x y := Γ.graph.Adj x y ∧ y ∉ Γ.source ∧ x ∉ Γ.target

/-- The normalized web has the same vertices and distinguished sides. -/
def normalized (Γ : DWeb V) : DWeb V where
  graph := Γ.normalizedGraph
  source := Γ.source
  target := Γ.target

@[simp]
theorem normalized_adj_iff (Γ : DWeb V) (x y : V) :
    Γ.normalized.graph.Adj x y ↔
      Γ.graph.Adj x y ∧ y ∉ Γ.source ∧ x ∉ Γ.target :=
  Iff.rfl

@[simp]
theorem normalized_source (Γ : DWeb V) : Γ.normalized.source = Γ.source :=
  rfl

@[simp]
theorem normalized_target (Γ : DWeb V) : Γ.normalized.target = Γ.target :=
  rfl

theorem normalized_isNormalized (Γ : DWeb V) : Γ.normalized.IsNormalized := by
  intro x y h
  exact h.2

/-- Forget that a walk uses only normalized edges. -/
def liftNormalizedWalk : {x y : V} →
    DirectedPath.Walk Γ.normalized.graph x y →
      DirectedPath.Walk Γ.graph x y
  | _, _, .nil => .nil
  | _, _, .cons h p => .cons h.1 (liftNormalizedWalk p)

@[simp]
theorem support_liftNormalizedWalk {x y : V}
    (p : DirectedPath.Walk Γ.normalized.graph x y) :
    (liftNormalizedWalk p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftNormalizedWalk, ih]

/-- Forget that a finite path uses only normalized edges. -/
def liftNormalizedFinitePath
    (p : DirectedPath.FinitePath Γ.normalized.graph) :
    DirectedPath.FinitePath Γ.graph where
  start := p.start
  finish := p.finish
  walk := liftNormalizedWalk p.walk
  isPath := by
    change (liftNormalizedWalk p.walk).support.Nodup
    rw [support_liftNormalizedWalk]
    exact p.isPath

@[simp]
theorem support_liftNormalizedFinitePath
    (p : DirectedPath.FinitePath Γ.normalized.graph) :
    (liftNormalizedFinitePath p).support = p.support := by
  ext x
  simp only [DirectedPath.FinitePath.support, liftNormalizedFinitePath,
    support_liftNormalizedWalk]

/-- Convert a walk with no later source vertex and no earlier target vertex
to the normalized graph. -/
def normalizeWalk : {x y : V} → (p : DirectedPath.Walk Γ.graph x y) →
    (∀ {z}, z ∈ p.support.tail → z ∉ Γ.source) →
    (∀ {z}, z ∈ p.support.dropLast → z ∉ Γ.target) →
    DirectedPath.Walk Γ.normalized.graph x y
  | _, _, .nil, _, _ => .nil
  | _, _, .cons h p, hsource, htarget =>
      .cons
        ⟨h,
          hsource (by
            simp only [DirectedPath.Walk.support_cons, List.tail_cons]
            exact p.start_mem_support),
          htarget (by
            rw [DirectedPath.Walk.support_cons,
              List.dropLast_cons_of_ne_nil p.support_ne_nil]
            simp)⟩
        (normalizeWalk p
          (fun {_} hz ↦ hsource (by
            simp only [DirectedPath.Walk.support_cons, List.tail_cons]
            exact List.mem_of_mem_tail hz))
          (fun {_} hz ↦ htarget (by
            rw [DirectedPath.Walk.support_cons,
              List.dropLast_cons_of_ne_nil p.support_ne_nil]
            exact List.mem_cons_of_mem _ hz)))

@[simp]
theorem support_normalizeWalk {x y : V}
    (p : DirectedPath.Walk Γ.graph x y)
    (hsource : ∀ {z}, z ∈ p.support.tail → z ∉ Γ.source)
    (htarget : ∀ {z}, z ∈ p.support.dropLast → z ∉ Γ.target) :
    (normalizeWalk p hsource htarget).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      let hs : ∀ {z}, z ∈ p.support.tail → z ∉ Γ.source :=
        fun {_} hz ↦ hsource (by
          simp only [DirectedPath.Walk.support_cons, List.tail_cons]
          exact List.mem_of_mem_tail hz)
      let ht : ∀ {z}, z ∈ p.support.dropLast → z ∉ Γ.target :=
        fun {_} hz ↦ htarget (by
          rw [DirectedPath.Walk.support_cons,
            List.dropLast_cons_of_ne_nil p.support_ne_nil]
          exact List.mem_cons_of_mem _ hz)
      rw [normalizeWalk, DirectedPath.Walk.support_cons]
      exact congrArg (List.cons _) (ih hs ht)

/-- The canonical normalized subpath of an arbitrary finite source--target
path: begin at its last source vertex before the first target hit. -/
noncomputable def normalizeFinitePath
    (p : DirectedPath.FinitePath Γ.graph)
    (hsource : p.start ∈ Γ.source) (htarget : p.finish ∈ Γ.target) :
    DirectedPath.FinitePath Γ.normalized.graph := by
  let T := p.truncate Γ.source Γ.target hsource htarget
  exact
    { start := T.path.start
      finish := T.path.finish
      walk := normalizeWalk T.path.walk
        (fun {_} hz ↦ T.no_mem_left_after hz)
        (fun {_} hz ↦ T.no_mem_right_before hz)
      isPath := by
        change (normalizeWalk T.path.walk
          (fun {_} hz ↦ T.no_mem_left_after hz)
          (fun {_} hz ↦ T.no_mem_right_before hz)).support.Nodup
        rw [support_normalizeWalk]
        exact T.path.isPath }

@[simp]
theorem normalizeFinitePath_start_mem
    (p : DirectedPath.FinitePath Γ.graph)
    (hsource : p.start ∈ Γ.source) (htarget : p.finish ∈ Γ.target) :
    (normalizeFinitePath p hsource htarget).start ∈ Γ.normalized.source := by
  exact (p.truncate Γ.source Γ.target hsource htarget).start_mem

@[simp]
theorem normalizeFinitePath_finish_mem
    (p : DirectedPath.FinitePath Γ.graph)
    (hsource : p.start ∈ Γ.source) (htarget : p.finish ∈ Γ.target) :
    (normalizeFinitePath p hsource htarget).finish ∈ Γ.normalized.target := by
  exact (p.truncate Γ.source Γ.target hsource htarget).finish_mem

theorem normalizeFinitePath_support_subset
    (p : DirectedPath.FinitePath Γ.graph)
    (hsource : p.start ∈ Γ.source) (htarget : p.finish ∈ Γ.target) :
    (normalizeFinitePath p hsource htarget).support ⊆ p.support := by
  intro x hx
  change x ∈ (normalizeWalk
    (p.truncate Γ.source Γ.target hsource htarget).path.walk
    (fun {_} hz ↦
      (p.truncate Γ.source Γ.target hsource htarget).no_mem_left_after hz)
    (fun {_} hz ↦
      (p.truncate Γ.source Γ.target hsource htarget).no_mem_right_before hz)).support at hx
  rw [support_normalizeWalk] at hx
  exact (p.truncate Γ.source Γ.target hsource htarget).support_subset hx

/-- In a normalized web, a source vertex on a finite walk is its first
vertex. -/
theorem IsNormalized.eq_start_of_mem_walk
    (hΓ : Γ.IsNormalized) {x y z : V}
    (p : DirectedPath.Walk Γ.graph x y)
    (hzp : z ∈ p.support) (hzA : z ∈ Γ.source) : z = x := by
  induction p with
  | nil => simpa using hzp
  | @cons x y w h p ih =>
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hzp
      rcases hzp with rfl | hzp
      · rfl
      · have hzy : z = y := ih hzp
        subst z
        exact False.elim ((hΓ h).1 hzA)

/-- In a normalized web, a target vertex on a finite walk is its last
vertex. -/
theorem IsNormalized.eq_finish_of_mem_walk
    (hΓ : Γ.IsNormalized) {x y z : V}
    (p : DirectedPath.Walk Γ.graph x y)
    (hzp : z ∈ p.support) (hzB : z ∈ Γ.target) : z = y := by
  induction p with
  | nil => simpa using hzp
  | @cons x y w h p ih =>
      simp only [DirectedPath.Walk.support_cons, List.mem_cons] at hzp
      rcases hzp with rfl | hzp
      · exact False.elim ((hΓ h).2 hzB)
      · exact ih hzp

/-- A source vertex on any concrete path in a normalized web is the path's
initial vertex. -/
theorem IsNormalized.eq_initial_of_mem_path
    (hΓ : Γ.IsNormalized) (p : Γ.DPath) {z : V}
    (hzp : z ∈ p.support) (hzA : z ∈ Γ.source) : z = p.initial := by
  rcases p with p | r
  · exact hΓ.eq_start_of_mem_walk p.walk hzp hzA
  · rcases hzp with ⟨n, rfl⟩
    cases n with
    | zero => rfl
    | succ n => exact False.elim ((hΓ (r.adj_succ n)).1 hzA)

/-- A target vertex on a concrete path in a normalized web is its finite
terminal; in particular no ray contains a target vertex. -/
theorem IsNormalized.terminal?_eq_of_mem_path
    (hΓ : Γ.IsNormalized) (p : Γ.DPath) {z : V}
    (hzp : z ∈ p.support) (hzB : z ∈ Γ.target) :
    Γ.terminal? p = some z := by
  rcases p with p | r
  · have hz := hΓ.eq_finish_of_mem_walk p.walk hzp hzB
    simpa [hz]
  · rcases hzp with ⟨n, rfl⟩
    exact False.elim ((hΓ (r.adj_succ n)).2 hzB)

/-- The source endpoints of `Z` not used as source endpoints of `Y` are
entirely outside `Y`. -/
theorem initialSet_sdiff_subset_initialSet_sdiff_vertexSet
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZA : Γ.initialSet Z ⊆ Γ.source) :
    Γ.initialSet Z \ Γ.initialSet Y ⊆
      Γ.initialSet Z \ Γ.vertexSet Y := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hzY
  rcases hzY with ⟨p, hpY, hzp⟩
  apply hz.2
  exact ⟨p, hpY, (hΓ.eq_initial_of_mem_path p hzp (hZA hz.1)).symm⟩

/-- Dually, a terminal endpoint of `Z` lying on `Y` must already be a
terminal endpoint of `Y`. -/
theorem terminalFrontier_inter_vertexSet_subset
    (hΓ : Γ.IsNormalized) {Z Y : Set Γ.DPath}
    (hZB : Γ.terminalFrontier Z ⊆ Γ.target) :
    Γ.terminalFrontier Z ∩ Γ.vertexSet Y ⊆
      Γ.terminalFrontier Y := by
  intro z hz
  rcases hz.2 with ⟨p, hpY, hzp⟩
  exact ⟨p, hpY, hΓ.terminal?_eq_of_mem_path p hzp (hZB hz.1)⟩

variable {V : Type u} (Γ : DWeb V)

theorem walk_start_not_mem_tail2 {D : Digraph V} {x y : V}
    (p : Walk D x y) (hp : p.IsPath) : x ∉ p.support.tail := by
  cases p with
  | nil => simp
  | cons h p => exact hp.notMem

theorem walk_finish_not_mem_dropLast2 {D : Digraph V} {x y : V}
    (p : Walk D x y) (hp : p.IsPath) : y ∉ p.support.dropLast := by
  intro hy
  have hne := hp.rel_dropLast_getLast hy
  exact hne p.getLast_support.symm

def liftNormalizedPath (p : Γ.normalized.DPath) : Γ.DPath :=
  DirectedPath.Path.lift
    (fun {_ _} (h : Γ.normalized.graph.Adj _ _) => h.1) p

@[simp] theorem support_liftNormalizedPath (p : Γ.normalized.DPath) :
    (Γ.liftNormalizedPath p).support = p.support := by
  unfold liftNormalizedPath
  exact DirectedPath.Path.support_lift
    (fun {_ _} (h : Γ.normalized.graph.Adj _ _) => h.1) p

@[simp] theorem initial_liftNormalizedPath (p : Γ.normalized.DPath) :
    (Γ.liftNormalizedPath p).initial = p.initial := by
  rcases p with p | r <;> rfl

@[simp] theorem terminal?_liftNormalizedPath (p : Γ.normalized.DPath) :
    Γ.terminal? (Γ.liftNormalizedPath p) = Γ.normalized.terminal? p := by
  rcases p with p | r <;> rfl

def liftNormalizedFamily (W : Set Γ.normalized.DPath) : Set Γ.DPath :=
  Γ.liftNormalizedPath '' W

theorem IsWarp.liftNormalizedFamily {W : Set Γ.normalized.DPath}
    (hW : Γ.normalized.IsWarp W) :
    Γ.IsWarp (Γ.liftNormalizedFamily W) := by
  rintro p ⟨p₀, hp₀, rfl⟩ q ⟨q₀, hq₀, rfl⟩ hpq
  change Disjoint (Γ.liftNormalizedPath p₀).support
    (Γ.liftNormalizedPath q₀).support
  rw [Γ.support_liftNormalizedPath, Γ.support_liftNormalizedPath]
  apply hW hp₀ hq₀
  intro hp₀q₀
  subst q₀
  exact hpq rfl

@[simp] theorem initialSet_liftNormalizedFamily (W : Set Γ.normalized.DPath) :
    Γ.initialSet (Γ.liftNormalizedFamily W) = Γ.normalized.initialSet W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨Γ.liftNormalizedPath q, ⟨q, hq, rfl⟩, by simpa using hqx⟩

@[simp] theorem terminalFrontier_liftNormalizedFamily
    (W : Set Γ.normalized.DPath) :
    Γ.terminalFrontier (Γ.liftNormalizedFamily W) =
      Γ.normalized.terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, hpx⟩
    exact ⟨q, hq, by simpa using hpx⟩
  · rintro ⟨q, hq, hqx⟩
    exact ⟨Γ.liftNormalizedPath q, ⟨q, hq, rfl⟩, by simpa using hqx⟩

theorem IsWave.liftNormalizedFamily {W : Set Γ.normalized.DPath}
    (hW : Γ.normalized.IsWave W) :
    Γ.IsWave (Γ.liftNormalizedFamily W) := by
  refine ⟨hW.1.liftNormalizedFamily, ?_, ?_⟩
  · rw [Γ.initialSet_liftNormalizedFamily]
    simpa using hW.2.1
  · intro a ha p hp
    have hpA : p.start ∈ Γ.source := hp.1 ▸ ha
    let q := Γ.normalizeFinitePath p hpA hp.2
    have hqTarget : Γ.normalized.IsTargetPathFrom q.start q := by
      exact ⟨rfl, Γ.normalizeFinitePath_finish_mem p hpA hp.2⟩
    obtain ⟨x, hxq, hxW⟩ := hW.2.2
      (Γ.normalizeFinitePath_start_mem p hpA hp.2) q hqTarget
    refine ⟨x, Γ.normalizeFinitePath_support_subset p hpA hp.2 hxq, ?_⟩
    simpa using hxW

theorem IsUnhindered.normalized (hΓ : Γ.IsUnhindered) :
    Γ.normalized.IsUnhindered := by
  rw [Γ.normalized.isUnhindered_iff]
  intro W hW
  have hLift := (Γ.isUnhindered_iff.mp hΓ)
    (Γ.liftNormalizedFamily W) hW.liftNormalizedFamily
  simpa using hLift

private theorem sourceNormalizedMember_tail_no_source
    {U : Set Γ.DPath} (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial})
    (p : U) {z : V}
    (hz : z ∈ (Γ.finiteMemberPath U hfin p).walk.support.tail) :
    z ∉ Γ.source := by
  intro hzA
  let q := Γ.finiteMemberPath U hfin p
  have hpq : p.1 = (.inl q : Γ.DPath) :=
    Γ.finiteMemberPath_eq U hfin p
  have hzq : z ∈ q.support := List.mem_of_mem_tail hz
  have hzi := hsource p.1 p.2
    (by
      rw [hpq]
      exact ⟨hzq, hzA⟩)
  have hzi' : z = p.1.initial := by simpa using hzi
  rw [hpq] at hzi'
  have hzeq : z = q.start := hzi'
  exact walk_start_not_mem_tail2 q.walk q.isPath (hzeq ▸ hz)

private theorem waveMember_dropLast_no_target
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U) (p : U) {z : V}
    (hz : z ∈ (Γ.finiteMemberPath U hfin p).walk.support.dropLast) :
    z ∉ Γ.target := by
  intro hzB
  let q := Γ.finiteMemberPath U hfin p
  have hpq : p.1 = (.inl q : Γ.DPath) :=
    Γ.finiteMemberPath_eq U hfin p
  have hqU : (.inl q : Γ.DPath) ∈ U := by
    rw [← hpq]
    exact p.2
  have hzq : z ∈ q.support := List.mem_of_mem_dropLast hz
  have hzRoof : z ∈ Γ.roof (Γ.terminalFrontier U) :=
    (DWeb.IsWave.self_roofing (Γ := Γ) hU)
      ⟨(.inl q : Γ.DPath), hqU, hzq⟩
  have hzFrontier : z ∈ Γ.terminalFrontier U := by
    let t := FinitePath.trivial Γ.graph z
    obtain ⟨x, hxt, hxF⟩ := hzRoof t ⟨rfl, hzB⟩
    have hxz : x = z := by simpa [t] using hxt
    exact hxz ▸ hxF
  have hzFinish : z = q.finish := by
    have hzSingleton :=
      DWeb.IsWarp.finite_support_inter_terminalFrontier
        (Γ := Γ) (W := U) hU.1 (p := q) hqU
        ⟨hzq, hzFrontier⟩
    simpa using hzSingleton
  exact walk_finish_not_mem_dropLast2 q.walk q.isPath (hzFinish ▸ hz)

noncomputable def normalizeWaveMember
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial})
    (p : U) : Γ.normalized.DPath := by
  let q := Γ.finiteMemberPath U hfin p
  let hs : ∀ {z}, z ∈ q.walk.support.tail → z ∉ Γ.source :=
    fun {_} hz => Γ.sourceNormalizedMember_tail_no_source hfin hsource p hz
  let ht : ∀ {z}, z ∈ q.walk.support.dropLast → z ∉ Γ.target :=
    fun {_} hz => Γ.waveMember_dropLast_no_target hU hfin p hz
  exact .inl
    { start := q.start
      finish := q.finish
      walk := Γ.normalizeWalk q.walk hs ht
      isPath := by
        change (Γ.normalizeWalk q.walk hs ht).support.Nodup
        rw [Γ.support_normalizeWalk]
        exact q.isPath }

@[simp] theorem support_normalizeWaveMember
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial})
    (p : U) :
    (Γ.normalizeWaveMember hU hfin hsource p).support = p.1.support := by
  let q := Γ.finiteMemberPath U hfin p
  have hpq : p.1 = (.inl q : Γ.DPath) :=
    Γ.finiteMemberPath_eq U hfin p
  ext x
  change x ∈ (Γ.normalizeWalk q.walk _ _).support ↔ x ∈ p.1.support
  rw [Γ.support_normalizeWalk, hpq]
  rfl

@[simp] theorem initial_normalizeWaveMember
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial})
    (p : U) :
    (Γ.normalizeWaveMember hU hfin hsource p).initial = p.1.initial := by
  let q := Γ.finiteMemberPath U hfin p
  have hpq : p.1 = (.inl q : Γ.DPath) :=
    Γ.finiteMemberPath_eq U hfin p
  change q.start = p.1.initial
  rw [hpq]
  rfl

@[simp] theorem terminal?_normalizeWaveMember
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial})
    (p : U) :
    Γ.normalized.terminal? (Γ.normalizeWaveMember hU hfin hsource p) =
      Γ.terminal? p.1 := by
  let q := Γ.finiteMemberPath U hfin p
  have hpq : p.1 = (.inl q : Γ.DPath) :=
    Γ.finiteMemberPath_eq U hfin p
  change some q.finish = Γ.terminal? p.1
  rw [hpq]
  rfl

noncomputable def normalizeWaveFamily
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial}) :
    Set Γ.normalized.DPath :=
  Γ.normalizeWaveMember hU hfin hsource '' Set.univ

theorem IsWarp.normalizeWaveFamily
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial}) :
    Γ.normalized.IsWarp (Γ.normalizeWaveFamily hU hfin hsource) := by
  rintro _ ⟨p, _hp, rfl⟩ _ ⟨q, _hq, rfl⟩ hpq
  change Disjoint (Γ.normalizeWaveMember hU hfin hsource p).support
    (Γ.normalizeWaveMember hU hfin hsource q).support
  rw [Γ.support_normalizeWaveMember, Γ.support_normalizeWaveMember]
  apply hU.1 p.2 q.2
  intro hpqval
  have hpqsub : p = q := Subtype.ext hpqval
  exact hpq (congrArg (Γ.normalizeWaveMember hU hfin hsource) hpqsub)

@[simp] theorem initialSet_normalizeWaveFamily
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial}) :
    Γ.normalized.initialSet (Γ.normalizeWaveFamily hU hfin hsource) =
      Γ.initialSet U := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpx⟩
    exact ⟨p.1, p.2, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    let pU : U := ⟨p, hp⟩
    exact ⟨Γ.normalizeWaveMember hU hfin hsource pU,
      ⟨pU, Set.mem_univ pU, rfl⟩, by simpa using hpx⟩

@[simp] theorem terminalFrontier_normalizeWaveFamily
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial}) :
    Γ.normalized.terminalFrontier (Γ.normalizeWaveFamily hU hfin hsource) =
      Γ.terminalFrontier U := by
  ext x
  constructor
  · rintro ⟨_, ⟨p, _hp, rfl⟩, hpx⟩
    exact ⟨p.1, p.2, by simpa using hpx⟩
  · rintro ⟨p, hp, hpx⟩
    let pU : U := ⟨p, hp⟩
    exact ⟨Γ.normalizeWaveMember hU hfin hsource pU,
      ⟨pU, Set.mem_univ pU, rfl⟩, by simpa using hpx⟩

theorem IsWave.normalizeWaveFamily
    {U : Set Γ.DPath} (hU : Γ.IsWave U)
    (hfin : Γ.HasFiniteCharacter U)
    (hsource : ∀ p ∈ U, p.support ∩ Γ.source ⊆ {p.initial}) :
    Γ.normalized.IsWave (Γ.normalizeWaveFamily hU hfin hsource) := by
  refine ⟨DWeb.IsWarp.normalizeWaveFamily Γ hU hfin hsource, ?_, ?_⟩
  · rw [Γ.initialSet_normalizeWaveFamily]
    simpa using hU.2.1
  · intro a ha p hp
    let q := Γ.liftNormalizedFinitePath p
    have hqTarget : Γ.IsTargetPathFrom a q := by
      change p.start = a ∧ p.finish ∈ Γ.target
      exact ⟨hp.1, by simpa using hp.2⟩
    obtain ⟨x, hxq, hxF⟩ := hU.2.2 (by simpa using ha) q hqTarget
    refine ⟨x, ?_, ?_⟩
    · simpa [q] using hxq
    · simpa using hxF

theorem IsHindered.normalized (hΓ : Γ.IsHindered) :
    Γ.normalized.IsHindered := by
  obtain ⟨U, hU, hfin, hsource⟩ :=
    Γ.exists_source_normalized_hindrance hΓ
  refine ⟨Γ.normalizeWaveFamily hU.1 hfin hsource,
    DWeb.IsWave.normalizeWaveFamily (Γ := Γ) hU.1 hfin hsource, ?_⟩
  rw [Γ.initialSet_normalizeWaveFamily]
  simpa using hU.2

theorem IsUnhindered.of_normalized (hΓ : Γ.normalized.IsUnhindered) :
    Γ.IsUnhindered := by
  rw [Γ.isUnhindered_iff_not_isHindered]
  intro hH
  exact (Γ.normalized.isUnhindered_iff_not_isHindered.mp hΓ)
    hH.normalized

theorem isUnhindered_normalized_iff :
    Γ.normalized.IsUnhindered ↔ Γ.IsUnhindered :=
  ⟨fun h => h.of_normalized, fun h => h.normalized⟩

theorem delete_normalized (X : Set V) :
    (Γ.delete X).normalized = Γ.normalized.delete X := by
  cases Γ with
  | mk graph source target =>
      rw [DWeb.mk.injEq]
      refine ⟨?_, rfl, rfl⟩
      apply Digraph.ext
      funext u v
      apply propext
      simp only [DWeb.normalized, DWeb.normalizedGraph, DWeb.delete,
        DWeb.inducedGraph, Set.mem_compl_iff, Set.mem_sdiff]
      tauto

theorem HasSafeTargetPath.of_normalized {a : V}
    (h : Γ.normalized.HasSafeTargetPath a) : Γ.HasSafeTargetPath a := by
  obtain ⟨p, hpStart, hpTarget, hpSafe⟩ := h
  let q := Γ.liftNormalizedFinitePath p
  refine ⟨q, ?_, ?_, ?_⟩
  · exact hpStart
  · change p.finish ∈ Γ.target
    simpa using hpTarget
  · apply IsUnhindered.of_normalized
    rw [Γ.delete_normalized, Γ.support_liftNormalizedFinitePath]
    exact hpSafe
end DWeb
end Erdos599
