/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ConcreteWave
import ErdosProblems.Erdos599.EssentialWaveLift
import ErdosProblems.Erdos599.IteratedArrow
import ErdosProblems.Erdos599.LadderBookkeeping
import ErdosProblems.Erdos599.RoofQuotient
import ErdosProblems.Erdos599.Stationary
import ErdosProblems.Erdos599.WarpLimits
import ErdosProblems.Erdos599.WaveLimits

/-!
# Transfinite ladder bookkeeping for Erdős Problem 599

This file contains the ordinal and stationary-set part of the
Aharoni--Berger ladder construction.  The graph-theoretic construction
produces, at each ordinal stage, a set of paths which have just become
inessential.  The bookkeeping below chooses at most one previously
unrecorded path, preferring a ray whenever one is available.

Keeping this layer independent of the representation of paths has two
advantages.  First, the off-by-one convention is explicit:
`inessentialNext α` is the inessential part of the *successor* warp
`Y_(α+1)`.  Second, the stationary argument separating grounded and
hanging records depends only on the injective regressive provenance map,
not on any graph operation.

The definitions here correspond to the bookkeeping in Section 7 of
Aharoni--Berger.  In particular, `recordedBefore B α` is their
`ℓᵃℓ H_α`, `phi B` is `Φ(ℓᵃℓ L)`, and
`phiInfinite B` is `Φ_∞(ℓᵃℓ L)`.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Ladder

universe u v

/-- The stages of a `κ`-ladder, represented by ordinals below the initial
ordinal of `κ`. -/
abbrev Stage (κ : Cardinal.{u}) := Stationary.Below κ

/-- Stages through and including the final stage `κ`. -/
abbrev ExtendedStage (κ : Cardinal.{u}) :=
  {a : Ordinal.{u} // a ≤ κ.ord}

/-- Include an ordinary ladder stage among the extended stages. -/
def Stage.toExtended (a : Stage κ) : ExtendedStage κ :=
  ⟨a.1, le_of_lt a.2⟩

/-- The successor of an ordinary stage, as an extended stage.  This is
defined even before assuming that `κ` is infinite. -/
def Stage.succExtended (a : Stage κ) : ExtendedStage κ :=
  ⟨a.1 + 1, (Order.add_one_le_iff).2 a.2⟩

/-- The last extended stage. -/
def finalStage (κ : Cardinal.{u}) : ExtendedStage κ :=
  ⟨κ.ord, le_rfl⟩

/-- The initial extended stage. -/
def zeroStage (κ : Cardinal.{u}) : ExtendedStage κ :=
  ⟨0, bot_le⟩

/-! ## One-record-per-stage bookkeeping -/

/-- The data on which the Section 7 bookkeeping operates.

`inessentialNext α` is deliberately successor-normalized: it denotes the
paths in `IE(Y_(α+1))`, rather than in `IE(Y_α)`.  This removes the
off-by-one ambiguity in the printed definition of the emergence ordinal.
The structure contains data only; the conditions saying that `chosen`
really makes the prescribed choice are in `IsValid`. -/
structure Bookkeeping (κ : Cardinal.{u}) (Path : Type v) where
  /-- Paths which are inessential in the successor warp at a stage. -/
  inessentialNext : Stage κ → Set Path
  /-- The predicate distinguishing rays from finite paths. -/
  isRay : Path → Prop
  /-- The optional path recorded at a stage. -/
  chosen : Stage κ → Option Path

variable {κ : Cardinal.{u}} {Path : Type v}

namespace Bookkeeping

/-- A path was selected at a strictly earlier stage. -/
def recordedBefore (B : Bookkeeping κ Path) (α : Stage κ) : Set Path :=
  {p | ∃ β : Stage κ, β < α ∧ B.chosen β = some p}

/-- The paths eligible for selection at a stage. -/
def available (B : Bookkeeping κ Path) (α : Stage κ) : Set Path :=
  B.inessentialNext α \ B.recordedBefore α

/-- The obstruction stages: at least one path is available. -/
def phi (B : Bookkeeping κ Path) : Set (Stage κ) :=
  {α | (B.available α).Nonempty}

/-- Obstruction stages at which an unrecorded ray is available. -/
def phiInfinite (B : Bookkeeping κ Path) : Set (Stage κ) :=
  {α | α ∈ B.phi ∧ ∃ p ∈ B.available α, B.isRay p}

/-- Obstruction stages at which no unrecorded ray is available. -/
def phiFinite (B : Bookkeeping κ Path) : Set (Stage κ) :=
  B.phi \ B.phiInfinite

/-- The bookkeeping rule at one stage: choose exactly when the available
set is nonempty, choose from that set, and prefer a ray if one is
available. -/
def IsValidAt (B : Bookkeeping κ Path) (α : Stage κ) : Prop :=
  ((B.available α).Nonempty →
      ∃ p, B.chosen α = some p ∧ p ∈ B.available α ∧
        ((∃ q ∈ B.available α, B.isRay q) → B.isRay p)) ∧
    ∀ p, B.chosen α = some p → p ∈ B.available α

/-- The choice rule holds at every stage. -/
def IsValid (B : Bookkeeping κ Path) : Prop :=
  ∀ α, B.IsValidAt α

@[simp]
theorem mem_recordedBefore {B : Bookkeeping κ Path} {α : Stage κ} {p : Path} :
    p ∈ B.recordedBefore α ↔
      ∃ β : Stage κ, β < α ∧ B.chosen β = some p :=
  Iff.rfl

@[simp]
theorem mem_available {B : Bookkeeping κ Path} {α : Stage κ} {p : Path} :
    p ∈ B.available α ↔
      p ∈ B.inessentialNext α ∧ p ∉ B.recordedBefore α :=
  Iff.rfl

@[simp]
theorem mem_phi {B : Bookkeeping κ Path} {α : Stage κ} :
    α ∈ B.phi ↔ (B.available α).Nonempty :=
  Iff.rfl

@[simp]
theorem mem_phiInfinite {B : Bookkeeping κ Path} {α : Stage κ} :
    α ∈ B.phiInfinite ↔
      α ∈ B.phi ∧ ∃ p ∈ B.available α, B.isRay p :=
  Iff.rfl

@[simp]
theorem mem_phiFinite {B : Bookkeeping κ Path} {α : Stage κ} :
    α ∈ B.phiFinite ↔ α ∈ B.phi ∧ α ∉ B.phiInfinite :=
  Iff.rfl

theorem recordedBefore_mono (B : Bookkeeping κ Path) {α β : Stage κ}
    (hαβ : α ≤ β) :
    B.recordedBefore α ⊆ B.recordedBefore β := by
  rintro p ⟨γ, hγα, hp⟩
  exact ⟨γ, hγα.trans_le hαβ, hp⟩

theorem chosen_mem_available (B : Bookkeeping κ Path) (hB : B.IsValid)
    {α : Stage κ} {p : Path} (hp : B.chosen α = some p) :
    p ∈ B.available α :=
  (hB α).2 p hp

theorem chosen_not_mem_recordedBefore (B : Bookkeeping κ Path) (hB : B.IsValid)
    {α : Stage κ} {p : Path} (hp : B.chosen α = some p) :
    p ∉ B.recordedBefore α :=
  (B.chosen_mem_available hB hp).2

theorem mem_phi_iff_exists_chosen (B : Bookkeeping κ Path) (hB : B.IsValid)
    {α : Stage κ} :
    α ∈ B.phi ↔ ∃ p, B.chosen α = some p := by
  constructor
  · intro hα
    obtain ⟨p, hp, -⟩ := (hB α).1 hα
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, B.chosen_mem_available hB hp⟩

theorem chosen_stage_unique (B : Bookkeeping κ Path) (hB : B.IsValid)
    {α β : Stage κ} {p : Path}
    (hp : B.chosen α = some p) (hq : B.chosen β = some p) :
    α = β := by
  rcases lt_trichotomy α β with hlt | he | hgt
  · exact False.elim <| B.chosen_not_mem_recordedBefore hB hq ⟨α, hlt, hp⟩
  · exact he
  · exact False.elim <| B.chosen_not_mem_recordedBefore hB hp ⟨β, hgt, hq⟩

/-- The graph-theoretic content of source Lemma 7.4, isolated as a property
of the successor-normalized bookkeeping data.  The concrete ladder proves
this property by induction through arrow successors and liminf limits. -/
def IsPersistent (B : Bookkeeping κ Path) : Prop :=
  ∀ α p, B.chosen α = some p →
    ∀ β, α ≤ β → p ∈ B.inessentialNext β

/-- Once a path has been recorded, persistence puts it in the inessential
part at every later stage (source Lemma 7.4, bookkeeping form). -/
theorem recorded_mem_inessentialNext (B : Bookkeeping κ Path)
    (hpers : B.IsPersistent) {α β : Stage κ} {p : Path}
    (hp : B.chosen α = some p) (hαβ : α ≤ β) :
    p ∈ B.inessentialNext β :=
  hpers α p hp β hαβ

theorem recordedBefore_subset_inessentialNext (B : Bookkeeping κ Path)
    (hpers : B.IsPersistent) (α : Stage κ) :
    B.recordedBefore α ⊆ B.inessentialNext α := by
  rintro p ⟨β, hβα, hp⟩
  exact hpers β p hp α hβα.le

/-- The priority rule records a ray at every `Φ_∞` stage. -/
theorem chosen_isRay_of_mem_phiInfinite (B : Bookkeeping κ Path)
    (hB : B.IsValid) {α : Stage κ} (hα : α ∈ B.phiInfinite) :
    ∃ p, B.chosen α = some p ∧ B.isRay p := by
  obtain ⟨p, hp, _hpavail, hpref⟩ := (hB α).1 hα.1
  exact ⟨p, hp, hpref hα.2⟩

end Bookkeeping

/-! ## Concrete ladder data -/

end Ladder

namespace DirectedPath

/-! ## Directed-edge observables under path limits -/

variable {V : Type u} {D : Digraph V}

theorem Walk.mem_edgeSet_iff_exists_getElem {a b : V}
    (p : Walk D a b) (e : V × V) :
    e ∈ p.edgeSet ↔
      ∃ n, ∃ hn : n + 1 < p.support.length,
        e = (p.support[n], p.support[n + 1]) := by
  induction p generalizing e with
  | nil => simp
  | @cons a c b h p ih =>
      constructor
      · intro he
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at he
        rcases he with rfl | he
        · refine ⟨0, ?_, ?_⟩
          · have hpos : 0 < p.support.length :=
              List.length_pos_iff.mpr p.support_ne_nil
            simp only [Walk.support_cons, List.length_cons]
            omega
          · have hpos : 0 < p.support.length :=
              List.length_pos_iff.mpr p.support_ne_nil
            have hp0 : p.support[0]'hpos = c := by
              calc
                p.support[0]'hpos = p.support.head p.support_ne_nil :=
                  List.getElem_zero hpos
                _ = c := p.head_support
            simp [hp0]
        · obtain ⟨n, hn, rfl⟩ := (ih e).1 he
          refine ⟨n + 1, ?_, ?_⟩
          · simpa [Nat.add_assoc] using Nat.succ_lt_succ hn
          · simp only [Walk.support_cons, List.getElem_cons_succ]
      · rintro ⟨n, hn, rfl⟩
        cases n with
        | zero =>
            left
            have hpos : 0 < p.support.length :=
              List.length_pos_iff.mpr p.support_ne_nil
            have hp0 : p.support[0]'hpos = c := by
              calc
                p.support[0]'hpos = p.support.head p.support_ne_nil :=
                  List.getElem_zero hpos
                _ = c := p.head_support
            simp [hp0]
        | succ n =>
            right
            apply (ih _).2
            refine ⟨n, ?_, ?_⟩
            · simp only [Walk.support_cons, List.length_cons] at hn
              omega
            · simp only [Walk.support_cons, List.getElem_cons_succ]

theorem Walk.edgeSet_subset_ray_of_getElem_eq {a b : V}
    (p : Walk D a b) (r : Ray D)
    (h : ∀ n (hn : n < p.support.length), p.support[n] = r n) :
    p.edgeSet ⊆ r.edgeSet := by
  intro e he
  obtain ⟨n, hn, rfl⟩ := (p.mem_edgeSet_iff_exists_getElem _).1 he
  exact ⟨n, by rw [h n (lt_trans (Nat.lt_succ_self n) hn), h (n + 1) hn]⟩

theorem FinitePath.edgeSet_subset_ray {p : FinitePath D} {r : Ray D}
    (h : p.IsInitialSegmentOf r) : p.edgeSet ⊆ r.edgeSet :=
  p.walk.edgeSet_subset_ray_of_getElem_eq r h

/-- Directed edges are monotone under forward path extension. -/
theorem Path.edgeSet_mono_of_extends {p q : Path D} (h : Extends p q) :
    p.edgeSet ⊆ q.edgeSet := by
  rcases p with p | r <;> rcases q with q | s
  · exact p.walk.edgeSet_subset_of_support_prefix q.walk h
  · exact p.edgeSet_subset_ray h
  · exact False.elim h
  · subst s
    exact Set.Subset.rfl

theorem FinitePath.lt_length_of_prefix_mem_getElem {p q : FinitePath D}
    (hpq : p.IsPrefixOf q) (n : ℕ) (hnq : n < q.walk.support.length)
    (hnp : q.walk.support[n] ∈ p.support) :
    n < p.walk.support.length := by
  change q.walk.support[n] ∈ p.walk.support at hnp
  obtain ⟨m, hm, hmn⟩ := List.mem_iff_getElem.mp hnp
  have hmq : m < q.walk.support.length :=
    lt_of_lt_of_le hm hpq.length_le
  have heq : q.walk.support[m] = q.walk.support[n] := by
    calc
      q.walk.support[m]'hmq = p.walk.support[m] := (hpq.getElem hm).symm
      _ = q.walk.support[n] := hmn
  have hmnIndex : m = n := q.isPath.getElem_inj_iff.mp heq
  simpa [hmnIndex] using hm

theorem FinitePath.lt_length_of_initialSegment_mem {p : FinitePath D}
    {r : Ray D} (hpr : p.IsInitialSegmentOf r) (n : ℕ)
    (hnp : r n ∈ p.support) : n < p.walk.support.length := by
  change r n ∈ p.walk.support at hnp
  obtain ⟨m, hm, hmn⟩ := List.mem_iff_getElem.mp hnp
  have heq : r m = r n := by
    calc
      r m = p.walk.support[m] := (hpr m hm).symm
      _ = r n := hmn
  have hmnIndex : m = n := r.injective heq
  simpa [hmnIndex] using hm

/-- The edge set of a path-chain limit is the union of the edge sets of
the chain members. -/
theorem Path.edgeSet_chainLimit
    (C : Set (Path D)) (hCne : C.Nonempty) (hC : IsChain Extends C) :
    (chainLimit C hCne hC).edgeSet = ⋃ p ∈ C, p.edgeSet := by
  apply Set.Subset.antisymm
  · intro e he
    have hsupport := support_chainLimit C hCne hC
    generalize hq : chainLimit C hCne hC = q at he hsupport
    rcases q with q | r
    · obtain ⟨n, hn, rfl⟩ :=
        (q.walk.mem_edgeSet_iff_exists_getElem _).1 he
      have hx : q.walk.support[n + 1] ∈
          Path.support (Sum.inl q : Path D) := by
        exact List.getElem_mem hn
      rw [hsupport] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨p, hpC, hxp⟩ := hx
      have hpq : Extends p (.inl q) := by
        rw [← hq]
        exact extends_chainLimit C hCne hC hpC
      rcases p with p | s
      · have hn' : n + 1 < p.walk.support.length :=
          p.lt_length_of_prefix_mem_getElem hpq (n + 1) hn hxp
        simp only [Set.mem_iUnion]
        refine ⟨Sum.inl p, hpC, ?_⟩
        apply (p.walk.mem_edgeSet_iff_exists_getElem _).2
        refine ⟨n, hn', ?_⟩
        rw [hpq.getElem (lt_trans (Nat.lt_succ_self n) hn'),
          hpq.getElem hn']
      · exact False.elim hpq
    · obtain ⟨n, rfl⟩ := he
      have hx : r (n + 1) ∈ Path.support (Sum.inr r : Path D) :=
        ⟨n + 1, rfl⟩
      rw [hsupport] at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨p, hpC, hxp⟩ := hx
      have hpr : Extends p (.inr r) := by
        rw [← hq]
        exact extends_chainLimit C hCne hC hpC
      simp only [Set.mem_iUnion]
      refine ⟨p, hpC, ?_⟩
      rcases p with p | s
      · have hn' : n + 1 < p.walk.support.length :=
          p.lt_length_of_initialSegment_mem hpr (n + 1) hxp
        apply (p.walk.mem_edgeSet_iff_exists_getElem _).2
        refine ⟨n, hn', ?_⟩
        rw [hpr n (lt_trans (Nat.lt_succ_self n) hn'), hpr (n + 1) hn']
      · change s = r at hpr
        subst s
        exact ⟨n, rfl⟩
  · intro e he
    simp only [Set.mem_iUnion] at he
    obtain ⟨p, hpC, hep⟩ := he
    exact edgeSet_mono_of_extends
      (extends_chainLimit C hCne hC hpC) hep

end DirectedPath

namespace DWeb

open DirectedPath
open Ladder

/-- Forget the target of a concrete web, retaining the graph and source
needed by the path-only Section 7 bookkeeping. -/
def bookkeepingPathSystem (G : DWeb V) : LadderBookkeeping.PathSystem V where
  graph := G.graph
  source := G.source

/-- Directed edges occurring in a finite walk.  This name is retained for
the ladder API, but is definitionally the canonical observable from
`PathTools`; successor and limit clauses therefore speak about the same
directed-edge set. -/
def walkEdgeSet {D : Digraph V} {a b : V}
    (p : DirectedPath.Walk D a b) : Set (V × V) :=
  p.edgeSet

/-- Directed edges occurring in a finite path or ray, definitionally the
canonical `DirectedPath.Path.edgeSet`. -/
def pathEdgeSet {D : Digraph V} (p : DirectedPath.Path D) : Set (V × V) :=
  p.edgeSet

variable {V : Type u} (G : DWeb V)

/-- The inessential paths of a warp: precisely the members removed by
essential trimming.  This is the path-valued notation `IE(W)` in the
source, and is distinct from `DWeb.inessential`, which is vertex-valued. -/
def inessentialPaths (W : Set G.DPath) : Set G.DPath :=
  W \ G.essentialWarpPart W

@[simp]
theorem mem_inessentialPaths {W : Set G.DPath} {p : G.DPath} :
    p ∈ G.inessentialPaths W ↔ p ∈ W ∧ p ∉ G.essentialWarpPart W :=
  Iff.rfl

/-- Every ray in a warp is an inessential path, since essential trimming
keeps only paths with a finite terminal. -/
theorem ray_mem_inessentialPaths {W : Set G.DPath}
    {r : DirectedPath.Ray G.graph} (hr : Sum.inr r ∈ W) :
    Sum.inr r ∈ G.inessentialPaths W := by
  refine ⟨hr, ?_⟩
  rintro ⟨_, t, ht, _⟩
  simp at ht

/-- A path meeting an essential member of the same warp cannot be
inessential.  When the path is a ray, equality with the finite essential
member is impossible by the sum constructors; when it is finite, equality
makes the path itself essential.  Thus this single warp-disjointness lemma
contains exactly the finite-versus-ray split used in source Lemma 7.28. -/
theorem not_mem_inessentialPaths_of_intersects_essential
    {W : Set G.DPath} (hW : G.IsWarp W) {p q : G.DPath}
    (hq : q ∈ G.essentialWarpPart W)
    (hpq : (p.support ∩ q.support).Nonempty) :
    p ∉ G.inessentialPaths W := by
  intro hp
  by_cases hpeq : p = q
  · exact hp.2 (hpeq ▸ hq)
  · obtain ⟨x, hxp, hxq⟩ := hpq
    exact Set.disjoint_left.1 (hW hp.1 hq.1 hpeq) hxp hxq

/-- Membership in a warp together with avoidance of its essential terminal
frontier is exactly enough to make a path inessential. -/
theorem mem_inessentialPaths_of_misses_essentialFrontier
    {W : Set G.DPath} {p : G.DPath} (hp : p ∈ W)
    (hmiss : ¬ (G.essential (G.terminalFrontier W) ∩ p.support).Nonempty) :
    p ∈ G.inessentialPaths W := by
  refine ⟨hp, ?_⟩
  rintro ⟨_, t, hpt, ht⟩
  apply hmiss
  exact ⟨t, ht, G.terminal_mem_support hpt⟩

/-- The terminal of a finite inessential warp member lies in the strict
roof of the warp's terminal frontier.  This is the path-level fact used in
source Lemma 7.19. -/
theorem terminal_mem_strictRoof_of_mem_inessentialPaths
    {W : Set G.DPath} {p : G.DPath} {x : V}
    (hp : p ∈ G.inessentialPaths W) (hpx : G.terminal? p = some x) :
    x ∈ G.strictRoof (G.terminalFrontier W) := by
  constructor
  · apply G.subset_roof
    exact ⟨p, hp.1, hpx⟩
  · intro hx
    exact hp.2 ⟨hp.1, x, hpx, hx⟩

/-! ## Direct limits of growing warp families -/

/-- A linearly indexed family of warps in which every earlier path has an
extension at every later index.  Unlike `ForwardExtension`, this one-sided
notion permits fresh marker components to appear. -/
structure GrowingWarpChain (I : Type v) [LinearOrder I] where
  stage : I → Set G.DPath
  isWarp : ∀ i, G.IsWarp (stage i)
  grows : ∀ ⦃i j : I⦄, i ≤ j →
    ∀ p ∈ stage i, ∃ q ∈ stage j, G.Extends p q

/-- Directed-edge observable of a path family. -/
def pathFamilyEdgeSet (W : Set G.DPath) : Set (V × V) :=
  {e | ∃ p ∈ W, e ∈ p.edgeSet}

namespace GrowingWarpChain

variable {I : Type v} [LinearOrder I]

/-- Initial vertices which occur at some stage of a growing chain. -/
def initialUnion (C : G.GrowingWarpChain I) : Set V :=
  ⋃ i, G.initialSet (C.stage i)

/-- All members of the extension thread with initial vertex `a`. -/
def thread (C : G.GrowingWarpChain I) (a : V) : Set G.DPath :=
  {p | ∃ i, p ∈ C.stage i ∧ p.initial = a}

theorem thread_nonempty (C : G.GrowingWarpChain I)
    (a : C.initialUnion) : (C.thread G a.1).Nonempty := by
  obtain ⟨i, p, hp, hpa⟩ := Set.mem_iUnion.1 a.2
  exact ⟨p, i, hp, hpa⟩

/-- A common late stage compares any two members of one initial thread. -/
theorem thread_isChain (C : G.GrowingWarpChain I) (a : V) :
    IsChain DirectedPath.Path.Extends (C.thread G a) := by
  rintro p ⟨i, hpi, hpa⟩ q ⟨j, hqj, hqa⟩ hpq
  rcases le_total i j with hij | hji
  · obtain ⟨r, hrj, hpr⟩ := C.grows hij p hpi
    have hrq : r = q :=
      DWeb.IsWarp.eq_of_initial_eq G (C.isWarp j) hrj hqj
        ((G.extends_initial hpr).symm.trans (hpa.trans hqa.symm))
    exact Or.inl (hrq ▸ hpr)
  · obtain ⟨r, hri, hqr⟩ := C.grows hji q hqj
    have hrp : r = p :=
      DWeb.IsWarp.eq_of_initial_eq G (C.isWarp i) hri hpi
        ((G.extends_initial hqr).symm.trans (hqa.trans hpa.symm))
    exact Or.inr (hrp ▸ hqr)

/-- The genuine direct-limit path of one thread.  An unbounded chain of
strictly growing finite prefixes becomes a ray here. -/
noncomputable def threadLimit (C : G.GrowingWarpChain I)
    (a : C.initialUnion) : G.DPath :=
  DirectedPath.Path.chainLimit (C.thread G a.1)
    (C.thread_nonempty G a) (C.thread_isChain G a.1)

theorem threadLimit_initial (C : G.GrowingWarpChain I)
    (a : C.initialUnion) : (C.threadLimit G a).initial = a.1 := by
  obtain ⟨p, i, hpi, hpa⟩ := C.thread_nonempty G a
  exact (G.extends_initial
    (DirectedPath.Path.extends_chainLimit (C.thread G a.1)
      (C.thread_nonempty G a) (C.thread_isChain G a.1)
      ⟨i, hpi, hpa⟩)).symm.trans hpa

/-- One direct-limit path for every initial vertex ever introduced. -/
noncomputable def limitPaths (C : G.GrowingWarpChain I) : Set G.DPath :=
  Set.range (C.threadLimit G)

theorem mem_limitPaths_iff (C : G.GrowingWarpChain I) (p : G.DPath) :
    p ∈ C.limitPaths G ↔
      ∃ a : C.initialUnion, C.threadLimit G a = p :=
  Iff.rfl

theorem initialSet_limitPaths (C : G.GrowingWarpChain I) :
    G.initialSet (C.limitPaths G) = C.initialUnion := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, ⟨a, rfl⟩, rfl⟩
    simpa [C.threadLimit_initial G a] using a.2
  · intro x hx
    let a : C.initialUnion := ⟨x, hx⟩
    exact ⟨C.threadLimit G a, ⟨a, rfl⟩, C.threadLimit_initial G a⟩

theorem mem_support_threadLimit_iff (C : G.GrowingWarpChain I)
    (a : C.initialUnion) (x : V) :
    x ∈ (C.threadLimit G a).support ↔
      ∃ i p, p ∈ C.stage i ∧ p.initial = a.1 ∧ x ∈ p.support := by
  rw [threadLimit, DirectedPath.Path.support_chainLimit]
  simp only [Set.mem_iUnion, thread]
  constructor
  · rintro ⟨p, ⟨i, hpi, hpa⟩, hxp⟩
    exact ⟨i, p, hpi, hpa, hxp⟩
  · rintro ⟨i, p, hpi, hpa, hxp⟩
    exact ⟨p, ⟨i, hpi, hpa⟩, hxp⟩

/-- Direct limits of growing warp chains are warps. -/
theorem isWarp_limitPaths (C : G.GrowingWarpChain I) :
    G.IsWarp (C.limitPaths G) := by
  rintro pa ⟨a, rfl⟩ pb ⟨b, rfl⟩ hab
  apply Set.disjoint_left.2
  intro x hxa hxb
  obtain ⟨i, p, hpi, hpa, hxp⟩ :=
    (C.mem_support_threadLimit_iff G a x).1 hxa
  obtain ⟨j, q, hqj, hqb, hxq⟩ :=
    (C.mem_support_threadLimit_iff G b x).1 hxb
  rcases le_total i j with hij | hji
  · obtain ⟨r, hrj, hpr⟩ := C.grows hij p hpi
    have hxr : x ∈ r.support := G.support_mono_of_extends hpr hxp
    have hrq : r = q := by
      by_contra hrq
      exact Set.disjoint_left.1 (C.isWarp j hrj hqj hrq) hxr hxq
    have habv : a.1 = b.1 := by
      calc
        a.1 = p.initial := hpa.symm
        _ = r.initial := G.extends_initial hpr
        _ = q.initial := congrArg DirectedPath.Path.initial hrq
        _ = b.1 := hqb
    exact hab (congrArg (C.threadLimit G) (Subtype.ext habv))
  · obtain ⟨r, hri, hqr⟩ := C.grows hji q hqj
    have hxr : x ∈ r.support := G.support_mono_of_extends hqr hxq
    have hrp : r = p := by
      by_contra hrp
      exact Set.disjoint_left.1 (C.isWarp i hri hpi hrp) hxr hxp
    have habv : a.1 = b.1 := by
      calc
        a.1 = p.initial := hpa.symm
        _ = r.initial := congrArg DirectedPath.Path.initial hrp.symm
        _ = q.initial := (G.extends_initial hqr).symm
        _ = b.1 := hqb
    exact hab (congrArg (C.threadLimit G) (Subtype.ext habv))

/-- Every stage path has its thread limit as an extension. -/
theorem grows_limitPaths (C : G.GrowingWarpChain I) (i : I) :
    ∀ p ∈ C.stage i, ∃ q ∈ C.limitPaths G, G.Extends p q := by
  intro p hp
  have hpInitial : p.initial ∈ C.initialUnion :=
    Set.mem_iUnion.2 ⟨i, p, hp, rfl⟩
  let a : C.initialUnion := ⟨p.initial, hpInitial⟩
  refine ⟨C.threadLimit G a, ⟨a, rfl⟩, ?_⟩
  exact DirectedPath.Path.extends_chainLimit (C.thread G a.1)
    (C.thread_nonempty G a) (C.thread_isChain G a.1) ⟨i, hp, rfl⟩

/-- Vertex supports in a growing warp chain are monotone. -/
theorem vertexSet_mono (C : G.GrowingWarpChain I) :
    Monotone (fun i ↦ G.vertexSet (C.stage i)) := by
  intro i j hij x hx
  obtain ⟨p, hp, hxp⟩ := hx
  obtain ⟨q, hq, hpq⟩ := C.grows hij p hp
  exact ⟨q, hq, G.support_mono_of_extends hpq hxp⟩

/-- The vertex support of the threadwise direct limit is the union of all
earlier vertex supports. -/
theorem vertexSet_limitPaths (C : G.GrowingWarpChain I) :
    G.vertexSet (C.limitPaths G) = ⋃ i, G.vertexSet (C.stage i) := by
  ext x
  constructor
  · rintro ⟨q, ⟨a, rfl⟩, hxq⟩
    obtain ⟨i, p, hp, _hpa, hxp⟩ :=
      (C.mem_support_threadLimit_iff G a x).1 hxq
    exact Set.mem_iUnion.2 ⟨i, p, hp, hxp⟩
  · intro hx
    obtain ⟨i, p, hp, hxp⟩ := Set.mem_iUnion.1 hx
    have hpInitial : p.initial ∈ C.initialUnion :=
      Set.mem_iUnion.2 ⟨i, p, hp, rfl⟩
    let a : C.initialUnion := ⟨p.initial, hpInitial⟩
    refine ⟨C.threadLimit G a, ⟨a, rfl⟩, ?_⟩
    exact (C.mem_support_threadLimit_iff G a x).2
      ⟨i, p, hp, rfl, hxp⟩

/-- The direct limit realizes eventual membership of the source's vertex
observable. -/
theorem vertexSet_limitPaths_eq_setLiminf [Nonempty I]
    (C : G.GrowingWarpChain I) :
    G.vertexSet (C.limitPaths G) =
      WarpLimits.setLiminf (fun i ↦ G.vertexSet (C.stage i)) := by
  rw [C.vertexSet_limitPaths G,
    WarpLimits.setLiminf_eq_iUnion_of_monotone C.vertexSet_mono]

theorem pathFamilyEdgeSet_mono (C : G.GrowingWarpChain I) :
    Monotone (fun i ↦ G.pathFamilyEdgeSet (C.stage i)) := by
  intro i j hij e he
  obtain ⟨p, hp, hep⟩ := he
  obtain ⟨q, hq, hpq⟩ := C.grows hij p hp
  exact ⟨q, hq, DirectedPath.Path.edgeSet_mono_of_extends hpq hep⟩

/-- The edge set of the direct-limit family is the union of all earlier
family edge sets. -/
theorem pathFamilyEdgeSet_limitPaths (C : G.GrowingWarpChain I) :
    G.pathFamilyEdgeSet (C.limitPaths G) =
      ⋃ i, G.pathFamilyEdgeSet (C.stage i) := by
  ext e
  constructor
  · rintro ⟨q, ⟨a, rfl⟩, heq⟩
    rw [threadLimit] at heq
    rw [DirectedPath.Path.edgeSet_chainLimit] at heq
    simp only [Set.mem_iUnion] at heq
    obtain ⟨p, hpThread, hep⟩ := heq
    obtain ⟨i, hp, _hpa⟩ := hpThread
    exact Set.mem_iUnion.2 ⟨i, p, hp, hep⟩
  · intro he
    obtain ⟨i, p, hp, hep⟩ := Set.mem_iUnion.1 he
    obtain ⟨q, hq, hpq⟩ := C.grows_limitPaths G i p hp
    exact ⟨q, hq, DirectedPath.Path.edgeSet_mono_of_extends hpq hep⟩

/-- The direct limit also realizes eventual membership of the source's
directed-edge observable. -/
theorem pathFamilyEdgeSet_limitPaths_eq_setLiminf [Nonempty I]
    (C : G.GrowingWarpChain I) :
    G.pathFamilyEdgeSet (C.limitPaths G) =
      WarpLimits.setLiminf (fun i ↦ G.pathFamilyEdgeSet (C.stage i)) := by
  rw [C.pathFamilyEdgeSet_limitPaths G,
    WarpLimits.setLiminf_eq_iUnion_of_monotone C.pathFamilyEdgeSet_mono]

end GrowingWarpChain

/-! ## The ordinal recursion used by the concrete constructor -/

/-- A recursive accumulator together with the flag saying that no earlier
rung has exhausted its marker candidates. -/
abbrev LadderAccumulationState := Set G.DPath × Bool

/-- The earlier path-family values form the stages of a growing warp
chain.  The constructor's transfinite induction proves this predicate at
every genuine limit; making it explicit lets the recursive definition use
the genuine threadwise direct limit without building proofs into its
value type. -/
def HasMatchingLadderChain (o : Ordinal.{u})
    (prior : ∀ b : Ordinal.{u}, b < o → G.LadderAccumulationState) : Prop :=
  ∃ C : G.GrowingWarpChain (Set.Iio o),
    ∀ b : Set.Iio o, C.stage b = (prior b.1 b.2).1

/-- No earlier stage has exhausted its candidates. -/
def AllPriorLadderStagesActive (o : Ordinal.{u})
    (prior : ∀ b : Ordinal.{u}, b < o → G.LadderAccumulationState) : Prop :=
  ∀ b (hb : b < o), (prior b hb).2 = true

/-- At a genuine limit, take the threadwise direct limit of the earlier
chain.  A false flag is propagated cofinally: once a rung has exhausted
its candidates, later stages continue to mark time.  The fallback branch
is totality bookkeeping only; the construction theorem proves that its
hypothesis never occurs. -/
noncomputable def ladderLimitState (o : Ordinal.{u})
    (_ho : Order.IsSuccLimit o)
    (prior : ∀ b : Ordinal.{u}, b < o → G.LadderAccumulationState) :
    G.LadderAccumulationState := by
  classical
  exact if hchain : G.HasMatchingLadderChain o prior then
      ((Classical.choose hchain).limitPaths G,
        if G.AllPriorLadderStagesActive o prior then true else false)
    else
      (G.trivialWave, false)

/-- Unrestricted ordinal recursion underlying a ladder accumulator. -/
noncomputable def ladderAccumulatedStateAux
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : Ordinal.{u}) : G.LadderAccumulationState :=
  Ordinal.limitRecOn a (G.trivialWave, true) step G.ladderLimitState

/-- Restriction of the ordinal recursion to stages through `κ`. -/
noncomputable def ladderAccumulatedState (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : ExtendedStage κ) : G.LadderAccumulationState :=
  G.ladderAccumulatedStateAux step a.1

/-- The path-family projection of the recursive state. -/
noncomputable def ladderAccumulated (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : ExtendedStage κ) : Set G.DPath :=
  (G.ladderAccumulatedState κ step a).1

@[simp]
theorem ladderAccumulatedState_zero (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState) :
    G.ladderAccumulatedState κ step (zeroStage κ) =
      (G.trivialWave, true) := by
  simp [ladderAccumulatedState, ladderAccumulatedStateAux, zeroStage]

@[simp]
theorem ladderAccumulated_zero (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState) :
    G.ladderAccumulated κ step (zeroStage κ) = G.trivialWave := by
  simp [ladderAccumulated]

@[simp]
theorem ladderAccumulatedState_succ (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : Stage κ) :
    G.ladderAccumulatedState κ step (Stage.succExtended a) =
      step a.1
        (G.ladderAccumulatedState κ step (Stage.toExtended a)) := by
  simp [ladderAccumulatedState, ladderAccumulatedStateAux,
    Stage.succExtended, Stage.toExtended]

@[simp]
theorem ladderAccumulated_succ (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : Stage κ) :
    G.ladderAccumulated κ step (Stage.succExtended a) =
      (step a.1
        (G.ladderAccumulatedState κ step (Stage.toExtended a))).1 := by
  simp [ladderAccumulated]

theorem ladderAccumulatedState_limit (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : ExtendedStage κ) (ha : Order.IsSuccLimit a.1) :
    G.ladderAccumulatedState κ step a =
      G.ladderLimitState a.1 ha
        (fun b _hb ↦ G.ladderAccumulatedStateAux step b) := by
  exact Ordinal.limitRecOn_limit a.1 (G.trivialWave, true) step
    G.ladderLimitState ha

theorem ladderAccumulated_limit_of_matching (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : ExtendedStage κ) (ha : Order.IsSuccLimit a.1)
    (hchain : G.HasMatchingLadderChain a.1
      (fun b _hb ↦ G.ladderAccumulatedStateAux step b)) :
    G.ladderAccumulated κ step a =
      (Classical.choose hchain).limitPaths G := by
  rw [ladderAccumulated, G.ladderAccumulatedState_limit κ step a ha]
  simp only [ladderLimitState, dif_pos hchain]

theorem exists_ladderLimitChain (κ : Cardinal.{u})
    (step : Ordinal.{u} →
      G.LadderAccumulationState → G.LadderAccumulationState)
    (a : ExtendedStage κ) (ha : Order.IsSuccLimit a.1)
    (hchain : G.HasMatchingLadderChain a.1
      (fun b _hb ↦ G.ladderAccumulatedStateAux step b)) :
    ∃ C : G.GrowingWarpChain (Set.Iio a.1),
      (∀ b : Set.Iio a.1,
        C.stage b = G.ladderAccumulated κ step
          ⟨b.1, b.2.le.trans a.2⟩) ∧
      G.ladderAccumulated κ step a = C.limitPaths G := by
  let C := Classical.choose hchain
  refine ⟨C, ?_, ?_⟩
  · intro b
    exact Classical.choose_spec hchain b
  · exact G.ladderAccumulated_limit_of_matching κ step a ha hchain

/-- The exact stage web `Γ_α = ℰ(Γ/Y_α)`: first quotient by
the terminal frontier of the accumulated warp and then take the essential
web, i.e. the induced restriction to vertices from which the target is
finitely reachable. -/
def stageWebOf (W : Set G.DPath) : DWeb V :=
  (G.quotient (G.terminalFrontier W)).essentialPart

/-! ## Canonical successor data -/

/-- The canonical maximal rung chosen from a recursive accumulator state.
After marker exhaustion the stage web is loose; consequently this same
definition is provably the trivial wave there. -/
noncomputable def ladderRungOfState (s : G.LadderAccumulationState) :
    Set ((G.stageWebOf s.1).DPath) :=
  (G.stageWebOf s.1).chosenMaximalWave.1

/-- Candidate vertices for the optional fresh marker at a recursive
successor state. -/
def ladderMarkerCandidatesOfState (s : G.LadderAccumulationState) : Set V :=
  ((G.stageWebOf s.1).reachableToTarget ∩
      G.quotientVertexSet (G.terminalFrontier s.1)) \
    ((G.stageWebOf s.1).source ∪
      (G.stageWebOf s.1).vertexSet (G.ladderRungOfState s))

/-- The canonical marker choice, preferring the scheduled vertex whenever
that vertex is currently eligible. -/
noncomputable def ladderMarkerOfState (preferred : Option V)
    (s : G.LadderAccumulationState) : Option V := by
  classical
  exact if s.2 = true then
    match preferred with
    | some x =>
        if x ∈ G.ladderMarkerCandidatesOfState s then some x
        else if h : (G.ladderMarkerCandidatesOfState s).Nonempty then
          some (Classical.choose h)
        else none
    | none =>
        if h : (G.ladderMarkerCandidatesOfState s).Nonempty then
          some (Classical.choose h)
        else none
  else none

theorem ladderMarkerOfState_eq_some_preferred
    {preferred : Option V} {s : G.LadderAccumulationState} {x : V}
    (hactive : s.2 = true) (hpref : preferred = some x)
    (hx : x ∈ G.ladderMarkerCandidatesOfState s) :
    G.ladderMarkerOfState preferred s = some x := by
  simp [ladderMarkerOfState, hactive, hpref, hx]

theorem ladderMarkerOfState_mem_candidates
    {preferred : Option V} {s : G.LadderAccumulationState} {x : V}
    (hx : G.ladderMarkerOfState preferred s = some x) :
    x ∈ G.ladderMarkerCandidatesOfState s := by
  classical
  simp only [ladderMarkerOfState.eq_def] at hx
  split at hx
  next hactive =>
    cases hpref : preferred with
    | none =>
        simp only [hpref] at hx
        split at hx
        next hne =>
          have hchosen := Classical.choose_spec hne
          exact Option.some.inj hx ▸ hchosen
        next _ => simp at hx
    | some y =>
        simp only [hpref] at hx
        split at hx
        next hy => exact Option.some.inj hx ▸ hy
        next hy =>
          split at hx
          next hne =>
            have hchosen := Classical.choose_spec hne
            exact Option.some.inj hx ▸ hchosen
          next _ => simp at hx
  next _ => simp at hx

theorem ladderMarkerOfState_eq_none_iff
    (preferred : Option V) (s : G.LadderAccumulationState)
    (hactive : s.2 = true) :
    G.ladderMarkerOfState preferred s = none ↔
      G.ladderMarkerCandidatesOfState s = ∅ := by
  classical
  constructor
  · intro hnone
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨x, hx⟩ := hne
    have hnonempty : (G.ladderMarkerCandidatesOfState s).Nonempty :=
      ⟨x, hx⟩
    cases hpref : preferred with
    | none =>
        simp only [ladderMarkerOfState.eq_def, hactive, if_pos,
          hpref, hnonempty, dif_pos] at hnone
        cases hnone
    | some y =>
        by_cases hy : y ∈ G.ladderMarkerCandidatesOfState s
        · simp only [ladderMarkerOfState.eq_def, hactive, if_pos,
            hpref, hy] at hnone
          cases hnone
        · simp only [ladderMarkerOfState.eq_def, hactive, if_pos,
            hpref, hy, hnonempty, dif_pos] at hnone
          simp only [if_false] at hnone
          cases hnone
  · intro hempty
    have hne : ¬ (G.ladderMarkerCandidatesOfState s).Nonempty := by
      simpa [hempty]
    cases hpref : preferred with
    | none => simp [ladderMarkerOfState.eq_def, hactive, hne]
    | some y =>
        have hy : y ∉ G.ladderMarkerCandidatesOfState s := by
          simpa [hempty]
        simp [ladderMarkerOfState.eq_def, hactive, hy, hne]

/-- Lift a path in the essential quotient stage back to the ambient web. -/
def liftLadderStagePathOf (W : Set G.DPath)
    (p : (G.stageWebOf W).DPath) : G.DPath :=
  G.liftQuotientPath (G.terminalFrontier W)
    ((G.quotient (G.terminalFrontier W)).liftEssentialPartPath p)

/-- The family-level lift of a canonical rung. -/
def liftedLadderRungOfState (s : G.LadderAccumulationState) :
    Set G.DPath :=
  G.liftLadderStagePathOf s.1 '' G.ladderRungOfState s

/-- The optional singleton marker family associated with a state. -/
def ladderMarkerPathSetOfState (preferred : Option V)
    (s : G.LadderAccumulationState) :
    Set G.DPath :=
  match G.ladderMarkerOfState preferred s with
  | none => ∅
  | some y => {G.trivialPath y}

/-- The concrete successor family while the construction is active. -/
noncomputable def activeLadderSuccessor
    (preferred : Option V) (s : G.LadderAccumulationState) : Set G.DPath :=
  G.arrow s.1 (G.liftedLadderRungOfState s) ∪
    G.ladderMarkerPathSetOfState preferred s

/-- One successor step of the canonical ladder recursion.  After the first
empty candidate set the path family is held fixed and the flag remains
false. -/
noncomputable def ladderSuccessorState
    (preferred : Ordinal.{u} → Option V)
    (a : Ordinal.{u}) (s : G.LadderAccumulationState) :
    G.LadderAccumulationState := by
  classical
  exact if hs : s.2 = true then
    (G.activeLadderSuccessor (preferred a) s,
      if (G.ladderMarkerCandidatesOfState s).Nonempty then true else false)
  else (s.1, false)

/-- Extend a schedule on stages below `κ` to the unrestricted ordinal
recursion. -/
noncomputable def extendLadderPreference (κ : Cardinal.{u})
    (preferred : Stage κ → Option V) (a : Ordinal.{u}) : Option V := by
  classical
  exact if ha : a < κ.ord then preferred ⟨a, ha⟩ else none

/-- State of the canonical recursion at an extended stage. -/
noncomputable def canonicalLadderState (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : ExtendedStage κ) : G.LadderAccumulationState :=
  G.ladderAccumulatedState κ
    (G.ladderSuccessorState (extendLadderPreference κ preferred)) a

/-- Accumulated family of the canonical recursion. -/
noncomputable def canonicalLadderAccumulated (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : ExtendedStage κ) : Set G.DPath :=
  (G.canonicalLadderState κ preferred a).1

/-- Canonical rung at a stage below `κ`. -/
noncomputable def canonicalLadderRung (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : Stage κ) : Set ((G.stageWebOf
      (G.canonicalLadderAccumulated κ preferred
        (Stage.toExtended a))).DPath) :=
  G.ladderRungOfState
    (G.canonicalLadderState κ preferred (Stage.toExtended a))

/-- Canonical marker at a stage below `κ`. -/
noncomputable def canonicalLadderMarker (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : Stage κ) : Option V :=
  G.ladderMarkerOfState (preferred a)
    (G.canonicalLadderState κ preferred (Stage.toExtended a))

/-- The raw data of a `κ`-ladder.  Structural laws (warp-valuedness,
wave-valued rungs, successor arrows, marker freshness, and limit clauses)
are predicates below, rather than hidden proof fields. -/
structure KappaLadder (κ : Cardinal.{u}) where
  /-- Accumulated warps, including the final stage `κ`. -/
  accumulated : ExtendedStage κ → Set G.DPath
  /-- The wave selected in the trimmed quotient stage. -/
  rung : ∀ a : Stage κ,
    Set ((G.stageWebOf (accumulated (Ladder.Stage.toExtended a))).DPath)
  /-- The fresh singleton marker, when the construction adds one. -/
  marker : Stage κ → Option V
  /-- The troublesome inessential path recorded at the stage. -/
  chosen : Stage κ → Option G.DPath

/-- The canonical transfinite ladder data before the independent
one-record-per-stage bookkeeping choice is installed. -/
noncomputable def canonicalLadderCore (κ : Cardinal.{u})
    (preferred : Stage κ → Option V) :
    G.KappaLadder κ where
  accumulated := G.canonicalLadderAccumulated κ preferred
  rung := G.canonicalLadderRung κ preferred
  marker := G.canonicalLadderMarker κ preferred
  chosen := fun _ ↦ none

variable {G : DWeb V}

namespace KappaLadder

@[simp]
theorem canonicalLadderCore_accumulated (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : ExtendedStage κ) :
    (G.canonicalLadderCore κ preferred).accumulated a =
      G.canonicalLadderAccumulated κ preferred a :=
  rfl

@[simp]
theorem canonicalLadderCore_rung (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : Stage κ) :
    (G.canonicalLadderCore κ preferred).rung a =
      G.canonicalLadderRung κ preferred a :=
  rfl

@[simp]
theorem canonicalLadderCore_marker (κ : Cardinal.{u})
    (preferred : Stage κ → Option V)
    (a : Stage κ) :
    (G.canonicalLadderCore κ preferred).marker a =
      G.canonicalLadderMarker κ preferred a :=
  rfl

/-- The accumulated warp at an ordinary stage. -/
def warpAt (L : G.KappaLadder κ) (a : Stage κ) : Set G.DPath :=
  L.accumulated (Ladder.Stage.toExtended a)

/-- The accumulated successor warp `Y_(α+1)`. -/
def successorWarp (L : G.KappaLadder κ) (a : Stage κ) : Set G.DPath :=
  L.accumulated (Ladder.Stage.succExtended a)

/-- The limiting ladder warp `Y_κ`. -/
def limitWarp (L : G.KappaLadder κ) : Set G.DPath :=
  L.accumulated (finalStage κ)

/-- The source-faithful trimmed quotient stage. -/
def stageWeb (L : G.KappaLadder κ) (a : Stage κ) : DWeb V :=
  G.stageWebOf (L.warpAt a)

/-- The frontier `T_α`, namely the source of the essential quotient web.
It is not definitionally replaced by an essential-vertex formula in the
original web. -/
def frontier (L : G.KappaLadder κ) (a : Stage κ) : Set V :=
  (L.stageWeb a).source

@[simp]
theorem frontier_eq (L : G.KappaLadder κ) (a : Stage κ) :
    L.frontier a =
      (G.quotient (G.terminalFrontier (L.warpAt a))).source ∩
        (G.quotient
          (G.terminalFrontier (L.warpAt a))).reachableToTarget :=
  rfl

/-- Every rung of the canonical core is roof-maximal. -/
theorem canonicalLadderCore_roofLE_rung (κ : Cardinal.{u})
    (preferred : Stage κ → Option V) (a : Stage κ)
    (W : Set ((G.canonicalLadderCore κ preferred).stageWeb a).DPath)
    (hW : ((G.canonicalLadderCore κ preferred).stageWeb a).IsWave W) :
    ((G.canonicalLadderCore κ preferred).stageWeb a).RoofLE W
      ((G.canonicalLadderCore κ preferred).rung a) := by
  exact ((G.canonicalLadderCore κ preferred).stageWeb a)
    |>.roofLE_chosenMaximalWave W hW

/-- At a hindered canonical stage, the chosen rung is a hindrance. -/
theorem canonicalLadderCore_rung_isHindrance (κ : Cardinal.{u})
    (preferred : Stage κ → Option V) (a : Stage κ)
    (hstage :
      ¬ ((G.canonicalLadderCore κ preferred).stageWeb a).IsUnhindered) :
    ((G.canonicalLadderCore κ preferred).stageWeb a).IsHindrance
      ((G.canonicalLadderCore κ preferred).rung a) := by
  exact ((G.canonicalLadderCore κ preferred).stageWeb a)
    |>.chosenMaximalWave_isHindrance_of_not_isUnhindered hstage

/-- Every accumulated family is genuinely a warp. -/
def HasWarpStages (L : G.KappaLadder κ) : Prop :=
  ∀ a : ExtendedStage κ, G.IsWarp (L.accumulated a)

/-- Every rung is a wave in its own essential quotient stage. -/
def HasWaveRungs (L : G.KappaLadder κ) : Prop :=
  ∀ a : Stage κ, (L.stageWeb a).IsWave (L.rung a)

/-- Every rung is maximal in the roof preorder of its essential quotient
stage.  This is a genuine construction law: the canonical recursion chooses
`chosenMaximalWave` at every stage.  It is also the exact maximality input
needed to rule out the same-stage marker branch in Section 8. -/
def HasRoofMaximalRungs (L : G.KappaLadder κ) : Prop :=
  ∀ a : Stage κ, ∀ W : Set (L.stageWeb a).DPath,
    (L.stageWeb a).IsWave W → (L.stageWeb a).RoofLE W (L.rung a)

/-- The canonical recursion satisfies the roof-maximal rung construction
law at every stage. -/
theorem canonicalLadderCore_hasRoofMaximalRungs (κ : Cardinal.{u})
    (preferred : Stage κ → Option V) :
    (G.canonicalLadderCore κ preferred).HasRoofMaximalRungs := by
  intro a W hW
  exact canonicalLadderCore_roofLE_rung κ preferred a W hW

/-- The ladder starts with the trivial warp on the original source. -/
def HasInitialStage (L : G.KappaLadder κ) : Prop :=
  L.accumulated (zeroStage κ) = G.trivialWave

/-- At a limit stage the accumulated family is the genuine direct limit of
the earlier extension threads.  Literal set liminf on whole path values is
incorrect here: a finite path strictly extended cofinally often is never
eventually equal to any one record, while its source limit is a ray. -/
def HasLimitStages (L : G.KappaLadder κ) : Prop :=
  ∀ (a : ExtendedStage κ), Order.IsSuccLimit a.1 →
    ∃ C : G.GrowingWarpChain (Set.Iio a.1),
      (∀ b : Set.Iio a.1,
        C.stage b = L.accumulated ⟨b.1, b.2.le.trans a.2⟩) ∧
      L.accumulated a = C.limitPaths G

/-- The limit clause itself supplies warp-valuedness at every genuine
limit stage. -/
theorem HasLimitStages.isWarp_at_limit {L : G.KappaLadder κ}
    (hL : L.HasLimitStages) (a : ExtendedStage κ)
    (ha : Order.IsSuccLimit a.1) : G.IsWarp (L.accumulated a) := by
  obtain ⟨C, _hstage, hlimit⟩ := hL a ha
  rw [hlimit]
  exact C.isWarp_limitPaths G

/-- Every earlier component extends to a component of the accumulated
direct limit. -/
theorem HasLimitStages.grows_to_limit {L : G.KappaLadder κ}
    (hL : L.HasLimitStages) (a : ExtendedStage κ)
    (ha : Order.IsSuccLimit a.1) (b : Set.Iio a.1)
    (p : G.DPath)
    (hp : p ∈ L.accumulated ⟨b.1, b.2.le.trans a.2⟩) :
    ∃ q ∈ L.accumulated a, G.Extends p q := by
  obtain ⟨C, hstage, hlimit⟩ := hL a ha
  have hpC : p ∈ C.stage b := by
    rw [hstage b]
    exact hp
  obtain ⟨q, hq, hpq⟩ := C.grows_limitPaths G b p hpC
  exact ⟨q, hlimit.symm ▸ hq, hpq⟩

/-- The accumulated limit satisfies the source's vertex-liminf equation. -/
theorem HasLimitStages.vertexSet_eq_setLiminf {L : G.KappaLadder κ}
    (hL : L.HasLimitStages) (a : ExtendedStage κ)
    (ha : Order.IsSuccLimit a.1) :
    G.vertexSet (L.accumulated a) =
      WarpLimits.setLiminf (fun b : Set.Iio a.1 ↦
        G.vertexSet (L.accumulated ⟨b.1, b.2.le.trans a.2⟩)) := by
  letI : Nonempty (Set.Iio a.1) := ha.nonempty_Iio.to_subtype
  obtain ⟨C, hstage, hlimit⟩ := hL a ha
  rw [hlimit, C.vertexSet_limitPaths_eq_setLiminf G]
  congr 2
  funext b
  rw [hstage b]

/-- The accumulated limit satisfies the source's directed-edge-liminf
equation. -/
theorem HasLimitStages.pathFamilyEdgeSet_eq_setLiminf
    {L : G.KappaLadder κ} (hL : L.HasLimitStages)
    (a : ExtendedStage κ) (ha : Order.IsSuccLimit a.1) :
    G.pathFamilyEdgeSet (L.accumulated a) =
      WarpLimits.setLiminf (fun b : Set.Iio a.1 ↦
        G.pathFamilyEdgeSet
          (L.accumulated ⟨b.1, b.2.le.trans a.2⟩)) := by
  letI : Nonempty (Set.Iio a.1) := ha.nonempty_Iio.to_subtype
  obtain ⟨C, hstage, hlimit⟩ := hL a ha
  rw [hlimit, C.pathFamilyEdgeSet_limitPaths_eq_setLiminf G]
  congr 2
  funext b
  rw [hstage b]

/-- The vertices of the essential quotient stage.  Since `DWeb` keeps a
fixed ambient vertex type, membership in the induced web is represented by
finite reachability to its target. -/
def stageVertexSet (L : G.KappaLadder κ) (a : Stage κ) : Set V :=
  (L.stageWeb a).reachableToTarget ∩
    G.quotientVertexSet (G.terminalFrontier (L.warpAt a))

/-- Vertices eligible to be the fresh singleton marker on rung `a`. -/
def markerCandidates (L : G.KappaLadder κ) (a : Stage κ) : Set V :=
  L.stageVertexSet a \
    ((L.stageWeb a).source ∪ (L.stageWeb a).vertexSet (L.rung a))

/-- The canonical recursion has not yet exhausted marker candidates at
this stage. -/
def CanonicalStageActive (preferred : Stage κ → Option V)
    (a : Stage κ) : Prop :=
  (G.canonicalLadderState κ preferred (Stage.toExtended a)).2 = true

@[simp]
theorem extendLadderPreference_stage
    (preferred : Stage κ → Option V) (a : Stage κ) :
    extendLadderPreference κ preferred a.1 = preferred a := by
  unfold extendLadderPreference
  split
  · congr 1
  · rename_i h
    exact (h a.2).elim

@[simp]
theorem canonicalLadderCore_warpAt
    (preferred : Stage κ → Option V) (a : Stage κ) :
    (G.canonicalLadderCore κ preferred).warpAt a =
      (G.canonicalLadderState κ preferred (Stage.toExtended a)).1 :=
  rfl

@[simp]
theorem canonicalLadderCore_markerCandidates
    (preferred : Stage κ → Option V) (a : Stage κ) :
    (G.canonicalLadderCore κ preferred).markerCandidates a =
      G.ladderMarkerCandidatesOfState
        (G.canonicalLadderState κ preferred (Stage.toExtended a)) :=
  rfl

/-- The scheduled vertex is selected whenever it is eligible at an active
stage. -/
theorem canonicalLadderCore_marker_eq_preferred
    (preferred : Stage κ → Option V) (a : Stage κ) {x : V}
    (hactive : CanonicalStageActive (G := G) preferred a)
    (hpref : preferred a = some x)
    (hx : x ∈ (G.canonicalLadderCore κ preferred).markerCandidates a) :
    (G.canonicalLadderCore κ preferred).marker a = some x := by
  exact G.ladderMarkerOfState_eq_some_preferred hactive hpref hx

/-- At an active stage, the canonical marker is absent exactly when the
candidate set is empty. -/
theorem canonicalLadderCore_marker_eq_none_iff
    (preferred : Stage κ → Option V) (a : Stage κ)
    (hactive : CanonicalStageActive (G := G) preferred a) :
    (G.canonicalLadderCore κ preferred).marker a = none ↔
      (G.canonicalLadderCore κ preferred).markerCandidates a = ∅ := by
  exact G.ladderMarkerOfState_eq_none_iff (preferred a)
    (G.canonicalLadderState κ preferred (Stage.toExtended a)) hactive

/-- Lift a rung path through the essential subweb and the quotient back to
the original web. -/
def liftStagePath (L : G.KappaLadder κ) (a : Stage κ)
    (p : (L.stageWeb a).DPath) : G.DPath :=
  G.liftQuotientPath (G.terminalFrontier (L.warpAt a))
    ((G.quotient (G.terminalFrontier (L.warpAt a))).liftEssentialPartPath p)

/-- A successor path is obtained by continuing an old path along one rung
path.  Support and edge-set equality rule out a merely equisupported but
differently ordered continuation. -/
def IsRungContinuation (L : G.KappaLadder κ) (a : Stage κ)
    (p q : G.DPath) (r : (L.stageWeb a).DPath) : Prop :=
  r ∈ L.rung a ∧
    G.terminal? p = some r.initial ∧
    G.Extends p q ∧
    q.support = p.support ∪ (L.liftStagePath a r).support ∧
    pathEdgeSet q = pathEdgeSet p ∪ pathEdgeSet (L.liftStagePath a r) ∧
    G.terminal? q = G.terminal? (L.liftStagePath a r)

/-- The graph of the exact warp-arrow operation on one old path.  Rays stay
fixed; a finite path is continued by the unique matching rung path when
one exists, and otherwise stays fixed. -/
def IsRungArrowPair (L : G.KappaLadder κ) (a : Stage κ)
    (p q : G.DPath) : Prop :=
  (G.terminal? p = none ∧ q = p) ∨
    ∃ x, G.terminal? p = some x ∧
      ((∃ r : (L.stageWeb a).DPath,
          r.initial = x ∧ L.IsRungContinuation a p q r) ∨
        ((¬ ∃ r ∈ L.rung a, r.initial = x) ∧ q = p))

/-- `Z` is exactly `Y_a ↷ W_a`: every old path has a unique arrow image,
and every member of `Z` is such an image. -/
def IsRungArrowResult (L : G.KappaLadder κ) (a : Stage κ)
    (Z : Set G.DPath) : Prop :=
  (∀ p ∈ L.warpAt a,
      ∃! q : G.DPath, q ∈ Z ∧ L.IsRungArrowPair a p q) ∧
    ∀ q ∈ Z, ∃ p ∈ L.warpAt a, L.IsRungArrowPair a p q

/-- The optional singleton marker family. -/
def markerPathSet (L : G.KappaLadder κ) (a : Stage κ) : Set G.DPath :=
  match L.marker a with
  | none => ∅
  | some y => {G.trivialPath y}

/-- The arrow part of the successor, with its optional marker removed. -/
def arrowPart (L : G.KappaLadder κ) (a : Stage κ) : Set G.DPath :=
  L.successorWarp a \ L.markerPathSet a

/-- Source-exact successor construction: the successor is precisely the
old warp arrowed through the rung, plus the one eligible marker path when a
marker is chosen.  In particular no extra successor components are
permitted. -/
def HasExactSuccessorArrows (L : G.KappaLadder κ) : Prop :=
  ∀ a : Stage κ,
    L.IsRungArrowResult a (L.arrowPart a) ∧
      L.successorWarp a = L.arrowPart a ∪ L.markerPathSet a

/-- Exact marker choice at a successor: a marker is absent precisely when
there is no eligible vertex; a chosen marker is eligible and its singleton
path is inserted in the successor warp. -/
def HasFreshMarkers (L : G.KappaLadder κ) : Prop :=
  (∀ a : Stage κ, L.marker a = none ↔ L.markerCandidates a = ∅) ∧
    ∀ (a : Stage κ) (y : V), L.marker a = some y →
      y ∈ L.markerCandidates a ∧ G.trivialPath y ∈ L.successorWarp a

/-- Once the eligible set is exhausted, all later rungs mark time with the
trivial wave and no further markers. -/
def MarksTimeAfterExhaustion (L : G.KappaLadder κ) : Prop :=
  ∀ {a b : Stage κ}, L.marker a = none → a < b →
    L.marker b = none ∧ L.rung b = (L.stageWeb b).trivialWave

/-- The canonical successor-normalized bookkeeping associated with a
concrete ladder. -/
def bookkeeping (L : G.KappaLadder κ) : Bookkeeping κ G.DPath where
  inessentialNext a := G.inessentialPaths (L.successorWarp a)
  isRay p := G.terminal? p = none
  chosen := L.chosen

/-- The concrete Section 7 bookkeeping associated with a ladder.  Unlike
`bookkeeping`, this bridge exposes both `IE(Y_α)` and `IE(Y_(α+1))`, as
required by the exact persistence and emergence arguments in Lemmas 7.4
and 7.27. -/
def concreteBookkeeping (L : G.KappaLadder κ) :
    LadderBookkeeping.ConcreteBookkeeping κ G.bookkeepingPathSystem where
  inessentialCurrent a := G.inessentialPaths (L.warpAt a)
  inessentialNext a := G.inessentialPaths (L.successorWarp a)
  isRay p := G.terminal? p = none
  chosen := L.chosen

/-- Validity of the one-path-per-stage choice rule. -/
def HasValidBookkeeping (L : G.KappaLadder κ) : Prop :=
  L.bookkeeping.IsValid

/-- The ray-preferring ladder choice rule implies the path-only choice
rule used by the emergence bookkeeping. -/
theorem concreteBookkeeping_isValid (L : G.KappaLadder κ)
    (hL : L.HasValidBookkeeping) : L.concreteBookkeeping.IsValid := by
  intro a
  change
    ((L.bookkeeping.available a).Nonempty →
      ∃ p, L.chosen a = some p ∧ p ∈ L.bookkeeping.available a) ∧
    ∀ p, L.chosen a = some p → p ∈ L.bookkeeping.available a
  constructor
  · intro havailable
    obtain ⟨p, hp, hpavailable, _⟩ := (hL a).1 havailable
    exact ⟨p, hp, hpavailable⟩
  · intro p hp
    exact (hL a).2 p hp

/-- The obstruction set `Φ(ℓᵃℓ L)`. -/
def phi (L : G.KappaLadder κ) : Set (Stage κ) :=
  L.bookkeeping.phi

/-- Stages at which an unrecorded ray is available. -/
def phiInfinite (L : G.KappaLadder κ) : Set (Stage κ) :=
  L.bookkeeping.phiInfinite

/-- Stages at which all available paths are finite. -/
def phiFinite (L : G.KappaLadder κ) : Set (Stage κ) :=
  L.bookkeeping.phiFinite

/-- Stages at which the selected rung is itself a hindrance. -/
def phiHindrance (L : G.KappaLadder κ) : Set (Stage κ) :=
  {a | (L.stageWeb a).IsHindrance (L.rung a)}

/-- Stages at which a ray occurs which occurred at no earlier accumulated
stage.  This is the source set `Φ_h^∞`. -/
def phiNewRay (L : G.KappaLadder κ) : Set (Stage κ) :=
  {a | ∃ p ∈ L.warpAt a, G.terminal? p = none ∧
      ∀ b : Stage κ, b < a → p ∉ L.warpAt b}

/-- The exceptional obstruction stages in source Lemma 7.27:
hindrance rungs together with stages at which a genuinely new ray occurs. -/
def exceptionalStages (L : G.KappaLadder κ) : Set (Stage κ) :=
  L.phiHindrance ∪ L.phiNewRay

/-- Stages at which at least `κ` paths are inessential in the successor
warp. -/
def largeInessentialStages (L : G.KappaLadder κ) : Set (Stage κ) :=
  {a | κ ≤ #(G.inessentialPaths (L.successorWarp a))}

@[simp]
theorem concreteBookkeeping_phi (L : G.KappaLadder κ) :
    L.concreteBookkeeping.phi = L.phi :=
  rfl

@[simp]
theorem concreteBookkeeping_largeInessentialStages (L : G.KappaLadder κ) :
    L.concreteBookkeeping.largeInessentialStages =
      L.largeInessentialStages := by
  rfl

/-- The first successor-normalized stage at which the path chosen at `a`
is inessential. -/
noncomputable def emergenceIndex (L : G.KappaLadder κ)
    (hvalid : L.HasValidBookkeeping) (a : Stage κ) : Stage κ :=
  L.concreteBookkeeping.emergenceIndex
    (L.concreteBookkeeping_isValid hvalid) a

/-- Markers added before a prescribed stage. -/
def markerSetBelow (L : G.KappaLadder κ) (a : Stage κ) : Set V :=
  {y | ∃ b : Stage κ, b < a ∧ L.marker b = some y}

/-- All markers added by the ladder. -/
def markerSet (L : G.KappaLadder κ) : Set V :=
  {y | ∃ a : Stage κ, L.marker a = some y}

/-- The terminal set `X_fin` of finite recorded paths. -/
def finiteTerminalSet (L : G.KappaLadder κ) : Set V :=
  {x | ∃ a ∈ L.phiFinite, ∃ p,
    L.chosen a = some p ∧ G.terminal? p = some x}

/-- The optional terminal `x_α` of the path recorded at stage `α`. -/
def recordedTerminalAt (L : G.KappaLadder κ) (a : Stage κ) : Option V :=
  (L.chosen a).bind G.terminal?

/-- Grounded obstruction stages, whose record starts in the original
source. -/
def phiGround (L : G.KappaLadder κ) : Set (Stage κ) :=
  {a | ∃ p, L.chosen a = some p ∧ p.initial ∈ G.source}

/-- Hanging obstruction stages, whose record starts at an earlier marker. -/
def phiHanging (L : G.KappaLadder κ) : Set (Stage κ) :=
  L.phi \ L.phiGround

/-- A vertex is used as a fresh marker at at most one stage. -/
def MarkersInjective (L : G.KappaLadder κ) : Prop :=
  ∀ ⦃a b : Stage κ⦄ ⦃y : V⦄,
    L.marker a = some y → L.marker b = some y → a = b

/-- Source marker provenance for hanging records: the initial vertex of a
path recorded at a hanging stage is a marker from a strictly earlier
stage. -/
def HasHangingProvenance (L : G.KappaLadder κ) : Prop :=
  ∀ (a : Stage κ), a ∈ L.phiHanging →
    ∀ (p : G.DPath), L.chosen a = some p →
      ∃ b : Stage κ, b < a ∧ L.marker b = some p.initial

/-- A chosen stage witnessing membership in the set of marker vertices. -/
noncomputable def markerStageIndex (L : G.KappaLadder κ)
    (y : L.markerSet) : Stage κ :=
  Classical.choose (show ∃ a : Stage κ, L.marker a = some y.1 from y.2)

@[simp]
theorem markerStageIndex_spec (L : G.KappaLadder κ) (y : L.markerSet) :
    L.marker (L.markerStageIndex y) = some y.1 :=
  Classical.choose_spec
    (show ∃ a : Stage κ, L.marker a = some y.1 from y.2)

/-- Choose the unique stage at which a marker vertex was inserted.  The
embedding itself is injective because one stage has only one optional
marker; `markerStage_eq` below uses `MarkersInjective` to show that this
chosen stage is the only possible stage for the vertex. -/
noncomputable def markerStage (L : G.KappaLadder κ) :
    L.markerSet ↪ Stage κ where
  toFun := L.markerStageIndex
  inj' := by
    intro y z hstage
    apply Subtype.ext
    change L.markerStageIndex y = L.markerStageIndex z at hstage
    have hy := L.markerStageIndex_spec y
    have hz := L.markerStageIndex_spec z
    rw [hstage] at hy
    exact Option.some.inj (hy.symm.trans hz)

@[simp]
theorem markerStage_spec (L : G.KappaLadder κ) (y : L.markerSet) :
    L.marker (L.markerStage y) = some y.1 :=
  L.markerStageIndex_spec y

/-- Marker-stage uniqueness, derived from the construction's freshness
law. -/
theorem markerStage_eq (L : G.KappaLadder κ) (hL : L.MarkersInjective)
    {a : Stage κ} {y : V} (hy : L.marker a = some y) :
    L.markerStage ⟨y, a, hy⟩ = a :=
  hL (L.markerStage_spec ⟨y, a, hy⟩) hy

/-- The union of all ladder roofs `RF(ℓᵃℓ L)`. -/
def limitRoof (L : G.KappaLadder κ) : Set V :=
  ⋃ a : Stage κ, G.roof (L.frontier a)

/-- The union of all strict ladder roofs `RF°(ℓᵃℓ L)`. -/
def limitStrictRoof (L : G.KappaLadder κ) : Set V :=
  ⋃ a : Stage κ, G.strictRoof (L.frontier a)

/-- The source region `V^α = RF(T_α)`. -/
def upperRegion (L : G.KappaLadder κ) (a : Stage κ) : Set V :=
  G.roof (L.frontier a)

/-- The surviving region `V_α = V \ RF°(T_α)`. -/
def lowerRegion (L : G.KappaLadder κ) (a : Stage κ) : Set V :=
  (G.strictRoof (L.frontier a))ᶜ

/-- Every frontier is its own essential part (the minimal-separator part of
source Lemmas 7.10--7.11). -/
def FrontiersAreEssential (L : G.KappaLadder κ) : Prop :=
  ∀ a : Stage κ, G.essential (L.frontier a) = L.frontier a

/-- Later frontiers roof earlier frontiers (source Lemma 7.10). -/
def HasFrontierChronology (L : G.KappaLadder κ) : Prop :=
  ∀ {a b : Stage κ}, a < b → L.frontier a ⊆ G.roof (L.frontier b)

/-- A later frontier avoids the strict roof of every earlier frontier. -/
def HasStrictFrontierChronology (L : G.KappaLadder κ) : Prop :=
  ∀ {a b : Stage κ}, a < b →
    Disjoint (G.strictRoof (L.frontier a)) (L.frontier b)

/-- Source Lemma 7.16: the boundary of the union of ladder roofs consists
exactly of vertices which lie on every sufficiently late frontier. -/
theorem mem_limitRoof_diff_limitStrictRoof_iff_eventually_frontier
    (L : G.KappaLadder κ)
    (hessential : L.FrontiersAreEssential)
    (hchron : L.HasFrontierChronology)
    (hstrict : L.HasStrictFrontierChronology) (v : V) :
    v ∈ L.limitRoof \ L.limitStrictRoof ↔
      ∃ a : Stage κ, ∀ b : Stage κ, a ≤ b → v ∈ L.frontier b := by
  constructor
  · rintro ⟨hvRoof, hvNotStrict⟩
    obtain ⟨a, hva⟩ := Set.mem_iUnion.1 hvRoof
    refine ⟨a, fun b hab ↦ ?_⟩
    have hvbRoof : v ∈ G.roof (L.frontier b) := by
      rcases hab.lt_or_eq with hab | rfl
      · exact G.roof_cut (hchron hab) hva
      · exact hva
    have hvbNotStrict : v ∉ G.strictRoof (L.frontier b) := by
      intro hv
      exact hvNotStrict (Set.mem_iUnion.2 ⟨b, hv⟩)
    have hvEssential : v ∈ G.essential (L.frontier b) := by
      by_contra hvNotEssential
      exact hvbNotStrict ⟨hvbRoof, hvNotEssential⟩
    rwa [hessential b] at hvEssential
  · rintro ⟨a, ha⟩
    constructor
    · exact Set.mem_iUnion.2 ⟨a, G.subset_roof _ (ha a le_rfl)⟩
    · intro hvStrict
      obtain ⟨b, hvb⟩ := Set.mem_iUnion.1 hvStrict
      rcases lt_or_ge b a with hba | hab
      · exact Set.disjoint_left.1 (hstrict hba) hvb (ha a le_rfl)
      · have hvaEssential : v ∈ G.essential (L.frontier b) := by
          rw [hessential b]
          exact ha b hab
        exact hvb.2 hvaEssential

/-- The exact persistence conclusion of source Lemma 7.4.  A path chosen
at `α` lies in `IE(Y_β)` for every `β ≥ α+1`, including limit
stages.  The arrow/liminf construction proves this predicate. -/
def RecordedPathsPersist (L : G.KappaLadder κ) : Prop :=
  ∀ (a : Stage κ) (p : G.DPath), L.chosen a = some p →
    ∀ b : ExtendedStage κ, Ladder.Stage.succExtended a ≤ b →
      p ∈ G.inessentialPaths (L.accumulated b)

/-- Inessential paths at a stage remain inessential after the next arrow
step. -/
def CurrentInessentialPersists (L : G.KappaLadder κ) : Prop :=
  ∀ a : Stage κ,
    G.inessentialPaths (L.warpAt a) ⊆
      G.inessentialPaths (L.successorWarp a)

/-- Every accumulated frontier still roofs the original source.  Marker
components may start outside the original source, so accumulated families
and their essential parts need not themselves be waves; this is the exact
separation invariant actually used by the quotient-stage construction. -/
def RoofsSourceAtStages (L : G.KappaLadder κ) : Prop :=
  ∀ a : ExtendedStage κ,
    G.source ⊆ G.roof (G.terminalFrontier (L.accumulated a))

/-- Source-faithful legality conditions for raw ladder data.

This structure records only construction laws.  In particular it contains
no stationary-set conclusion and no assertion that a grounding wave or
hindrance exists. -/
structure IsLegal (L : G.KappaLadder κ) : Prop where
  regular : κ.IsRegular
  uncountable : ℵ₀ < κ
  initialStage : L.HasInitialStage
  limitStages : L.HasLimitStages
  warpStages : L.HasWarpStages
  waveRungs : L.HasWaveRungs
  roofMaximalRungs : L.HasRoofMaximalRungs
  exactSuccessorArrows : L.HasExactSuccessorArrows
  freshMarkers : L.HasFreshMarkers
  markersInjective : L.MarkersInjective
  marksTime : L.MarksTimeAfterExhaustion
  validBookkeeping : L.HasValidBookkeeping
  hangingProvenance : L.HasHangingProvenance
  recordedPathsPersist : L.RecordedPathsPersist
  currentInessentialPersists : L.CurrentInessentialPersists
  roofsSourceAtStages : L.RoofsSourceAtStages
  frontiersEssential : L.FrontiersAreEssential
  frontierChronology : L.HasFrontierChronology
  strictFrontierChronology : L.HasStrictFrontierChronology

/-- Legal-ladder form of source Lemma 7.16. -/
theorem IsLegal.mem_limitRoof_diff_limitStrictRoof_iff_eventually_frontier
    {L : G.KappaLadder κ} (hL : L.IsLegal) (v : V) :
    v ∈ L.limitRoof \ L.limitStrictRoof ↔
      ∃ a : Stage κ, ∀ b : Stage κ, a ≤ b → v ∈ L.frontier b :=
  L.mem_limitRoof_diff_limitStrictRoof_iff_eventually_frontier
    hL.frontiersEssential hL.frontierChronology
    hL.strictFrontierChronology v

/-- Strict roofs of ladder frontiers increase with the stage.  This is the
roof-calculus step used to pass from source Lemma 7.19 to Lemma 7.20. -/
theorem IsLegal.strictRoof_frontier_mono
    {L : G.KappaLadder κ} (hL : L.IsLegal)
    {a b : Stage κ} (hab : a ≤ b) :
    G.strictRoof (L.frontier a) ⊆ G.strictRoof (L.frontier b) := by
  rcases hab.lt_or_eq with hab | rfl
  · intro x hx
    constructor
    · exact G.roof_cut (hL.frontierChronology hab) hx.1
    · intro hxEssential
      have hxFrontier : x ∈ L.frontier b := by
        rw [← hL.frontiersEssential b]
        exact hxEssential
      exact Set.disjoint_left.1 (hL.strictFrontierChronology hab)
        hx hxFrontier
  · exact fun _ hx ↦ hx

theorem IsRungArrowPair.extends {L : G.KappaLadder κ} {a : Stage κ}
    {p q : G.DPath} (h : L.IsRungArrowPair a p q) : G.Extends p q := by
  rcases h with ⟨_, rfl⟩ | ⟨x, _, hcontinue | hfixed⟩
  · exact G.extends_refl q
  · obtain ⟨r, _, _hrung, _hterminal, hext, _hsupport, _hedges, _hfinish⟩ :=
      hcontinue
    exact hext
  · exact hfixed.2 ▸ G.extends_refl p

/-- Compatibility projection: exact successor arrows in particular extend
every old path. -/
theorem IsLegal.successorExtensions {L : G.KappaLadder κ}
    (hL : L.IsLegal) (a : Stage κ) (p : G.DPath) (hp : p ∈ L.warpAt a) :
    ∃ q ∈ L.successorWarp a, G.Extends p q := by
  obtain ⟨q, hq, _⟩ := (hL.exactSuccessorArrows a).1.1 p hp
  exact ⟨q, hq.1.1, hq.2.extends⟩

/-- Each old component has exactly one non-marker successor component, and
that component is its exact rung-arrow image. -/
theorem IsLegal.existsUniqueSuccessorArrow {L : G.KappaLadder κ}
    (hL : L.IsLegal) (a : Stage κ) (p : G.DPath) (hp : p ∈ L.warpAt a) :
    ∃! q : G.DPath,
      (q ∈ L.successorWarp a ∧ q ∉ L.markerPathSet a) ∧
        L.IsRungArrowPair a p q := by
  simpa only [arrowPart, Set.mem_sdiff] using
    (hL.exactSuccessorArrows a).1.1 p hp

/-- Exhaustive provenance for successor components: every component is
either the rung-arrow image of an old component or the one explicitly
chosen marker singleton.  Thus the exact successor clause permits no
extraneous components. -/
theorem IsLegal.successorComponentProvenance {L : G.KappaLadder κ}
    (hL : L.IsLegal) (a : Stage κ) (q : G.DPath)
    (hq : q ∈ L.successorWarp a) :
    (∃ p ∈ L.warpAt a, L.IsRungArrowPair a p q) ∨
      ∃ y : V, L.marker a = some y ∧ q = G.trivialPath y := by
  rw [(hL.exactSuccessorArrows a).2] at hq
  rcases hq with hq | hq
  · exact Or.inl ((hL.exactSuccessorArrows a).1.2 q hq)
  · cases hmarker : L.marker a with
    | none => simp [markerPathSet, hmarker] at hq
    | some y =>
        refine Or.inr ⟨y, rfl, ?_⟩
        simpa [markerPathSet, hmarker] using hq

/-- A legal ladder is a `κ`-hindrance when its obstruction set is
stationary. -/
structure IsKappaHindrance (L : G.KappaLadder κ) : Prop where
  legal : L.IsLegal
  stationary : Stationary.IsStationaryBelow κ L.phi

/-- The path selected at an obstruction stage. -/
noncomputable def selectedPath (L : G.KappaLadder κ)
    (hvalid : L.HasValidBookkeeping) (a : L.phi) : G.DPath :=
  Classical.choose ((L.bookkeeping.mem_phi_iff_exists_chosen hvalid).1 a.2)

@[simp]
theorem chosen_selectedPath (L : G.KappaLadder κ)
    (hvalid : L.HasValidBookkeeping) (a : L.phi) :
    L.chosen a.1 = some (L.selectedPath hvalid a) :=
  Classical.choose_spec
    ((L.bookkeeping.mem_phi_iff_exists_chosen hvalid).1 a.2)

/-- The earlier marker stage supporting a hanging selected path.  It is
totalized by the identity away from hanging stages so that Fodor's lemma
can be applied directly. -/
noncomputable def hangingOrigin (L : G.KappaLadder κ)
    (hlegal : L.IsLegal) (a : Stage κ) : Stage κ := by
  classical
  exact if ha : a ∈ L.phiHanging then
    Classical.choose (hlegal.hangingProvenance a ha
      (L.selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩)
      (L.chosen_selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩))
  else a

theorem hangingOrigin_spec (L : G.KappaLadder κ) (hlegal : L.IsLegal)
    {a : Stage κ} (ha : a ∈ L.phiHanging) :
    L.hangingOrigin hlegal a < a ∧
      L.marker (L.hangingOrigin hlegal a) =
        some (L.selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩).initial := by
  rw [hangingOrigin, dif_pos ha]
  exact Classical.choose_spec (hlegal.hangingProvenance a ha
    (L.selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩)
    (L.chosen_selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩))

theorem hangingOrigin_regressive (L : G.KappaLadder κ)
    (hlegal : L.IsLegal) :
    Stationary.IsRegressiveOn L.phiHanging (L.hangingOrigin hlegal) :=
  fun _ ha ↦ (L.hangingOrigin_spec hlegal ha).1

/-- The source proof of Lemma 7.15: equal marker origins force equal
initial vertices; persistence puts both selected paths into the same later
warp, whose disjointness then forces the selected paths and hence their
stages to be equal. -/
theorem hangingOrigin_injOn (L : G.KappaLadder κ)
    (hlegal : L.IsLegal) :
    Set.InjOn (L.hangingOrigin hlegal) L.phiHanging := by
  intro a ha b hb hab
  let pa : G.DPath :=
    L.selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩
  let pb : G.DPath :=
    L.selectedPath hlegal.validBookkeeping ⟨b, hb.1⟩
  have hpa : L.chosen a = some pa :=
    L.chosen_selectedPath hlegal.validBookkeeping ⟨a, ha.1⟩
  have hpb : L.chosen b = some pb :=
    L.chosen_selectedPath hlegal.validBookkeeping ⟨b, hb.1⟩
  have hinitial : pa.initial = pb.initial := by
    have hma := (L.hangingOrigin_spec hlegal ha).2
    have hmb := (L.hangingOrigin_spec hlegal hb).2
    rw [hab] at hma
    exact Option.some.inj (hma.symm.trans hmb)
  rcases lt_trichotomy a b with hablt | rfl | hbalt
  · have hpaIE : pa ∈ G.inessentialPaths (L.successorWarp b) := by
      apply hlegal.recordedPathsPersist a pa hpa
        (Ladder.Stage.succExtended b)
      change a.1 + 1 ≤ b.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hablt.le
    have hpaWarp : pa ∈ L.successorWarp b := hpaIE.1
    have hpbWarp : pb ∈ L.successorWarp b :=
      ((L.bookkeeping.chosen_mem_available
        hlegal.validBookkeeping hpb).1).1
    by_cases hp : pa = pb
    · exact L.bookkeeping.chosen_stage_unique hlegal.validBookkeeping
        hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hlegal.warpStages (Ladder.Stage.succExtended b)
          hpaWarp hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)
  · rfl
  · have hpbIE : pb ∈ G.inessentialPaths (L.successorWarp a) := by
      apply hlegal.recordedPathsPersist b pb hpb
        (Ladder.Stage.succExtended a)
      change b.1 + 1 ≤ a.1 + 1
      rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
      exact Order.succ_le_succ hbalt.le
    have hpbWarp : pb ∈ L.successorWarp a := hpbIE.1
    have hpaWarp : pa ∈ L.successorWarp a :=
      ((L.bookkeeping.chosen_mem_available
        hlegal.validBookkeeping hpa).1).1
    by_cases hp : pa = pb
    · exact L.bookkeeping.chosen_stage_unique hlegal.validBookkeeping
        hpa (hp ▸ hpb)
    · exact False.elim <| Set.disjoint_left.1
        (hlegal.warpStages (Ladder.Stage.succExtended a)
          hpaWarp hpbWarp hp)
        pa.initial_mem_support (hinitial ▸ pb.initial_mem_support)

/-- Concrete source Lemma 7.15, derived from legal marker provenance. -/
theorem phiHanging_not_stationary_of_legal
    (L : G.KappaLadder κ) (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (hlegal : L.IsLegal) :
    ¬ Stationary.IsStationaryBelow κ L.phiHanging :=
  Stationary.not_isStationaryBelow_of_injOn_regressive hκu hκ
    (L.hangingOrigin_regressive hlegal) (L.hangingOrigin_injOn hlegal)

/-- Concrete source Lemma 7.22: the grounded obstruction stages of a legal
`κ`-hindrance are stationary. -/
theorem IsKappaHindrance.phiGround_isStationary
    (L : G.KappaLadder κ) (hL : L.IsKappaHindrance)
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ) :
    Stationary.IsStationaryBelow κ L.phiGround := by
  have hdecomp : L.phi = L.phiGround ∪ L.phiHanging := by
    ext a
    constructor
    · intro ha
      by_cases hg : a ∈ L.phiGround
      · exact Or.inl hg
      · exact Or.inr ⟨ha, hg⟩
    · rintro (hg | hh)
      · obtain ⟨p, hp, -⟩ := hg
        exact (L.bookkeeping.mem_phi_iff_exists_chosen
          hL.legal.validBookkeeping).2 ⟨p, hp⟩
      · exact hh.1
  have hcof : Order.cof (Stage κ) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκu).ne'
  have hunion : Stationary.IsStationaryBelow κ
      (L.phiGround ∪ L.phiHanging) := by
    rw [← hdecomp]
    exact hL.stationary
  exact (isStationary_union_iff hcof).mp hunion |>.resolve_right
    (L.phiHanging_not_stationary_of_legal hκ hκu hL.legal)

/-- Source Lemma 7.4 in the current-stage indexing used by the emergence
bookkeeping. -/
theorem concreteBookkeeping_isPersistent (L : G.KappaLadder κ)
    (hL : L.RecordedPathsPersist) : L.concreteBookkeeping.IsPersistent := by
  intro a p hp b hab
  change p ∈ G.inessentialPaths (L.warpAt b)
  apply hL a p hp (Ladder.Stage.toExtended b)
  change a.1 + 1 ≤ b.1
  exact (Order.add_one_le_iff).2 hab

/-- Source Lemma 7.18: the first successor-normalized inessential stage of
a selected obstruction path is no later than its selection stage. -/
theorem emergenceIndex_le (L : G.KappaLadder κ)
    (hvalid : L.HasValidBookkeeping) {a : Stage κ} (ha : a ∈ L.phi) :
    L.emergenceIndex hvalid a ≤ a := by
  have ha' : a ∈ L.concreteBookkeeping.phi := by
    rwa [L.concreteBookkeeping_phi]
  exact L.concreteBookkeeping.emergenceIndex_le
    (L.concreteBookkeeping_isValid hvalid) ha'

/-- Source Lemma 7.27 on a concrete legal ladder.  The three local graph
premises are Lemmas 7.6--7.8 respectively: exceptional stages obstruct,
nonexceptional emergence is regressive, and a large inessential family
forces an obstruction tail.  The stationary/fiber argument itself is
fully discharged by `LadderBookkeeping.obstruction_characterization`. -/
theorem stationary_phi_iff_exceptional_or_large
    (L : G.KappaLadder κ) (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (hlegal : L.IsLegal)
    (hexceptional : L.exceptionalStages ⊆ L.phi)
    (hreg : Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hlegal.validBookkeeping))
    (htail : ∀ a ∈ L.largeInessentialStages, Set.Ici a ⊆ L.phi) :
    Stationary.IsStationaryBelow κ L.phi ↔
      Stationary.IsStationaryBelow κ L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty := by
  exact LadderBookkeeping.ConcreteBookkeeping.obstruction_characterization
    hκ hκu L.concreteBookkeeping
      (L.concreteBookkeeping_isValid hlegal.validBookkeeping)
      L.exceptionalStages hexceptional hreg htail

/-- Legal-ladder form of source Lemma 7.27. -/
theorem isKappaHindrance_iff_exceptional_or_large
    (L : G.KappaLadder κ) (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (hlegal : L.IsLegal)
    (hexceptional : L.exceptionalStages ⊆ L.phi)
    (hreg : Stationary.IsRegressiveOn
      (L.phi \ L.exceptionalStages)
      (L.emergenceIndex hlegal.validBookkeeping))
    (htail : ∀ a ∈ L.largeInessentialStages, Set.Ici a ⊆ L.phi) :
    L.IsKappaHindrance ↔
      Stationary.IsStationaryBelow κ L.exceptionalStages ∨
        L.largeInessentialStages.Nonempty := by
  constructor
  · intro hL
    exact (L.stationary_phi_iff_exceptional_or_large hκ hκu hlegal
      hexceptional hreg htail).1 hL.stationary
  · intro hL
    exact ⟨hlegal, (L.stationary_phi_iff_exceptional_or_large hκ hκu
      hlegal hexceptional hreg htail).2 hL⟩

/-- Source Lemma 7.4 in directly usable form. -/
theorem recorded_mem_inessential (L : G.KappaLadder κ)
    (hL : L.RecordedPathsPersist) {a : Stage κ} {p : G.DPath}
    (hp : L.chosen a = some p) {b : ExtendedStage κ}
    (hab : Ladder.Stage.succExtended a ≤ b) :
    p ∈ G.inessentialPaths (L.accumulated b) :=
  hL a p hp b hab

theorem recorded_mem_successor_inessential (L : G.KappaLadder κ)
    (hL : L.RecordedPathsPersist) {a b : Stage κ} {p : G.DPath}
    (hp : L.chosen a = some p) (hab : a ≤ b) :
    p ∈ G.inessentialPaths (L.successorWarp b) := by
  apply hL a p hp (Ladder.Stage.succExtended b)
  change a.1 + 1 ≤ b.1 + 1
  rw [← Order.succ_eq_add_one, ← Order.succ_eq_add_one]
  exact Order.succ_le_succ hab

/-- Two recorded finite paths with the same terminal were recorded at the
same stage.  Persistence places both in a common successor warp, where
warp disjointness forces equality; bookkeeping uniqueness then identifies
their stages. -/
theorem IsLegal.recordedStage_eq_of_same_terminal
    {L : G.KappaLadder κ} (hL : L.IsLegal)
    {a b : Stage κ} {p q : G.DPath} {x : V}
    (hpa : L.chosen a = some p) (hpx : G.terminal? p = some x)
    (hqb : L.chosen b = some q) (hqx : G.terminal? q = some x) :
    a = b := by
  rcases le_total a b with hab | hba
  · have hpWarp : p ∈ L.successorWarp b :=
      (L.recorded_mem_successor_inessential
        hL.recordedPathsPersist hpa hab).1
    have hqWarp : q ∈ L.successorWarp b :=
      ((L.bookkeeping.chosen_mem_available
        hL.validBookkeeping hqb).1).1
    by_cases hpq : p = q
    · subst q
      exact L.bookkeeping.chosen_stage_unique
        hL.validBookkeeping hpa hqb
    · exact False.elim <| Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.succExtended b)
          hpWarp hqWarp hpq)
        (G.terminal_mem_support hpx) (G.terminal_mem_support hqx)
  · have hqWarp : q ∈ L.successorWarp a :=
      (L.recorded_mem_successor_inessential
        hL.recordedPathsPersist hqb hba).1
    have hpWarp : p ∈ L.successorWarp a :=
      ((L.bookkeeping.chosen_mem_available
        hL.validBookkeeping hpa).1).1
    by_cases hpq : p = q
    · subst q
      exact L.bookkeeping.chosen_stage_unique
        hL.validBookkeeping hpa hqb
    · exact False.elim <| Set.disjoint_left.1
        (hL.warpStages (Ladder.Stage.succExtended a)
          hpWarp hqWarp hpq)
        (G.terminal_mem_support hpx) (G.terminal_mem_support hqx)

/-- Stages in a prescribed set whose frontier meets a path. -/
def hitStages (L : G.KappaLadder κ) (Sigma : Set (Stage κ))
    (p : G.DPath) : Set (Stage κ) :=
  {a | a ∈ Sigma ∧ (L.frontier a ∩ p.support).Nonempty}

@[simp]
theorem mem_hitStages {L : G.KappaLadder κ} {Sigma : Set (Stage κ)}
    {p : G.DPath} {a : Stage κ} :
    a ∈ L.hitStages Sigma p ↔
      a ∈ Sigma ∧ (L.frontier a ∩ p.support).Nonempty :=
  Iff.rfl

/-- The roof-theoretic input to the corrected proof of source Lemma 7.28.
If a directed family of earlier hit stages has supremum `a`, but `p`
misses `T_a`, frontier chronology and self-roofed essential prefixes put
the whole of `p` in `IE(Y_a)`. -/
def LimitMissIsInessential (L : G.KappaLadder κ)
    (Sigma : Set (Stage κ)) (p : G.DPath) : Prop :=
  ∀ (d : Set (Stage κ)) (a : Stage κ),
    d ⊆ L.hitStages Sigma p → d.Nonempty → DirectedOn (· ≤ ·) d →
    IsLUB d a → ¬ (L.frontier a ∩ p.support).Nonempty →
      p ∈ G.inessentialPaths (L.warpAt a)

/-- A more primitive limit-stage property: under the hypotheses occurring
in Lemma 7.28, missing the limiting frontier makes the final path an actual
member of the accumulated warp at the supremum.  Once Lemma 7.10 identifies
that frontier with the essential terminal frontier, inessentiality follows
formally. -/
def LimitMissBelongsAtSup (L : G.KappaLadder κ)
    (Sigma : Set (Stage κ)) (p : G.DPath) : Prop :=
  ∀ (d : Set (Stage κ)) (a : Stage κ),
    d ⊆ L.hitStages Sigma p → d.Nonempty → DirectedOn (· ≤ ·) d →
    IsLUB d a → ¬ (L.frontier a ∩ p.support).Nonempty →
      p ∈ L.warpAt a

/-- The limit-membership conclusion plus the frontier identity imply the
roof-theoretic input used in the corrected Lemma 7.28 proof. -/
theorem limitMissIsInessential_of_belongs
    (L : G.KappaLadder κ) (Sigma : Set (Stage κ)) (p : G.DPath)
    (hfrontier : ∀ a : Stage κ,
      G.essential (G.terminalFrontier (L.warpAt a)) = L.frontier a)
    (hbelongs : L.LimitMissBelongsAtSup Sigma p) :
    L.LimitMissIsInessential Sigma p := by
  intro d a hd hdn hdir ha hmiss
  apply G.mem_inessentialPaths_of_misses_essentialFrontier
  · exact hbelongs d a hd hdn hdir ha hmiss
  · rwa [hfrontier a]

/-- Corrected closure argument for source Lemma 7.28.

There is no countability or regularity step.  If the supremum already lies
in the directed family, closure is immediate (this includes finite
families).  Otherwise the family is cofinal below its supremum.  A record
before the supremum would, by Lemma 7.4, be inessential at a later hit
stage; the essential prefix at that hit and warp disjointness give the
finite/ray contradiction.  Thus the path is unrecorded, and persistence to
the successor makes the supremum a `Φ`-stage, contrary to the club's
avoidance of `Φ`. -/
theorem hitStages_isDirSupClosed
    (L : G.KappaLadder κ) (Sigma : Set (Stage κ)) (p : G.DPath)
    (hSigma : DirSupClosed Sigma)
    (hwarps : L.HasWarpStages)
    (hpersist : L.RecordedPathsPersist)
    (hprefix : ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty)
    (hmiss : L.LimitMissIsInessential Sigma p)
    (hsucc : ∀ a : Stage κ,
      p ∈ G.inessentialPaths (L.warpAt a) →
        p ∈ G.inessentialPaths (L.successorWarp a))
    (havoid : Disjoint Sigma L.phi) :
    DirSupClosed (L.hitStages Sigma p) := by
  intro d hd hdn hdir a ha
  have haSigma : a ∈ Sigma := by
    exact hSigma (fun x hx ↦ (hd hx).1) hdn hdir ha
  by_cases hmeet : (L.frontier a ∩ p.support).Nonempty
  · exact ⟨haSigma, hmeet⟩
  have hpCurrent : p ∈ G.inessentialPaths (L.warpAt a) :=
    hmiss d a hd hdn hdir ha hmeet
  have hpNotRecorded : p ∉ L.bookkeeping.recordedBefore a := by
    rintro ⟨b, hba, hb⟩
    have hcofinal : ∃ c ∈ d, b < c := by
      by_contra h
      push Not at h
      have hub : ∀ c ∈ d, c ≤ b := fun c hc ↦ h c hc
      exact (not_le_of_gt hba) (ha.2 hub)
    obtain ⟨c, hc, hbc⟩ := hcofinal
    obtain ⟨q, hq, hpq⟩ := hprefix c (hd hc)
    have hsuccle : Ladder.Stage.succExtended b ≤ Ladder.Stage.toExtended c := by
      change b.1 + 1 ≤ c.1
      exact (Order.add_one_le_iff).2 hbc
    have hpIE : p ∈ G.inessentialPaths (L.warpAt c) :=
      hpersist b p hb (Ladder.Stage.toExtended c) hsuccle
    exact (G.not_mem_inessentialPaths_of_intersects_essential
      (hwarps (Ladder.Stage.toExtended c)) hq hpq) hpIE
  have hpNext : p ∈ G.inessentialPaths (L.successorWarp a) :=
    hsucc a hpCurrent
  have haPhi : a ∈ L.phi :=
    ⟨p, hpNext, hpNotRecorded⟩
  exact (Set.disjoint_left.1 havoid haSigma haPhi).elim

/-- Club-specialized form of source Lemma 7.28. -/
theorem hitStages_isClosed
    (L : G.KappaLadder κ) (Sigma : Set (Stage κ)) (p : G.DPath)
    (hSigma : Stationary.IsClubBelow κ Sigma)
    (hwarps : L.HasWarpStages)
    (hpersist : L.RecordedPathsPersist)
    (hprefix : ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty)
    (hmiss : L.LimitMissIsInessential Sigma p)
    (hsucc : ∀ a : Stage κ,
      p ∈ G.inessentialPaths (L.warpAt a) →
        p ∈ G.inessentialPaths (L.successorWarp a))
    (havoid : Disjoint Sigma L.phi) :
    DirSupClosed (L.hitStages Sigma p) :=
  L.hitStages_isDirSupClosed Sigma p hSigma.dirSupClosed hwarps hpersist
    hprefix hmiss hsucc havoid

/-- Legal-ladder form of the corrected source Lemma 7.28.  The remaining
two hypotheses are the path-local consequences of the stage-web lift:
each hit supplies an essential prefix, and a missed limiting frontier puts
the path in the current inessential part. -/
theorem hitStages_isClosed_of_legal
    (L : G.KappaLadder κ) (hlegal : L.IsLegal)
    (Sigma : Set (Stage κ)) (p : G.DPath)
    (hSigma : Stationary.IsClubBelow κ Sigma)
    (hprefix : ∀ a ∈ L.hitStages Sigma p,
      ∃ q ∈ G.essentialWarpPart (L.warpAt a),
        (p.support ∩ q.support).Nonempty)
    (hmiss : L.LimitMissIsInessential Sigma p)
    (havoid : Disjoint Sigma L.phi) :
    DirSupClosed (L.hitStages Sigma p) :=
  L.hitStages_isClosed Sigma p hSigma hlegal.warpStages
    hlegal.recordedPathsPersist hprefix hmiss
    (fun a hp ↦ hlegal.currentInessentialPersists a hp) havoid

end KappaLadder

end DWeb

namespace Ladder

variable {κ : Cardinal.{u}} {Path : Type v}

/-! ## Grounded and hanging stages -/

section Grounded

variable (B : Bookkeeping κ Path)
variable {Vertex : Type*} (initial : Path → Vertex) (ground : Set Vertex)

/-- Obstruction stages whose selected path starts in the original source
set. -/
def phiGround : Set (Stage κ) :=
  {α | ∃ p, B.chosen α = some p ∧ initial p ∈ ground}

/-- Obstruction stages whose selected path starts at an earlier marker. -/
def phiHanging : Set (Stage κ) :=
  B.phi \ phiGround B initial ground

@[simp]
theorem mem_phiGround {α : Stage κ} :
    α ∈ phiGround B initial ground ↔
      ∃ p, B.chosen α = some p ∧ initial p ∈ ground :=
  Iff.rfl

@[simp]
theorem mem_phiHanging {α : Stage κ} :
    α ∈ phiHanging B initial ground ↔
      α ∈ B.phi ∧ α ∉ phiGround B initial ground :=
  Iff.rfl

theorem phi_eq_ground_union_hanging (hB : B.IsValid) :
    B.phi = phiGround B initial ground ∪ phiHanging B initial ground := by
  ext α
  constructor
  · intro hα
    by_cases hg : α ∈ phiGround B initial ground
    · exact Or.inl hg
    · exact Or.inr ⟨hα, hg⟩
  · rintro (hg | hh)
    · obtain ⟨p, hp, -⟩ := hg
      exact (B.mem_phi_iff_exists_chosen hB).2 ⟨p, hp⟩
    · exact hh.1

end Grounded

/-! ## The stationary provenance argument (source Lemmas 7.15 and 7.22) -/

/-- A stationary subset of a regular uncountable cardinal cannot be
subsingleton. -/
theorem stationary_not_subsingleton (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    {S : Set (Stage κ)} (hS : Stationary.IsStationaryBelow κ S) :
    ¬ S.Subsingleton := by
  intro hsub
  exact Stationary.not_isStationaryBelow_of_countable hκ hκu hsub.countable hS

/-- An injective regressive image cannot have stationary domain.  This is
the exact set-theoretic core of the hanging-stage argument. -/
theorem not_stationary_of_regressive_injective
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    {S : Set (Stage κ)} {f : Stage κ → Stage κ}
    (hreg : Stationary.IsRegressiveOn S f) (hinj : Set.InjOn f S) :
    ¬ Stationary.IsStationaryBelow κ S := by
  intro hS
  obtain ⟨i, hi⟩ := Stationary.pressingDown hκu hκ hS hreg
  apply stationary_not_subsingleton hκ hκu hi
  rintro α ⟨hαS, hαi⟩ β ⟨hβS, hβi⟩
  exact hinj hαS hβS (hαi.trans hβi.symm)

/-- Hanging obstruction stages are nonstationary when marker provenance is
an injective regressive map (source Lemma 7.15). -/
theorem phiHanging_not_stationary
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (B : Bookkeeping κ Path) {Vertex : Type*}
    (initial : Path → Vertex) (ground : Set Vertex)
    (origin : Stage κ → Stage κ)
    (hreg : Stationary.IsRegressiveOn (phiHanging B initial ground) origin)
    (hinj : Set.InjOn origin (phiHanging B initial ground)) :
    ¬ Stationary.IsStationaryBelow κ (phiHanging B initial ground) :=
  not_stationary_of_regressive_injective hκ hκu hreg hinj

/-- If `Φ` is stationary and the hanging part is nonstationary, then the
grounded part is stationary (source Lemma 7.22). -/
theorem phiGround_isStationary
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (B : Bookkeeping κ Path) (hB : B.IsValid)
    {Vertex : Type*} (initial : Path → Vertex) (ground : Set Vertex)
    (hphi : Stationary.IsStationaryBelow κ B.phi)
    (hhang : ¬ Stationary.IsStationaryBelow κ
      (phiHanging B initial ground)) :
    Stationary.IsStationaryBelow κ (phiGround B initial ground) := by
  have hcof : Order.cof (Stage κ) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκu).ne'
  have hu : Stationary.IsStationaryBelow κ
      (phiGround B initial ground ∪ phiHanging B initial ground) := by
    rw [← phi_eq_ground_union_hanging B initial ground hB]
    exact hphi
  exact (isStationary_union_iff hcof).mp hu |>.resolve_right hhang

end Ladder
end Erdos599
