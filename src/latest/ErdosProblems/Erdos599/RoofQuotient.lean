/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Core
import ErdosProblems.Erdos599.ConcreteWave
import ErdosProblems.Erdos599.RelationalRoof
import ErdosProblems.Erdos599.WarpLimits

/-!
# Roof and quotient lemmas for Erdős Problem 599

This file develops the concrete roof calculus used in Sections 2 and 3 of
Aharoni--Berger.  In particular it contains the last-roof-point lemma,
stability of the essential part, the two-set roof lemma, and the normalized
quotient support facts.  All paths below are the concrete simple directed
paths from `DirectedPath.lean`.
-/

namespace Erdos599

open Set
open DirectedPath

universe u v

namespace DirectedPath

variable {V : Type u} {D : Digraph V}

namespace Ray

/-- Prepend one fresh vertex and edge to a ray. -/
def prepend {u : V} (r : Ray D) (e : D.Adj u r.initial)
    (hu : u ∉ r.support) : Ray D where
  toFun
    | 0 => u
    | n + 1 => r n
  adj_succ n := by
    cases n with
    | zero => exact e
    | succ n => simpa using r.adj_succ n
  injective := by
    intro m n hmn
    cases m with
    | zero =>
        cases n with
        | zero => rfl
        | succ n => exact (hu ⟨n, hmn.symm⟩).elim
    | succ m =>
        cases n with
        | zero => exact (hu ⟨m, hmn⟩).elim
        | succ n => exact congrArg Nat.succ (r.injective hmn)

@[simp]
theorem prepend_zero {u : V} (r : Ray D) (e : D.Adj u r.initial)
    (hu : u ∉ r.support) : r.prepend e hu 0 = u :=
  rfl

@[simp]
theorem prepend_succ {u : V} (r : Ray D) (e : D.Adj u r.initial)
    (hu : u ∉ r.support) (n : ℕ) : r.prepend e hu (n + 1) = r n :=
  rfl

@[simp]
theorem initial_prepend {u : V} (r : Ray D) (e : D.Adj u r.initial)
    (hu : u ∉ r.support) : (r.prepend e hu).initial = u :=
  rfl

theorem support_prepend {u : V} (r : Ray D) (e : D.Adj u r.initial)
    (hu : u ∉ r.support) : (r.prepend e hu).support = insert u r.support := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl hn.symm
    | succ n => exact Or.inr ⟨n, hn⟩
  · rintro (rfl | ⟨n, rfl⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨n + 1, rfl⟩

end Ray

namespace Path

/-- Prepend one fresh vertex and edge to a finite path or ray. -/
def prepend {u : V} (q : Path D) (e : D.Adj u q.initial)
    (hu : u ∉ q.support) : Path D := by
  rcases q with q | r
  · change D.Adj u q.start at e
    change u ∉ q.support at hu
    exact .inl
      { start := u
        finish := q.finish
        walk := .cons e q.walk
        isPath := by
          change (u :: q.walk.support).Nodup
          exact List.nodup_cons.2 ⟨hu, q.isPath⟩ }
  · exact .inr (r.prepend e hu)

@[simp]
theorem initial_prepend {u : V} (q : Path D) (e : D.Adj u q.initial)
    (hu : u ∉ q.support) : (q.prepend e hu).initial = u := by
  rcases q with q | r <;> rfl

@[simp]
theorem terminal?_prepend {u : V} (q : Path D) (e : D.Adj u q.initial)
    (hu : u ∉ q.support) : (q.prepend e hu).terminal? = q.terminal? := by
  rcases q with q | r <;> rfl

theorem support_prepend {u : V} (q : Path D) (e : D.Adj u q.initial)
    (hu : u ∉ q.support) : (q.prepend e hu).support = insert u q.support := by
  rcases q with q | r
  · ext x
    change x ∈ u :: q.walk.support ↔ x = u ∨ x ∈ q.walk.support
    simp
  · exact r.support_prepend e hu

end Path

end DirectedPath

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-! ## Concrete specializations of the relational roof calculus -/

/-- The concrete and relation-generic roof definitions are definitionally
the same after specializing the relation to the web adjacency relation. -/
theorem roof_eq_relational (S : Set V) :
    G.roof S = RelationalRoof.roof G.graph.Adj G.target S := rfl

/-- The corresponding essential-frontier definitions also coincide. -/
theorem essential_eq_relational (S : Set V) :
    G.essential S = RelationalRoof.essential G.graph.Adj G.target S := rfl

/-- Aharoni--Berger Lemma 2.14, specialized to a concrete web. -/
theorem roof_essential_eq (S : Set V) :
    G.roof (G.essential S) = G.roof S :=
  RelationalRoof.roof_essential G.graph.Adj G.target S

/-- Aharoni--Berger Lemma 2.16, specialized to a concrete web. -/
theorem canonicalLastRoofHit_mem_essential_or_finish
    (S : Set V) (p : FinitePath G.graph) (hmeet : G.Meets p (G.roof S)) :
    let hmeet' : p.walk.Meets (G.roof S) :=
      ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
    let L := Walk.lastHit p.walk (G.roof S) hmeet'
    L.startpoint ∈ G.essential S ∪ {p.finish} := by
  exact RelationalRoof.lastRoofHit_mem_essential_or_finish
    G.graph.Adj G.target S p _

/-- Aharoni--Berger Lemma 2.17, specialized to a concrete web. -/
theorem essential_eq_of_essential_subset_of_subset
    {C D : Set V} (hEss : G.essential D ⊆ C) (hCD : C ⊆ D) :
    G.essential C = G.essential D :=
  RelationalRoof.essential_sandwich G.graph.Adj G.target hEss hCD

/-- Essential-frontier form of Aharoni--Berger Observation 2.18. -/
theorem essential_union_eq_of_cross_roof
    {S T X Y : Set V} (hXY : Disjoint X Y)
    (hX : X ⊆ G.roof (T ∪ Y)) (hY : Y ⊆ G.roof (S ∪ X)) :
    G.essential (S ∪ T ∪ X ∪ Y) = G.essential (S ∪ T) :=
  RelationalRoof.essential_mutual_roofing G.graph.Adj G.target hXY hX hY

/-- Roof form of Aharoni--Berger Observation 2.18. -/
theorem union_subset_roof_of_cross_roof
    {S T X Y : Set V} (hXY : Disjoint X Y)
    (hX : X ⊆ G.roof (T ∪ Y)) (hY : Y ⊆ G.roof (S ∪ X)) :
    X ∪ Y ⊆ G.roof (S ∪ T) :=
  RelationalRoof.mutual_roofing G.graph.Adj G.target hXY hX hY

/-- The concrete-web notation for relation-generic separation. -/
def SeparatesBetween (R T S : Set V) : Prop :=
  RelationalRoof.Separates G.graph.Adj R T S

/-- Aharoni--Berger Lemma 2.19, specialized to a concrete web. -/
theorem separatesBetween_of_roof_chain
    {R S T : Set V} (htrim : T = G.essential T)
    (hRS : G.roof R ⊆ G.roof S) (hST : G.roof S ⊆ G.roof T) :
    G.SeparatesBetween R T S :=
  RelationalRoof.nested_roofs_separate G.graph.Adj G.target htrim hRS hST

/-! ## Limits of roofs -/

/-- Aharoni--Berger Lemma 2.21.  For a linearly ordered family in which
each earlier set is roofed by every later set, the roof of the eventual
set-liminf contains the roof of every stage. -/
theorem iUnion_roof_subset_roof_setLiminf
    {I : Type v} [LinearOrder I] [Nonempty I]
    (S : I → Set V)
    (hchain : ∀ {i j}, i < j → S i ⊆ G.roof (S j)) :
    (⋃ i, G.roof (S i)) ⊆
      G.roof (WarpLimits.setLiminf S) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hx
  intro p hp
  have hmeetSi : G.Meets p (S i) := hxi p hp
  have hmeetUnion : G.Meets p (⋃ j, S j) := by
    obtain ⟨w, hwp, hwSi⟩ := hmeetSi
    exact ⟨w, hwp, Set.mem_iUnion.2 ⟨i, hwSi⟩⟩
  let hwMeet : p.walk.Meets (⋃ j, S j) :=
    ⟨hmeetUnion.choose, hmeetUnion.choose_spec.1, hmeetUnion.choose_spec.2⟩
  let L := Walk.lastHit p.walk (⋃ j, S j) hwMeet
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 L.startpoint_mem
  refine ⟨L.startpoint, L.support_subset L.walk.start_mem_support, ?_⟩
  rw [WarpLimits.mem_setLiminf]
  refine ⟨k, fun j hkj ↦ ?_⟩
  rcases hkj.eq_or_lt with rfl | hkj
  · exact hk
  · let q : FinitePath G.graph :=
      { start := L.startpoint
        finish := p.finish
        walk := L.walk
        isPath := L.isPath p.isPath }
    have hq : G.IsTargetPathFrom L.startpoint q := ⟨rfl, hp.2⟩
    obtain ⟨w, hwq, hwSj⟩ := hchain hkj hk q hq
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      G.graph.Adj L.walk).1 hwq with hw | hw
    · simpa only [hw] using hwSj
    · exact (L.no_mem_after hw (Set.mem_iUnion.2 ⟨j, hwSj⟩)).elim

/-! ## The trimmed web and normalized quotient -/

/-- The web `G[S]` of Aharoni--Berger Definition 2.20: retain the subgraph on
`S`, use `S ∩ source` as its source, and use `essential S` as its target.
The accompanying hypothesis `roof S = S` is imposed by lemmas using this
construction, not by the data constructor. -/
def trimWeb (S : Set V) : DWeb V where
  graph := inducedGraph G.graph S
  source := S ∩ G.source
  target := G.essential S

@[simp] theorem trimWeb_source (S : Set V) :
    (G.trimWeb S).source = S ∩ G.source := rfl

@[simp] theorem trimWeb_target (S : Set V) :
    (G.trimWeb S).target = G.essential S := rfl

/-- The concrete vertex region represented by a same-type quotient. -/
def quotientVertexSet (S : Set V) : Set V := (G.strictRoof S)ᶜ

/-- Every nontrivial quotient edge has both endpoints in the quotient vertex
region, and its destination is outside the commitment set. -/
theorem quotient_adj_endpoints {S : Set V} {x y : V}
    (hxy : (G.quotient S).graph.Adj x y) :
    x ∈ G.quotientVertexSet S ∧ y ∈ G.quotientVertexSet S ∧ y ∉ S :=
  ⟨hxy.2.1, hxy.2.2.1, hxy.2.2.2⟩

/-- Any vertex of a quotient path other than its initial vertex lies outside
both the strict roof and the commitment set. -/
theorem quotientWalk_tail_avoids {S : Set V} {a b : V}
    (p : Walk (G.quotient S).graph a b) :
    ∀ {x}, x ∈ p.support.tail → x ∉ G.strictRoof S ∧ x ∉ S := by
  induction p with
  | nil => simp
  | @cons u v w e p ih =>
      intro x hx
      simp only [Walk.support_cons, List.tail_cons] at hx
      have hx' : x = v ∨ x ∈ p.support.tail := by
        cases p <;> simpa using hx
      exact hx'.elim (fun h ↦ h ▸ e.2.2) (fun h ↦ ih h)

/-! ### Restricting an actual traversed walk to a quotient -/

/-- Convert an original walk to the quotient from exactly the conditions
needed on its traversed vertices: all vertices survive strict-roof deletion,
and every vertex after the initial one lies outside the commitment set.
Unlike a condition on the ambient graph, this imposes nothing on unused
chords between support vertices. -/
def restrictWalkToQuotient (T : Set V) :
    ∀ {a b : V} (p : Walk G.graph a b),
      (∀ {x}, x ∈ p.support → x ∉ G.strictRoof T) →
      (∀ {x}, x ∈ p.support.tail → x ∉ T) →
      Walk (G.quotient T).graph a b
  | _, _, .nil, _, _ => .nil
  | _, _, .cons e p, hstrict, hcommit =>
      .cons
        ⟨e,
          hstrict (by simp),
          hstrict (by simp),
          hcommit (by simpa using p.start_mem_support)⟩
        (restrictWalkToQuotient T p
          (fun {_} hx hbad ↦ hstrict (by simp [hx]) hbad)
          (fun {_} hx hbad ↦ hcommit (by
            simp only [Walk.support_cons, List.tail_cons]
            exact List.mem_of_mem_tail hx) hbad))

@[simp]
theorem support_restrictWalkToQuotient (T : Set V) {a b : V}
    (p : Walk G.graph a b)
    (hstrict : ∀ {x}, x ∈ p.support → x ∉ G.strictRoof T)
    (hcommit : ∀ {x}, x ∈ p.support.tail → x ∉ T) :
    (G.restrictWalkToQuotient T p hstrict hcommit).support = p.support := by
  induction p with
  | nil => rfl
  | @cons u v w e p ih =>
      let hs : ∀ {x}, x ∈ p.support → x ∉ G.strictRoof T :=
        fun {_} hx hbad ↦ hstrict (by simp [hx]) hbad
      let hc : ∀ {x}, x ∈ p.support.tail → x ∉ T :=
        fun {_} hx hbad ↦ hcommit (List.mem_of_mem_tail hx) hbad
      change u :: (G.restrictWalkToQuotient T p hs hc).support = u :: p.support
      rw [ih hs hc]

/-- Bundle `restrictWalkToQuotient` for a finite simple path. -/
def restrictFinitePathToQuotient (T : Set V) (p : FinitePath G.graph)
    (hstrict : ∀ {x}, x ∈ p.walk.support → x ∉ G.strictRoof T)
    (hcommit : ∀ {x}, x ∈ p.walk.support.tail → x ∉ T) :
    FinitePath (G.quotient T).graph where
  start := p.start
  finish := p.finish
  walk := G.restrictWalkToQuotient T p.walk hstrict hcommit
  isPath := by
    rw [Walk.isPath_iff, G.support_restrictWalkToQuotient]
    exact p.isPath

@[simp]
theorem support_restrictFinitePathToQuotient (T : Set V)
    (p : FinitePath G.graph)
    (hstrict : ∀ {x}, x ∈ p.walk.support → x ∉ G.strictRoof T)
    (hcommit : ∀ {x}, x ∈ p.walk.support.tail → x ∉ T) :
    (G.restrictFinitePathToQuotient T p hstrict hcommit).support = p.support := by
  ext x
  change x ∈ (G.restrictWalkToQuotient T p.walk hstrict hcommit).support ↔
    x ∈ p.walk.support
  rw [G.support_restrictWalkToQuotient]

/-- A ray is pathwise admissible for the quotient when every one of its
vertices survives strict-roof deletion and every traversed edge has its
head outside the commitment set. -/
def RayQuotientAdmissible (T : Set V) (r : Ray G.graph) : Prop :=
  (∀ n, r n ∉ G.strictRoof T) ∧ ∀ n, r (n + 1) ∉ T

/-- Restrict a pathwise-admissible ray to the quotient graph. -/
def restrictRayToQuotient (T : Set V) (r : Ray G.graph)
    (h : G.RayQuotientAdmissible T r) : Ray (G.quotient T).graph where
  toFun := r.toFun
  adj_succ n := ⟨r.adj_succ n, h.1 n, h.1 (n + 1), h.2 n⟩
  injective := r.injective

@[simp]
theorem support_restrictRayToQuotient (T : Set V) (r : Ray G.graph)
    (h : G.RayQuotientAdmissible T r) :
    (G.restrictRayToQuotient T r h).support = r.support :=
  rfl

@[simp]
theorem initial_restrictRayToQuotient (T : Set V) (r : Ray G.graph)
    (h : G.RayQuotientAdmissible T r) :
    (G.restrictRayToQuotient T r h).initial = r.initial :=
  rfl

/-- The exact traversed-edge admissibility predicate for a finite path or
ray.  This is weaker than `QuotientAdmissible`: it constrains only edges
actually used by the path, never unused chords of its support. -/
def PathQuotientAdmissible (T : Set V) : G.DPath → Prop
  | .inl p =>
      (∀ {x}, x ∈ p.walk.support → x ∉ G.strictRoof T) ∧
        ∀ {x}, x ∈ p.walk.support.tail → x ∉ T
  | .inr r => G.RayQuotientAdmissible T r

/-- Restrict an actual finite path or ray to the quotient using only its
traversed edges. -/
def restrictPathToQuotient (T : Set V) (p : G.DPath)
    (h : G.PathQuotientAdmissible T p) : (G.quotient T).DPath := by
  rcases p with p | r
  · exact .inl (G.restrictFinitePathToQuotient T p h.1 h.2)
  · exact .inr (G.restrictRayToQuotient T r (by
      simpa [PathQuotientAdmissible] using h))

@[simp]
theorem support_restrictPathToQuotient (T : Set V) (p : G.DPath)
    (h : G.PathQuotientAdmissible T p) :
    (G.restrictPathToQuotient T p h).support = p.support := by
  rcases p with p | r
  · exact G.support_restrictFinitePathToQuotient T p h.1 h.2
  · exact G.support_restrictRayToQuotient T r (by
      simpa [PathQuotientAdmissible] using h)

@[simp]
theorem initial_restrictPathToQuotient (T : Set V) (p : G.DPath)
    (h : G.PathQuotientAdmissible T p) :
    (G.restrictPathToQuotient T p h).initial = p.initial := by
  rcases p with p | r <;> rfl

@[simp]
theorem terminal_restrictPathToQuotient (T : Set V) (p : G.DPath)
    (h : G.PathQuotientAdmissible T p) :
    (G.quotient T).terminal? (G.restrictPathToQuotient T p h) =
      G.terminal? p := by
  rcases p with p | r <;> rfl

/-- The pathwise quotient image of a family whose members already satisfy
the quotient edge predicate.  The source warp quotient is obtained after
first decomposing each old member into its maximal admissible components. -/
def restrictWarpToQuotient (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    Set (G.quotient T).DPath :=
  {q | ∃ p : W, q = G.restrictPathToQuotient T p.1 (h p.1 p.2)}

/-- Pathwise quotient restriction preserves the warp property. -/
theorem IsWarp.restrictWarpToQuotient {T : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).IsWarp (G.restrictWarpToQuotient T W h) := by
  rintro q ⟨p, rfl⟩ r ⟨s, rfl⟩ hne
  have hps : p.1 ≠ s.1 := by
    intro heq
    have hpsub : p = s := Subtype.ext heq
    subst s
    exact hne rfl
  change Disjoint
    (G.restrictPathToQuotient T p.1 (h p.1 p.2)).support
    (G.restrictPathToQuotient T s.1 (h s.1 s.2)).support
  rw [G.support_restrictPathToQuotient,
    G.support_restrictPathToQuotient]
  exact hW p.2 s.2 hps

@[simp]
theorem vertexSet_restrictWarpToQuotient (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).vertexSet (G.restrictWarpToQuotient T W h) =
      G.vertexSet W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hx⟩
    exact ⟨p.1, p.2, by simpa using hx⟩
  · rintro ⟨p, hp, hx⟩
    let ps : W := ⟨p, hp⟩
    exact ⟨G.restrictPathToQuotient T p (h p hp), ⟨ps, rfl⟩,
      by simpa using hx⟩

@[simp]
theorem initialSet_restrictWarpToQuotient (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).initialSet (G.restrictWarpToQuotient T W h) =
      G.initialSet W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    exact ⟨p.1, p.2, by simpa using hqx⟩
  · rintro ⟨p, hp, hpx⟩
    let ps : W := ⟨p, hp⟩
    exact ⟨G.restrictPathToQuotient T p (h p hp), ⟨ps, rfl⟩,
      by simpa using hpx⟩

@[simp]
theorem terminalFrontier_restrictWarpToQuotient
    (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).terminalFrontier (G.restrictWarpToQuotient T W h) =
      G.terminalFrontier W := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, rfl⟩, hqx⟩
    exact ⟨p.1, p.2, by simpa using hqx⟩
  · rintro ⟨p, hp, hpx⟩
    let ps : W := ⟨p, hp⟩
    exact ⟨G.restrictPathToQuotient T p (h p hp), ⟨ps, rfl⟩,
      by simpa using hpx⟩

/-! ### Quotienting an already admissible warp -/

/-- Trivial paths based at an arbitrary set have exactly that vertex set. -/
@[simp]
theorem vertexSet_trivialPaths (S : Set V) :
    G.vertexSet (G.trivialPath '' S) = S := by
  ext x
  constructor
  · rintro ⟨p, ⟨y, hy, rfl⟩, hxp⟩
    have hxy : x = y := by simpa using hxp
    exact hxy.symm ▸ hy
  · intro hx
    exact ⟨G.trivialPath x, ⟨x, hx, rfl⟩, by simp⟩

/-- Trivial paths based at an arbitrary set have exactly that initial set. -/
@[simp]
theorem initialSet_trivialPaths (S : Set V) :
    G.initialSet (G.trivialPath '' S) = S := by
  ext x
  constructor
  · rintro ⟨p, ⟨y, hy, rfl⟩, hpx⟩
    have hyx : y = x := by simpa using hpx
    exact hyx ▸ hy
  · intro hx
    exact ⟨G.trivialPath x, ⟨x, hx, rfl⟩, by simp⟩

/-- Trivial paths based at an arbitrary set have exactly that terminal
frontier. -/
@[simp]
theorem terminalFrontier_trivialPaths (S : Set V) :
    G.terminalFrontier (G.trivialPath '' S) = S := by
  ext x
  constructor
  · rintro ⟨p, ⟨y, hy, rfl⟩, hpx⟩
    have hyx : y = x := Option.some.inj
      ((G.terminal?_trivialPath y).symm.trans hpx)
    exact hyx ▸ hy
  · intro hx
    exact ⟨G.trivialPath x, ⟨x, hx, rfl⟩, G.terminal?_trivialPath x⟩

@[simp]
theorem vertexSet_union (U W : Set G.DPath) :
    G.vertexSet (U ∪ W) = G.vertexSet U ∪ G.vertexSet W := by
  ext x
  simp only [mem_vertexSet, Set.mem_union]
  aesop

@[simp]
theorem initialSet_union (U W : Set G.DPath) :
    G.initialSet (U ∪ W) = G.initialSet U ∪ G.initialSet W := by
  ext x
  simp only [mem_initialSet, Set.mem_union]
  aesop

@[simp]
theorem terminalFrontier_union (U W : Set G.DPath) :
    G.terminalFrontier (U ∪ W) =
      G.terminalFrontier U ∪ G.terminalFrontier W := by
  ext x
  simp only [mem_terminalFrontier, Set.mem_union]
  aesop

/-- If the old paths already satisfy the quotient edge predicate, the source
quotient is their pathwise restriction together with isolated essential
commitment vertices not already used by the warp.  This is precisely
Definition 2.29 on an admissible component family. -/
def admissibleWarpQuotient (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    Set (G.quotient T).DPath :=
  G.restrictWarpToQuotient T W h ∪
    (G.quotient T).trivialPath '' (G.essential T \ G.vertexSet W)

/-- A family of trivial paths is a warp. -/
theorem isWarp_trivialPaths (S : Set V) :
    G.IsWarp (G.trivialPath '' S) := by
  exact (G.wavePathSystem).isWarp_trivialWarp S

/-- A pathwise-admissible warp remains a warp after adding the isolated
essential commitment points required by Definition 2.29. -/
theorem IsWarp.admissibleWarpQuotient {T : Set V} {W : Set G.DPath}
    (hW : G.IsWarp W)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).IsWarp (G.admissibleWarpQuotient T W h) := by
  apply Set.PairwiseDisjoint.union
    (IsWarp.restrictWarpToQuotient G hW h)
    ((G.quotient T).isWarp_trivialPaths (G.essential T \ G.vertexSet W))
  rintro q ⟨p, rfl⟩ r ⟨x, hx, rfl⟩ _hne
  rw [(G.quotient T).support_trivialPath]
  apply Set.disjoint_singleton_right.2
  intro hxq
  apply hx.2
  exact ⟨p.1, p.2, by simpa using hxq⟩

@[simp]
theorem vertexSet_admissibleWarpQuotient (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).vertexSet (G.admissibleWarpQuotient T W h) =
      G.vertexSet W ∪ G.essential T := by
  rw [admissibleWarpQuotient, (G.quotient T).vertexSet_union,
    G.vertexSet_restrictWarpToQuotient,
    (G.quotient T).vertexSet_trivialPaths]
  exact Set.union_sdiff_self

@[simp]
theorem initialSet_admissibleWarpQuotient (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).initialSet (G.admissibleWarpQuotient T W h) =
      G.initialSet W ∪ (G.essential T \ G.vertexSet W) := by
  rw [admissibleWarpQuotient, (G.quotient T).initialSet_union,
    G.initialSet_restrictWarpToQuotient,
    (G.quotient T).initialSet_trivialPaths]

@[simp]
theorem terminalFrontier_admissibleWarpQuotient
    (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).terminalFrontier (G.admissibleWarpQuotient T W h) =
      G.terminalFrontier W ∪ (G.essential T \ G.vertexSet W) := by
  rw [admissibleWarpQuotient, (G.quotient T).terminalFrontier_union,
    G.terminalFrontier_restrictWarpToQuotient,
    (G.quotient T).terminalFrontier_trivialPaths]

/-- A set consists of its strict roof boundary complement exactly at its
essential points. -/
theorem sdiff_strictRoof_self (T : Set V) :
    T \ G.strictRoof T = G.essential T := by
  ext x
  constructor
  · rintro ⟨hxT, hxNotStrict⟩
    by_contra hxNotEss
    exact hxNotStrict ⟨G.subset_roof T hxT, hxNotEss⟩
  · intro hxEss
    exact ⟨hxEss.1, fun hxStrict ↦ hxStrict.2 hxEss⟩

/-- Every vertex of a pathwise-admissible family survives strict-roof
deletion. -/
theorem vertexSet_disjoint_strictRoof_of_pathQuotientAdmissible
    {T : Set V} {W : Set G.DPath}
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    Disjoint (G.vertexSet W) (G.strictRoof T) := by
  apply Set.disjoint_left.2
  rintro x ⟨p, hpW, hxp⟩ hxStrict
  rcases p with p | r
  · exact (h (.inl p) hpW).1 hxp hxStrict
  · obtain ⟨n, rfl⟩ := hxp
    exact (h (.inr r) hpW).1 n hxStrict

/-- A commitment point used by an already admissible path can only be its
initial vertex, because every traversed quotient edge has head outside the
commitment set. -/
theorem essential_inter_vertexSet_subset_initialSet_of_admissible
    {T : Set V} {W : Set G.DPath}
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    G.essential T ∩ G.vertexSet W ⊆ G.initialSet W := by
  rintro x ⟨hxEss, p, hpW, hxp⟩
  refine ⟨p, hpW, ?_⟩
  rcases p with p | r
  · have hxwalk : x ∈ p.walk.support := hxp
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      G.graph.Adj p.walk).1 hxwalk with hstart | htail
    · exact hstart.symm
    · exact ((h (.inl p) hpW).2 htail hxEss.1).elim
  · obtain ⟨n, hn⟩ := hxp
    cases n with
    | zero =>
        change r.initial = x
        simpa [Ray.initial] using hn
    | succ n =>
        exact ((h (.inr r) hpW).2 n (hn ▸ hxEss.1)).elim

/-- Exact vertex-set clause of source Definition 2.29 for an already
admissible component family. -/
theorem vertexSet_admissibleWarpQuotient_source_formula
    (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).vertexSet (G.admissibleWarpQuotient T W h) =
      (G.vertexSet W ∪ T) \ G.strictRoof T := by
  rw [G.vertexSet_admissibleWarpQuotient]
  apply Set.Subset.antisymm
  · rintro x (hxW | hxEss)
    · exact ⟨Or.inl hxW,
        Set.disjoint_left.1
          (G.vertexSet_disjoint_strictRoof_of_pathQuotientAdmissible h) hxW⟩
    · exact ⟨Or.inr hxEss.1, fun hxStrict ↦ hxStrict.2 hxEss⟩
  · rintro x ⟨hxW | hxT, hxNotStrict⟩
    · exact Or.inl hxW
    · exact Or.inr ((G.sdiff_strictRoof_self T).symm ▸ ⟨hxT, hxNotStrict⟩)

/-- Exact initial-set clause of source Lemma 2.34 for an already admissible
component family. -/
theorem initialSet_admissibleWarpQuotient_source_formula
    (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.quotient T).initialSet (G.admissibleWarpQuotient T W h) =
      (G.initialSet W ∪ T) \ G.strictRoof T := by
  rw [G.initialSet_admissibleWarpQuotient]
  apply Set.Subset.antisymm
  · rintro x (hxIni | hxExtra)
    · obtain ⟨p, hpW, rfl⟩ := hxIni
      exact ⟨Or.inl ⟨p, hpW, rfl⟩,
        Set.disjoint_left.1
          (G.vertexSet_disjoint_strictRoof_of_pathQuotientAdmissible h)
          ⟨p, hpW, p.initial_mem_support⟩⟩
    · exact ⟨Or.inr hxExtra.1.1, fun hxStrict ↦ hxStrict.2 hxExtra.1⟩
  · rintro x ⟨hxIni | hxT, hxNotStrict⟩
    · exact Or.inl hxIni
    · have hxEss : x ∈ G.essential T :=
        (G.sdiff_strictRoof_self T).symm ▸ ⟨hxT, hxNotStrict⟩
      by_cases hxVW : x ∈ G.vertexSet W
      · exact Or.inl
          (G.essential_inter_vertexSet_subset_initialSet_of_admissible h
            ⟨hxEss, hxVW⟩)
      · exact Or.inr ⟨hxEss, hxVW⟩

/-- Source Lemma 2.31 for an already admissible component family: every
unused essential commitment vertex occurs as a trivial quotient path. -/
theorem trivialPath_mem_admissibleWarpQuotient
    (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p)
    {x : V} (hx : x ∈ G.essential T \ G.vertexSet W) :
    (G.quotient T).trivialPath x ∈ G.admissibleWarpQuotient T W h :=
  Or.inr ⟨x, hx, rfl⟩

/-- Terminal containment from source Lemma 2.34, in the admissible-component
case. -/
theorem terminalFrontier_source_subset_admissibleWarpQuotient
    (T : Set V) (W : Set G.DPath)
    (h : ∀ p ∈ W, G.PathQuotientAdmissible T p) :
    (G.terminalFrontier W \ G.strictRoof T) ∪
        (G.essential T \ G.vertexSet W) ⊆
      (G.quotient T).terminalFrontier
        (G.admissibleWarpQuotient T W h) := by
  rw [G.terminalFrontier_admissibleWarpQuotient]
  rintro x (hx | hx)
  · exact Or.inl hx.1
  · exact Or.inr hx

/-! ## The source calculation for quotient waves -/

/-- The standard web normalization used in the source: no directed edge
enters the source set.  Deleting such edges does not change paths which start
in the source, and makes the quotient-source formula literal. -/
def NoEdgeEnters (A : Set V) : Prop :=
  ∀ {u v}, G.graph.Adj u v → v ∈ A → False

/-- A walk starting outside a set which no edge enters avoids that set. -/
theorem walk_avoids_of_noEdgeEnters {A : Set V} (hA : G.NoEdgeEnters A) :
    ∀ {u v : V} (p : Walk G.graph u v), u ∉ A →
      ∀ {x : V}, x ∈ p.support → x ∉ A
  | u, _, .nil, hu, x, hx => by
      simp only [Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact hu
  | u, _, .cons e p, hu, x, hx => by
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hu
      · exact walk_avoids_of_noEdgeEnters hA p
          (fun hyA ↦ hA e hyA) hx

/-- Every noninitial vertex of a walk avoids a set which no edge enters. -/
theorem walk_tail_avoids_of_noEdgeEnters {A : Set V}
    (hA : G.NoEdgeEnters A) {u v : V} (p : Walk G.graph u v) :
    ∀ {x}, x ∈ p.support.tail → x ∉ A := by
  cases p with
  | nil => simp
  | @cons u y v e q =>
      intro x hx
      exact walk_avoids_of_noEdgeEnters G hA q
        (fun hyA ↦ hA e hyA) hx

/-- On a path beginning in a set which no edge enters, the only possible
vertex of that set is the initial vertex. -/
theorem targetPath_meets_noEdgeEnters_only_at_start
    {A : Set V} (hA : G.NoEdgeEnters A)
    (p : FinitePath G.graph) (hpA : p.start ∈ A) :
    ∀ {x}, x ∈ p.support → x ∈ A → x = p.start := by
  intro x hxp hxA
  have hxwalk : x ∈ p.walk.support := hxp
  rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
    G.graph.Adj p.walk).1 hxwalk with hx | hxtail
  · exact hx
  · exact (G.walk_tail_avoids_of_noEdgeEnters hA p.walk hxtail hxA).elim

/-- Source Observation 2.24.  Under the standard no-incoming-source
normalization and `A ∩ X = ∅`, the abstract essential source chosen by
`DWeb.quotient` is exactly `(A ∪ X) \ strictRoof X`. -/
theorem essential_union_eq_union_sdiff_strictRoof_of_noEdgeEnters
    {A X : Set V} (hA : G.NoEdgeEnters A) (hAX : Disjoint A X) :
    G.essential (A ∪ X) = (A ∪ X) \ G.strictRoof X := by
  apply Set.Subset.antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    intro hxStrict
    apply hx.2
    rcases hx.1 with hxA | hxX
    · apply G.roof_mono (show X ⊆ (A ∪ X) \ {x} by
        intro y hyX
        exact ⟨Or.inr hyX,
          fun hyx ↦ Set.disjoint_left.1 hAX hxA (hyx ▸ hyX)⟩)
      exact hxStrict.1
    · apply G.roof_mono (show X \ {x} ⊆ (A ∪ X) \ {x} by
        intro y hy
        exact ⟨Or.inr hy.1, hy.2⟩)
      by_contra hxNotRoof
      exact hxStrict.2 ⟨hxX, hxNotRoof⟩
  · rintro x ⟨hxAorX, hxNotStrict⟩
    refine ⟨hxAorX, ?_⟩
    rcases hxAorX with hxA | hxX
    · have hxNotX : x ∉ X :=
        fun hxX ↦ Set.disjoint_left.1 hAX hxA hxX
      have hxNotEssX : x ∉ G.essential X :=
        fun hxEss ↦ hxNotX hxEss.1
      have hxNotRoofX : x ∉ G.roof X := by
        intro hxRoof
        exact hxNotStrict ⟨hxRoof, hxNotEssX⟩
      obtain ⟨p, hp, hpAvoidX⟩ := (G.not_mem_roof_iff X x).1 hxNotRoofX
      apply (G.not_mem_roof_iff ((A ∪ X) \ {x}) x).2
      refine ⟨p, hp, ?_⟩
      apply Set.disjoint_left.2
      intro y hyp hy
      rcases hy.1 with hyA | hyX
      · have hpStartA : p.start ∈ A := hp.1 ▸ hxA
        have hyStart :=
          G.targetPath_meets_noEdgeEnters_only_at_start hA p hpStartA hyp hyA
        exact hy.2 (hyStart.trans hp.1)
      · exact Set.disjoint_left.1 hpAvoidX hyp hyX
    · have hxEssX : x ∈ G.essential X := by
        by_contra hxNotEss
        exact hxNotStrict ⟨G.subset_roof X hxX, hxNotEss⟩
      obtain ⟨p, hp, hpAvoid⟩ :=
        (G.not_mem_roof_iff (X \ {x}) x).1 hxEssX.2
      have hxNotA : x ∉ A :=
        fun hxA ↦ Set.disjoint_left.1 hAX hxA hxX
      apply (G.not_mem_roof_iff ((A ∪ X) \ {x}) x).2
      refine ⟨p, hp, ?_⟩
      apply Set.disjoint_left.2
      intro y hyp hy
      rcases hy.1 with hyA | hyX
      · have hpStartNotA : p.start ∉ A :=
          fun hpStartA ↦ hxNotA (hp.1 ▸ hpStartA)
        exact walk_avoids_of_noEdgeEnters G hA p.walk
          hpStartNotA hyp hyA
      · exact Set.disjoint_left.1 hpAvoid hyp ⟨hyX, hy.2⟩

theorem quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
    {X : Set V} (hA : G.NoEdgeEnters G.source)
    (hAX : Disjoint G.source X) :
    (G.quotient X).source =
      (G.source ∪ X) \ G.strictRoof X := by
  rw [G.quotient_source]
  exact G.essential_union_eq_union_sdiff_strictRoof_of_noEdgeEnters hA hAX

/-- The source-frontier inclusion used in source Lemma 3.27.  A point of
`essential (A ∪ X)` which comes from `A` lies under the deleted-web roof;
one which comes from `X` is already essential in `X`.  Essentiality in the
union also rules out the old strict roof. -/
theorem essential_union_subset_delete_roof_or_essential
    {A X S : Set V} (hAX : Disjoint A X)
    (hA : A ⊆ (G.delete X).roof S) :
    G.essential (A ∪ X) ⊆
      ((((G.delete X).roof S ∩ Xᶜ) \ G.strictRoof X) ∪ G.essential X) := by
  intro x hx
  rcases hx.1 with hxA | hxX
  · left
    have hxNotX : x ∉ X := fun hxX ↦ Set.disjoint_left.1 hAX hxA hxX
    refine ⟨⟨hA hxA, hxNotX⟩, ?_⟩
    intro hxStrict
    apply hx.2
    apply G.roof_mono (show X ⊆ (A ∪ X) \ {x} by
      intro y hyX
      refine ⟨Or.inr hyX, ?_⟩
      intro hyx
      subst y
      exact Set.disjoint_left.1 hAX hxA hyX)
    exact hxStrict.1
  · right
    refine ⟨hxX, ?_⟩
    intro hxRoof
    apply hx.2
    apply G.roof_mono (show X \ {x} ⊆ (A ∪ X) \ {x} by
      intro y hy
      exact ⟨Or.inr hy.1, hy.2⟩)
    exact hxRoof

/-- Rewriting the preceding source calculation with the concrete quotient
source. -/
theorem quotient_source_subset_delete_roof_or_essential
    {A X S : Set V} (hsource : G.source = A) (hAX : Disjoint A X)
    (hA : A ⊆ (G.delete X).roof S) :
    (G.quotient X).source ⊆
      ((((G.delete X).roof S ∩ Xᶜ) \ G.strictRoof X) ∪ G.essential X) := by
  rw [G.quotient_source, hsource]
  exact G.essential_union_subset_delete_roof_or_essential hAX hA

/-! ### Passing through the last commitment vertex -/

/-- Let `p` be a target path which meets `T`, and begin a suffix at the last
vertex of `T` on `p`.  That suffix is an honest path of the quotient by `T`.

This is the actual-edge version of the path restriction used throughout the
quotient arguments in Sections 2 and 3.  In particular, it does not require
that unused chords between vertices of the suffix satisfy the quotient edge
predicate.  The initial vertex survives because a last hit is essential;
every later vertex is outside `roof T`, hence outside its strict roof. -/
theorem exists_quotientPath_from_lastHit
    (T : Set V) (p : FinitePath G.graph) {v : V}
    (hp : G.IsTargetPathFrom v p) (hmeet : G.Meets p T) :
    let hwMeet : p.walk.Meets T :=
      ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
    let L := Walk.lastHit p.walk T hwMeet
    ∃ q : FinitePath (G.quotient T).graph,
      q.start = L.startpoint ∧ q.finish = p.finish ∧
        q.support = {x | x ∈ L.walk.support} := by
  let hwMeet : p.walk.Meets T :=
    ⟨hmeet.choose, hmeet.choose_spec.1, hmeet.choose_spec.2⟩
  let L := Walk.lastHit p.walk T hwMeet
  let r : FinitePath G.graph :=
    { start := L.startpoint
      finish := p.finish
      walk := L.walk
      isPath := L.isPath p.isPath }
  have hrTarget : G.IsTargetPathFrom L.startpoint r := ⟨rfl, hp.2⟩
  have hrAvoid : RelationalRoof.Avoids G.graph.Adj r (T \ {r.start}) := by
    intro x hxr hxT
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      G.graph.Adj r.walk).1 hxr with hxeq | hxtail
    · exact hxT.2 hxeq
    · exact L.no_mem_after hxtail hxT.1
  have hstartEss : L.startpoint ∈ G.essential T :=
    G.lastHit_mem_essential T p hp hmeet
  have hstrict : ∀ {x}, x ∈ r.walk.support → x ∉ G.strictRoof T := by
    intro x hxr hxStrict
    rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
      G.graph.Adj r.walk).1 hxr with hxeq | hxtail
    · exact hxStrict.2 (hxeq.symm ▸ hstartEss)
    · have hxne : x ≠ r.start := by
        intro hxeq
        have hheadNe := r.isPath.rel_head_tail hxtail
        exact hheadNe (r.walk.head_support.trans hxeq.symm)
      have hxNotRoof :=
        RelationalRoof.not_mem_roof_of_later_mem_targetPath
          G.graph.Adj G.target r hrTarget hrAvoid hxr hxne
      exact hxNotRoof hxStrict.1
  have hcommit : ∀ {x}, x ∈ r.walk.support.tail → x ∉ T := by
    intro x hx
    exact L.no_mem_after hx
  let q := G.restrictFinitePathToQuotient T r hstrict hcommit
  refine ⟨q, rfl, rfl, ?_⟩
  calc
    q.support = r.support :=
      G.support_restrictFinitePathToQuotient T r hstrict hcommit
    _ = {x | x ∈ L.walk.support} := rfl

/-- Regard a quotient walk, whose initial vertex is outside `T`, as a walk
in the deleted web.  The quotient's prohibition on arcs entering `T`
propagates the initial avoidance along the walk. -/
private def quotientWalkToDelete {T : Set V} :
    ∀ {a b : V} (_p : Walk (G.quotient T).graph a b), a ∉ T →
      Walk (G.delete T).graph a b
  | _, _, .nil, _ => .nil
  | _, _, .cons e p, ha =>
      .cons ⟨e.1, ha, e.2.2.2⟩ (quotientWalkToDelete p e.2.2.2)

@[simp] private theorem support_quotientWalkToDelete
    {T : Set V} {a b : V}
    (p : Walk (G.quotient T).graph a b) (ha : a ∉ T) :
    (G.quotientWalkToDelete p ha).support = p.support := by
  induction p with
  | nil => rfl
  | @cons u v w e p ih =>
      change u :: (G.quotientWalkToDelete p e.2.2.2).support = u :: p.support
      rw [ih]

/-- Convert a quotient finite path to a path in the deleted web when its
initial vertex is retained. -/
private def quotientFinitePathToDelete (T : Set V)
    (p : FinitePath (G.quotient T).graph) (hstart : p.start ∉ T) :
    FinitePath (G.delete T).graph where
  start := p.start
  finish := p.finish
  walk := G.quotientWalkToDelete p.walk hstart
  isPath := by
    rw [Walk.isPath_iff, G.support_quotientWalkToDelete]
    exact p.isPath

@[simp] private theorem support_quotientFinitePathToDelete
    (T : Set V) (p : FinitePath (G.quotient T).graph) (hstart : p.start ∉ T) :
    (G.quotientFinitePathToDelete T p hstart).support = p.support := by
  ext x
  change x ∈ (G.quotientWalkToDelete p.walk hstart).support ↔
    x ∈ p.walk.support
  rw [G.support_quotientWalkToDelete]

/-- A quotient finite path avoids `T` once its initial vertex does. -/
private theorem quotientFinitePath_avoids_commitment
    {T : Set V} (p : FinitePath (G.quotient T).graph)
    (hstart : p.start ∉ T) : Disjoint p.support T := by
  apply Set.disjoint_left.2
  intro x hxp hxT
  have hxwalk : x ∈ p.walk.support := hxp
  rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
    (G.quotient T).graph.Adj p.walk).1 hxwalk with
    hx | hx
  · exact hstart (hx.symm ▸ hxT)
  · exact (G.quotientWalk_tail_avoids p.walk hx).2 hxT

/-- A quotient finite path avoids the old strict roof once its initial
vertex does. -/
private theorem quotientFinitePath_avoids_strictRoof
    {T : Set V} (p : FinitePath (G.quotient T).graph)
    (hstart : p.start ∉ G.strictRoof T) :
    Disjoint p.support (G.strictRoof T) := by
  apply Set.disjoint_left.2
  intro x hxp hxT
  have hxwalk : x ∈ p.walk.support := hxp
  rcases (RelationalRoof.mem_support_iff_start_or_mem_tail
    (G.quotient T).graph.Adj p.walk).1 hxwalk with
    hx | hx
  · exact hstart (hx.symm ▸ hxT)
  · exact (G.quotientWalk_tail_avoids p.walk hx).1 hxT

/-- Lift a finite path in a quotient back to the original web. -/
private def liftQuotientFinitePath (T : Set V)
    (p : FinitePath (G.quotient T).graph) : FinitePath G.graph :=
  p.lift (D := (G.quotient T).graph) (E := G.graph)
    (fun {_ _} h ↦ h.1)

@[simp] private theorem support_liftQuotientFinitePath (T : Set V)
    (p : FinitePath (G.quotient T).graph) :
    (G.liftQuotientFinitePath T p).support = p.support := by
  unfold liftQuotientFinitePath
  exact FinitePath.support_lift (D := (G.quotient T).graph) (E := G.graph)
    (fun {_ _} h ↦ h.1) p

/-- Vertex-set form of the strict-roof comparison underlying
Aharoni--Berger Lemma 2.35.  Every point of the old strict roof which
survives quotienting remains in the quotient strict roof of the surviving
frontier.  The warp version additionally identifies that surviving frontier
with the terminal frontier of the quotient warp. -/
theorem strictRoof_inter_quotientVertexSet_subset_strictRoof_quotient
    (S T : Set V) :
    G.strictRoof S ∩ G.quotientVertexSet T ⊆
      (G.quotient T).strictRoof (S \ G.strictRoof T) := by
  intro v hv
  have hvStrictT : v ∉ G.strictRoof T := hv.2
  constructor
  · intro p hp
    let q := G.liftQuotientFinitePath T p
    have hq : G.IsTargetPathFrom v q := by
      exact ⟨hp.1, hp.2⟩
    obtain ⟨w, hwq, hwS⟩ := hv.1.1 q hq
    have hwp : w ∈ p.support := by simpa [q] using hwq
    have hav : Disjoint p.support (G.strictRoof T) :=
      G.quotientFinitePath_avoids_strictRoof p (by simpa [hp.1] using hvStrictT)
    exact ⟨w, hwp, hwS, Set.disjoint_left.1 hav hwp⟩
  · intro hvEss
    obtain ⟨p, hp, hav⟩ :=
      ((G.quotient T).not_mem_roof_iff
        ((S \ G.strictRoof T) \ {v}) v).1 hvEss.2
    let q := G.liftQuotientFinitePath T p
    have hq : G.IsTargetPathFrom v q := ⟨hp.1, hp.2⟩
    have hpAvoidStrict : Disjoint p.support (G.strictRoof T) :=
      G.quotientFinitePath_avoids_strictRoof p (by simpa [hp.1] using hvStrictT)
    have hqAvoid : G.Avoids q (S \ {v}) := by
      apply Set.disjoint_left.2
      intro w hwq hwS
      have hwp : w ∈ p.support := by simpa [q] using hwq
      have hwNotStrict : w ∉ G.strictRoof T :=
        Set.disjoint_left.1 hpAvoidStrict hwp
      exact Set.disjoint_left.1 hav hwp ⟨⟨hwS.1, hwNotStrict⟩, hwS.2⟩
    apply hv.1.2
    exact ⟨hvEss.1.1,
      (G.not_mem_roof_iff (S \ {v}) v).2 ⟨q, hq, hqAvoid⟩⟩

/-- Concrete form of Aharoni--Berger Lemma 2.36.  In the source the left
side is automatically a subset of `V(Γ-T)`; because `DWeb.delete` retains
the ambient Lean vertex type, that domain condition appears explicitly as
intersection with `Tᶜ`. -/
theorem delete_roof_inter_compl_sdiff_strictRoof_subset_quotient_roof
    (S T : Set V) :
    ((G.delete T).roof S ∩ Tᶜ) \ G.strictRoof T ⊆
      (G.quotient T).roof (S \ G.strictRoof T) := by
  intro v hv p hp
  have hvT : v ∉ T := hv.1.2
  have hvStrict : v ∉ G.strictRoof T := hv.2
  have hpAvoidsT : Disjoint p.support T :=
    G.quotientFinitePath_avoids_commitment p (by simpa [hp.1] using hvT)
  let q := G.quotientFinitePathToDelete T p (by simpa [hp.1] using hvT)
  have hq : (G.delete T).IsTargetPathFrom v q := by
    constructor
    · change p.start = v
      exact hp.1
    · refine ⟨hp.2, ?_⟩
      exact Set.disjoint_left.1 hpAvoidsT p.finish_mem_support
  obtain ⟨w, hwq, hwS⟩ := hv.1.1 q hq
  have hwp : w ∈ p.support := by
    simpa [q] using hwq
  have hpAvoidsStrict : Disjoint p.support (G.strictRoof T) :=
    G.quotientFinitePath_avoids_strictRoof p (by simpa [hp.1] using hvStrict)
  exact ⟨w, hwp, hwS, Set.disjoint_left.1 hpAvoidsStrict hwp⟩

/-- Source-hypothesis form of Lemma 2.36.  The disjointness assumption is
part of the paper's interface; the concrete quotient proof above is stronger
and does not need it. -/
theorem delete_roof_inter_compl_sdiff_strictRoof_subset_quotient_roof_of_disjoint
    {S T : Set V} (_hST : Disjoint S T) :
    ((G.delete T).roof S ∩ Tᶜ) \ G.strictRoof T ⊆
      (G.quotient T).roof (S \ G.strictRoof T) :=
  G.delete_roof_inter_compl_sdiff_strictRoof_subset_quotient_roof S T

/-- The proof kernel of source Lemma 3.27.  Once the concrete quotient-warp
construction supplies its elementary warp, initial, and terminal clauses,
the wave property and the advertised roof inclusion follow solely from
Lemmas 2.34--2.36. -/
theorem isWave_of_delete_roof_and_quotient_frontier
    {X S : Set V} {R : Set (G.quotient X).DPath}
    (hSourceX : Disjoint G.source X)
    (hDeleteRoof : (G.delete X).source ⊆ (G.delete X).roof S)
    (hWarp : (G.quotient X).IsWarp R)
    (hInitial : (G.quotient X).initialSet R ⊆ (G.quotient X).source)
    (hSurviving : S \ G.strictRoof X ⊆
      (G.quotient X).terminalFrontier R)
    (hCommitment : G.essential X ⊆
      (G.quotient X).terminalFrontier R) :
    (G.quotient X).IsWave R ∧
      (((G.delete X).roof S ∩ Xᶜ) \ G.strictRoof X) ⊆
        (G.quotient X).roof ((G.quotient X).terminalFrontier R) := by
  have hSourceRoof : G.source ⊆ (G.delete X).roof S := by
    intro a ha
    exact hDeleteRoof ⟨ha, fun haX ↦ Set.disjoint_left.1 hSourceX ha haX⟩
  have hQuotientRoof :
      (((G.delete X).roof S ∩ Xᶜ) \ G.strictRoof X) ⊆
        (G.quotient X).roof ((G.quotient X).terminalFrontier R) := by
    exact
      (G.delete_roof_inter_compl_sdiff_strictRoof_subset_quotient_roof S X).trans
        ((G.quotient X).roof_mono hSurviving)
  refine ⟨⟨hWarp, hInitial, ?_⟩, hQuotientRoof⟩
  intro a ha
  have haCases := G.quotient_source_subset_delete_roof_or_essential
    (A := G.source) (S := S) rfl hSourceX hSourceRoof ha
  rcases haCases with haRoof | haEss
  · exact hQuotientRoof haRoof
  · exact (G.quotient X).subset_roof _ (hCommitment haEss)

/-! ### Concrete quotient of a deleted-web wave -/

/-- If a finite path avoids `X` and its terminal lies outside `roof X`, then
every vertex of the path lies outside `roof X`. -/
theorem finitePath_support_disjoint_roof_of_finish_not_roof
    (X : Set V) (p : FinitePath G.graph)
    (hpAvoid : Disjoint p.support X) (hfinish : p.finish ∉ G.roof X) :
    Disjoint p.support (G.roof X) := by
  apply Set.disjoint_left.2
  intro x hxp hxRoof
  obtain ⟨q, hqTarget, hqAvoid⟩ := (G.not_mem_roof_iff X p.finish).1 hfinish
  let hm : p.walk.Meets ({x} : Set V) :=
    ⟨x, hxp, Set.mem_singleton x⟩
  let L := p.walk.lastHit ({x} : Set V) hm
  have hLx : L.startpoint = x := Set.mem_singleton_iff.1 L.startpoint_mem
  let pre : Walk G.graph x p.finish :=
    RelationalRoof.castStart G.graph.Adj hLx L.walk
  let qwalk : Walk G.graph p.finish q.finish :=
    RelationalRoof.castStart G.graph.Adj hqTarget.1 q.walk
  let w : Walk G.graph x q.finish := pre.append qwalk
  obtain ⟨y, hyw, hyX⟩ :=
    RelationalRoof.roof_meets_walk G.graph.Adj G.target hxRoof w hqTarget.2
  have hyCases : y ∈ pre.support ∨ y ∈ qwalk.support.tail := by
    simpa only [w, Walk.support_append, List.mem_append] using hyw
  rcases hyCases with hyPre | hyQ
  · have hyL : y ∈ L.walk.support := by
      simpa only [pre, RelationalRoof.support_castStart] using hyPre
    exact Set.disjoint_left.1 hpAvoid (L.support_subset hyL) hyX
  · exact Set.disjoint_left.1 hqAvoid
      (by
        change y ∈ q.walk.support
        simpa only [qwalk, RelationalRoof.support_castStart] using
          List.mem_of_mem_tail hyQ) hyX

/-- The finite members of a deleted-web family whose terminal survives the
strict roof, lifted back to the original graph. -/
def survivingTerminalLift (X : Set V) (U : Set (G.delete X).DPath) :
    Set G.DPath :=
  {p | ∃ q ∈ U, (∃ t, (G.delete X).terminal? q = some t ∧
      t ∉ G.strictRoof X) ∧ p = G.liftDeletePath X q}

theorem IsWarp.survivingTerminalLift {X : Set V}
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWarp U) :
    G.IsWarp (G.survivingTerminalLift X U) := by
  rintro p ⟨q, hqU, _hqterm, rfl⟩ r ⟨s, hsU, _hsterm, rfl⟩ hne
  have hqs : q ≠ s := by
    intro h
    subst s
    exact hne rfl
  change Disjoint (G.liftDeletePath X q).support
    (G.liftDeletePath X s).support
  rw [G.support_liftDeletePath, G.support_liftDeletePath]
  exact hU hqU hsU hqs

theorem initialSet_survivingTerminalLift_subset {X : Set V}
    {U : Set (G.delete X).DPath} :
    G.initialSet (G.survivingTerminalLift X U) ⊆
      (G.delete X).initialSet U := by
  rintro x ⟨p, ⟨q, hqU, _hqterm, rfl⟩, hpx⟩
  exact ⟨q, hqU, by simpa using hpx⟩

theorem terminalFrontier_survivingTerminalLift {X : Set V}
    (U : Set (G.delete X).DPath) :
    G.terminalFrontier (G.survivingTerminalLift X U) =
      (G.delete X).terminalFrontier U \ G.strictRoof X := by
  ext x
  constructor
  · rintro ⟨p, ⟨q, hqU, ⟨t, hqt, ht⟩, rfl⟩, hpx⟩
    have htx : t = x := by
      rcases q with q | r
      · exact Option.some.inj (hqt.symm.trans hpx)
      · simp at hqt
    exact ⟨⟨q, hqU, htx ▸ hqt⟩, htx ▸ ht⟩
  · rintro ⟨⟨q, hqU, hqx⟩, hx⟩
    refine ⟨G.liftDeletePath X q, ⟨q, hqU, ⟨x, hqx, hx⟩, rfl⟩, ?_⟩
    rcases q with q | r
    · exact hqx
    · simp at hqx

/-- Every surviving terminal member of a deleted-web wave is already an
honest quotient path. -/
theorem pathQuotientAdmissible_survivingTerminalLift
    {X : Set V} {U : Set (G.delete X).DPath}
    (hU : (G.delete X).IsWave U) :
    ∀ p ∈ G.survivingTerminalLift X U,
      G.PathQuotientAdmissible X p := by
  rintro p ⟨q, hqU, ⟨t, hqt, htStrict⟩, rfl⟩
  have hqInitial : q.initial ∈ (G.delete X).initialSet U := ⟨q, hqU, rfl⟩
  have hqSource := hU.2.1 hqInitial
  have hqAvoid : Disjoint (G.liftDeletePath X q).support X :=
    G.liftDeletePath_avoids X q hqSource.2
  have htSupport : t ∈ (G.liftDeletePath X q).support := by
    exact G.terminal_mem_support (by
      rcases q with q | r
      · exact hqt
      · simp at hqt)
  have htX : t ∉ X := Set.disjoint_left.1 hqAvoid htSupport
  have htRoof : t ∉ G.roof X := by
    intro ht
    apply htStrict
    exact ⟨ht, fun htEss ↦ htX htEss.1⟩
  rcases q with q | r
  · have hfinish : q.finish = t := Option.some.inj hqt
    let lifted : FinitePath G.graph :=
      q.lift (fun {_ _} h ↦ G.delete_adj_imp (X := X) h)
    have hliftEq : G.liftDeletePath X (.inl q) = (.inl lifted : G.DPath) := rfl
    have hliftAvoid : Disjoint lifted.support X := by
      apply Set.disjoint_left.2
      intro x hx hxX
      exact Set.disjoint_left.1 hqAvoid (by
        rw [hliftEq]
        exact hx) hxX
    have hfinishRoof : lifted.finish ∉ G.roof X := by
      change q.finish ∉ G.roof X
      simpa only [hfinish] using htRoof
    have hroofAvoid : Disjoint lifted.support (G.roof X) :=
      G.finitePath_support_disjoint_roof_of_finish_not_roof X lifted
        hliftAvoid hfinishRoof
    change G.PathQuotientAdmissible X (.inl lifted)
    constructor
    · intro x hx hxStrict'
      exact Set.disjoint_left.1 hroofAvoid hx hxStrict'.1
    · intro x hx hxX
      exact Set.disjoint_left.1 hqAvoid (by
        rw [hliftEq]
        exact List.mem_of_mem_tail hx) hxX
  · simp at hqt

theorem vertexSet_survivingTerminalLift_disjoint
    {X : Set V} {U : Set (G.delete X).DPath}
    (hU : (G.delete X).IsWave U) :
    Disjoint (G.vertexSet (G.survivingTerminalLift X U)) X := by
  apply Set.disjoint_left.2
  rintro x ⟨p, ⟨q, hqU, _hqterm, rfl⟩, hxp⟩ hxX
  have hqInitial : q.initial ∈ (G.delete X).initialSet U := ⟨q, hqU, rfl⟩
  have hqSource := hU.2.1 hqInitial
  exact Set.disjoint_left.1 (G.liftDeletePath_avoids X q hqSource.2)
    hxp hxX

/-- A concrete quotient of a deleted-web wave sufficient for Lemma 3.27:
retain exactly the finite members whose terminal survives the strict roof,
then add the isolated essential commitment vertices from Definition 2.29. -/
noncomputable def waveQuotient (X : Set V)
    (U : Set (G.delete X).DPath) (hU : (G.delete X).IsWave U) :
    Set (G.quotient X).DPath :=
  G.admissibleWarpQuotient X (G.survivingTerminalLift X U)
    (G.pathQuotientAdmissible_survivingTerminalLift hU)

theorem isWarp_waveQuotient {X : Set V}
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U) :
    (G.quotient X).IsWarp (G.waveQuotient X U hU) := by
  exact IsWarp.admissibleWarpQuotient G
    (IsWarp.survivingTerminalLift G hU.1)
    (G.pathQuotientAdmissible_survivingTerminalLift hU)

theorem surviving_terminal_subset_waveQuotient {X : Set V}
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U) :
    (G.delete X).terminalFrontier U \ G.strictRoof X ⊆
      (G.quotient X).terminalFrontier (G.waveQuotient X U hU) := by
  rw [waveQuotient, G.terminalFrontier_admissibleWarpQuotient,
    G.terminalFrontier_survivingTerminalLift]
  exact Set.subset_union_left

theorem essential_subset_terminal_waveQuotient {X : Set V}
    {U : Set (G.delete X).DPath} (hU : (G.delete X).IsWave U) :
    G.essential X ⊆
      (G.quotient X).terminalFrontier (G.waveQuotient X U hU) := by
  rw [waveQuotient, G.terminalFrontier_admissibleWarpQuotient]
  intro x hx
  right
  exact ⟨hx, fun hxV ↦
    Set.disjoint_left.1 (G.vertexSet_survivingTerminalLift_disjoint hU)
      hxV hx.1⟩

theorem initialSet_waveQuotient_subset_source
    {X : Set V} {U : Set (G.delete X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hU : (G.delete X).IsWave U) :
    (G.quotient X).initialSet (G.waveQuotient X U hU) ⊆
      (G.quotient X).source := by
  rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
    hNoEnter hSourceX]
  rw [waveQuotient,
    G.initialSet_admissibleWarpQuotient_source_formula]
  rintro x ⟨hx, hxStrict⟩
  refine ⟨?_, hxStrict⟩
  rcases hx with hx | hx
  · left
    have hxU := G.initialSet_survivingTerminalLift_subset hx
    exact (hU.2.1 hxU).1
  · exact Or.inr hx

/-- Aharoni--Berger Lemma 3.27, with the same-type deletion-domain
intersection made explicit. -/
theorem isWave_waveQuotient_and_roof
    {X : Set V} {U : Set (G.delete X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hU : (G.delete X).IsWave U) :
    (G.quotient X).IsWave (G.waveQuotient X U hU) ∧
      (((G.delete X).roof ((G.delete X).terminalFrontier U) ∩ Xᶜ) \
          G.strictRoof X) ⊆
        (G.quotient X).roof
          ((G.quotient X).terminalFrontier (G.waveQuotient X U hU)) := by
  exact G.isWave_of_delete_roof_and_quotient_frontier hSourceX hU.2.2
    (G.isWarp_waveQuotient hU)
    (G.initialSet_waveQuotient_subset_source hNoEnter hSourceX hU)
    (G.surviving_terminal_subset_waveQuotient hU)
    (G.essential_subset_terminal_waveQuotient hU)

/-- If the essential commitment frontier is roofed in the original web,
then quotient-roof membership at a surviving vertex implies original-roof
membership. -/
theorem quotient_roof_subset_original_roof_of_essential
    (X S : Set V) (hEss : G.essential X ⊆ G.roof S) :
    (G.quotient X).roof S \ G.strictRoof X ⊆ G.roof S := by
  intro v hv p hp
  have hRoofX : G.roof X ⊆ G.roof S := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  by_cases hmeet : G.Meets p (G.roof X)
  · obtain ⟨x, hxp, hxRoof⟩ := hmeet
    let hm : p.walk.Meets ({x} : Set V) :=
      ⟨x, hxp, Set.mem_singleton x⟩
    let L := p.walk.lastHit ({x} : Set V) hm
    have hLx : L.startpoint = x := Set.mem_singleton_iff.1 L.startpoint_mem
    let w : Walk G.graph x p.finish :=
      RelationalRoof.castStart G.graph.Adj hLx L.walk
    obtain ⟨y, hyw, hyS⟩ :=
      RelationalRoof.roof_meets_walk G.graph.Adj G.target
        (hRoofX hxRoof) w hp.2
    exact ⟨y, L.support_subset (by
      simpa only [w, RelationalRoof.support_castStart] using hyw), hyS⟩
  · have hstrict : ∀ {x}, x ∈ p.walk.support →
        x ∉ G.strictRoof X := by
      intro x hxp hxStrict
      exact hmeet ⟨x, hxp, hxStrict.1⟩
    have hcommit : ∀ {x}, x ∈ p.walk.support.tail → x ∉ X := by
      intro x hxp hxX
      exact hmeet ⟨x, List.mem_of_mem_tail hxp, G.subset_roof X hxX⟩
    let q := G.restrictFinitePathToQuotient X p hstrict hcommit
    have hq : (G.quotient X).IsTargetPathFrom v q := ⟨hp.1, hp.2⟩
    obtain ⟨x, hxq, hxS⟩ := hv.1 q hq
    exact ⟨x, by simpa only [q, G.support_restrictFinitePathToQuotient]
      using hxq, hxS⟩

/-- A quotient wave roofs the old essential commitment frontier in the
original web. -/
theorem essential_subset_original_roof_of_quotient_wave
    {X : Set V} {W : Set (G.quotient X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hW : (G.quotient X).IsWave W) :
    G.essential X ⊆ G.roof ((G.quotient X).terminalFrontier W) := by
  intro x hx p hp
  have hmeetX : G.Meets p X := ⟨p.start, p.start_mem_support, hp.1 ▸ hx.1⟩
  let hm : p.walk.Meets X :=
    ⟨hmeetX.choose, hmeetX.choose_spec.1, hmeetX.choose_spec.2⟩
  let L := p.walk.lastHit X hm
  have hLEss : L.startpoint ∈ G.essential X :=
    G.lastHit_mem_essential X p hp hmeetX
  have hLSource : L.startpoint ∈ (G.quotient X).source := by
    rw [G.quotient_source_eq_union_sdiff_strictRoof_of_noEdgeEnters
      hNoEnter hSourceX]
    exact ⟨Or.inr hLEss.1, fun hStrict ↦ hStrict.2 hLEss⟩
  obtain ⟨q, hqStart, hqFinish, hqSupport⟩ :=
    G.exists_quotientPath_from_lastHit X p hp hmeetX
  have hqTarget : (G.quotient X).IsTargetPathFrom L.startpoint q := by
    exact ⟨hqStart, hqFinish ▸ hp.2⟩
  obtain ⟨y, hyq, hyW⟩ := hW.2.2 hLSource q hqTarget
  have hyL : y ∈ L.walk.support := by
    rw [hqSupport] at hyq
    exact hyq
  exact ⟨y, L.support_subset hyL, hyW⟩

/-- Roof part of Aharoni--Berger Lemma 3.28.  The maximality premise is
stated as the roof-greatest property delivered by Lemma 3.22. -/
theorem delete_roof_subset_original_roof_of_roofGreatest_quotient
    {X : Set V} {U : Set (G.delete X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hU : (G.delete X).IsWave U)
    {W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W)
    (hGreatest : ∀ R : Set (G.quotient X).DPath,
      (G.quotient X).IsWave R → (G.quotient X).RoofLE R W) :
    (G.delete X).roof ((G.delete X).terminalFrontier U) ⊆
      G.roof ((G.quotient X).terminalFrontier W) := by
  let Q := G.waveQuotient X U hU
  have hQData := G.isWave_waveQuotient_and_roof hNoEnter hSourceX hU
  have hQLE : (G.quotient X).roof
      ((G.quotient X).terminalFrontier Q) ⊆
      (G.quotient X).roof ((G.quotient X).terminalFrontier W) :=
    hGreatest Q hQData.1
  have hEss : G.essential X ⊆
      G.roof ((G.quotient X).terminalFrontier W) :=
    G.essential_subset_original_roof_of_quotient_wave
      hNoEnter hSourceX hW
  have hRoofX : G.roof X ⊆
      G.roof ((G.quotient X).terminalFrontier W) := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  have hConvert := G.quotient_roof_subset_original_roof_of_essential
    X ((G.quotient X).terminalFrontier W) hEss
  intro v hv
  by_cases hvX : v ∈ X
  · exact hRoofX (G.subset_roof X hvX)
  by_cases hvStrict : v ∈ G.strictRoof X
  · exact hRoofX hvStrict.1
  · apply hConvert
    refine ⟨hQLE (hQData.2 ?_), hvStrict⟩
    exact ⟨⟨hv, hvX⟩, hvStrict⟩

/-- Cross-web strict-roof monotonicity.  Besides roof inclusion, commitment
vertices must already be roofed in the larger web so that an essential
witness path there restricts to the deletion. -/
theorem delete_strictRoof_subset_original_strictRoof_of_roof_subset
    (X S T : Set V)
    (hRoof : (G.delete X).roof S ⊆ G.roof T)
    (hX : X ⊆ G.roof T) :
    (G.delete X).strictRoof S ∩ Xᶜ ⊆ G.strictRoof T := by
  intro x hx
  refine ⟨hRoof hx.1.1, ?_⟩
  intro hxEss
  obtain ⟨p, hpTarget, hpAvoid⟩ :=
    (G.not_mem_roof_iff (T \ {x}) x).1 hxEss.2
  have hpAvoid' : G.Avoids p (T \ {p.start}) := by
    simpa only [hpTarget.1] using hpAvoid
  have hpAvoidRel : RelationalRoof.Avoids G.graph.Adj p
      (T \ {p.start}) := by
    intro z hzp hz
    exact Set.disjoint_left.1 hpAvoid' hzp hz
  have hpAvoidX : Disjoint p.support X := by
    apply Set.disjoint_left.2
    intro z hzp hzX
    have hzNe : z ≠ p.start := by
      intro hz
      exact hx.2 (hpTarget.1 ▸ hz ▸ hzX)
    exact (RelationalRoof.not_mem_roof_of_later_mem_targetPath
      G.graph.Adj G.target p hpTarget hpAvoidRel hzp hzNe) (hX hzX)
  let hrestrict : ∀ {u v : V}, G.graph.Adj u v →
      u ∈ p.support → v ∈ p.support → (G.delete X).graph.Adj u v :=
    fun {_ _} e hu hv ↦
      ⟨e, Set.disjoint_left.1 hpAvoidX hu,
        Set.disjoint_left.1 hpAvoidX hv⟩
  let pd : FinitePath (G.delete X).graph :=
    p.restrictGraphOnSupport hrestrict
  have hpdTarget : (G.delete X).IsTargetPathFrom x pd := by
    refine ⟨hpTarget.1, hpTarget.2, ?_⟩
    exact Set.disjoint_left.1 hpAvoidX p.finish_mem_support
  have hxRoofMinus : x ∈ (G.delete X).roof (S \ {x}) := by
    by_cases hxS : x ∈ S
    · by_contra hnot
      exact hx.1.2 ⟨hxS, hnot⟩
    · apply (G.delete X).roof_mono (show S ⊆ S \ {x} by
        intro y hy
        exact ⟨hy, fun hyx ↦ hxS (hyx ▸ hy)⟩)
      exact hx.1.1
  obtain ⟨y, hypd, hyS, hyx⟩ := hxRoofMinus pd hpdTarget
  have hyp : y ∈ p.support := by
    change y ∈ (p.restrictGraphOnSupport hrestrict).support at hypd
    rw [FinitePath.support_restrictGraphOnSupport] at hypd
    exact hypd
  have hyRoofT : y ∈ G.roof T :=
    hRoof ((G.delete X).subset_roof S hyS)
  have hyNe : y ≠ p.start := by
    intro hy
    exact hyx (hy.trans hpTarget.1)
  exact (RelationalRoof.not_mem_roof_of_later_mem_targetPath
    G.graph.Adj G.target p hpTarget hpAvoidRel hyp hyNe) hyRoofT

/-- Strict-roof part of Aharoni--Berger Corollary 3.28. -/
theorem delete_strictRoof_subset_original_strictRoof_of_roofGreatest_quotient
    {X : Set V} {U : Set (G.delete X).DPath}
    (hNoEnter : G.NoEdgeEnters G.source)
    (hSourceX : Disjoint G.source X)
    (hU : (G.delete X).IsWave U)
    {W : Set (G.quotient X).DPath}
    (hW : (G.quotient X).IsWave W)
    (hGreatest : ∀ R : Set (G.quotient X).DPath,
      (G.quotient X).IsWave R → (G.quotient X).RoofLE R W) :
    (G.delete X).strictRoof ((G.delete X).terminalFrontier U) ∩ Xᶜ ⊆
      G.strictRoof ((G.quotient X).terminalFrontier W) := by
  have hRoof :=
    G.delete_roof_subset_original_roof_of_roofGreatest_quotient
      hNoEnter hSourceX hU hW hGreatest
  have hEss := G.essential_subset_original_roof_of_quotient_wave
    hNoEnter hSourceX hW
  have hRoofX : G.roof X ⊆
      G.roof ((G.quotient X).terminalFrontier W) := by
    rw [← G.roof_essential X]
    exact G.roof_cut hEss
  exact G.delete_strictRoof_subset_original_strictRoof_of_roof_subset
    X ((G.delete X).terminalFrontier U)
      ((G.quotient X).terminalFrontier W) hRoof
      ((G.subset_roof X).trans hRoofX)

/-- The strict roof is disjoint from the represented vertex set of its own
quotient. -/
theorem disjoint_strictRoof_quotientVertexSet (S : Set V) :
    Disjoint (G.strictRoof S) (G.quotientVertexSet S) :=
  Set.disjoint_left.2 (fun _ hx hxc ↦ hxc hx)

end DWeb

end Erdos599
