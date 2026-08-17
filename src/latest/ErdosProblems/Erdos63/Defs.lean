/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# Erdős Problem 63: elementary finite-graph definitions

This file supplies the common language used by the finite Liu--Montgomery
part of the formalization.  Cycle and path lengths are expressed by walks,
whereas average degree is expressed without division.  For deletion and
expansion arguments, an avoiding path is allowed to meet a forbidden set only
inside an explicitly supplied permitted set.  The specialized predicate
`ReachWithin` permits its root (and only its root); thus it still behaves
correctly when the root itself belongs to the deleted set.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u v

variable {V : Type u} {W : Type v}
variable {G G' : SimpleGraph V} {H : SimpleGraph W}

/-! ## Exact path and cycle lengths -/

/-- There is a simple path from `x` to `y` having exactly `n` edges. -/
def HasPathBetweenLength (G : SimpleGraph V) (x y : V) (n : ℕ) : Prop :=
  ∃ p : G.Walk x y, p.IsPath ∧ p.length = n

/-- The graph contains a simple path having exactly `n` edges. -/
def HasPathLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ x y : V, HasPathBetweenLength G x y n

/-- The graph contains a simple cycle having exactly `n` edges. -/
def HasCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ x : V, ∃ p : G.Walk x x, p.IsCycle ∧ p.length = n

@[simp] theorem hasPathBetweenLength_zero_iff (G : SimpleGraph V) (x y : V) :
    HasPathBetweenLength G x y 0 ↔ x = y := by
  constructor
  · rintro ⟨p, -, hp⟩
    exact p.eq_of_length_eq_zero hp
  · rintro rfl
    exact ⟨Walk.nil, Walk.IsPath.nil, rfl⟩

theorem HasPathBetweenLength.mono (hGG' : G ≤ G') {x y : V} {n : ℕ}
    (h : HasPathBetweenLength G x y n) : HasPathBetweenLength G' x y n := by
  obtain ⟨p, hp, hlen⟩ := h
  exact ⟨p.mapLe hGG', hp.mapLe hGG', by simpa using hlen⟩

theorem HasPathLength.mono (hGG' : G ≤ G') {n : ℕ} (h : HasPathLength G n) :
    HasPathLength G' n := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, hxy.mono hGG'⟩

theorem HasCycleLength.mono (hGG' : G ≤ G') {n : ℕ} (h : HasCycleLength G n) :
    HasCycleLength G' n := by
  obtain ⟨x, p, hp, hlen⟩ := h
  exact ⟨x, p.mapLe hGG', hp.mapLe hGG', by simpa using hlen⟩

theorem HasPathBetweenLength.map (f : G →g H) (hf : Function.Injective f)
    {x y : V} {n : ℕ} (h : HasPathBetweenLength G x y n) :
    HasPathBetweenLength H (f x) (f y) n := by
  obtain ⟨p, hp, hlen⟩ := h
  exact ⟨p.map f, hp.map hf, by simpa using hlen⟩

theorem HasPathLength.map (f : G →g H) (hf : Function.Injective f) {n : ℕ}
    (h : HasPathLength G n) : HasPathLength H n := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨f x, f y, hxy.map f hf⟩

theorem HasCycleLength.map (f : G →g H) (hf : Function.Injective f) {n : ℕ}
    (h : HasCycleLength G n) : HasCycleLength H n := by
  obtain ⟨x, p, hp, hlen⟩ := h
  exact ⟨f x, p.map f, hp.map hf, by simpa using hlen⟩

/-- For genuine cycle lengths, the walk definition is exactly containment of
the corresponding cycle graph. -/
theorem hasCycleLength_iff_cycleGraph_isContained {n : ℕ} (hn : 2 < n) :
    HasCycleLength G n ↔ cycleGraph n ⊑ G := by
  exact (SimpleGraph.cycleGraph_isContained_iff hn).symm

theorem HasCycleLength.three_le {n : ℕ} (h : HasCycleLength G n) : 3 ≤ n := by
  obtain ⟨_, _, hp, rfl⟩ := h
  exact hp.three_le_length

/-! ## Division-free average degree -/

/-- `G` has average degree at least `d`, stated without division. -/
def AvgDegreeAtLeast [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) : Prop :=
  d * Fintype.card V ≤ ∑ x : V, G.degree x

@[simp] theorem avgDegreeAtLeast_zero [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : AvgDegreeAtLeast G 0 := by
  simp [AvgDegreeAtLeast]

theorem AvgDegreeAtLeast.mono [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d e : ℕ} (h : AvgDegreeAtLeast G d) (hed : e ≤ d) :
    AvgDegreeAtLeast G e := by
  exact (Nat.mul_le_mul_right (Fintype.card V) hed).trans h

theorem avgDegreeAtLeast_of_forall_degree [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (hdegree : ∀ x : V, d ≤ G.degree x) :
    AvgDegreeAtLeast G d := by
  simpa [AvgDegreeAtLeast, Nat.mul_comm] using
    (Finset.sum_le_sum fun x (_hx : x ∈ (Finset.univ : Finset V)) ↦ hdegree x)

/-! ## External neighborhoods -/

/-- The vertices outside `S` adjacent to at least one vertex of `S`. -/
noncomputable def externalNeighborhood [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : Finset V := by
  classical
  exact S.biUnion (fun v ↦ G.neighborFinset v) \ S

@[simp] theorem mem_externalNeighborhood [Fintype V] (G : SimpleGraph V)
    (S : Finset V) (x : V) :
    x ∈ externalNeighborhood G S ↔ x ∉ S ∧ ∃ y ∈ S, G.Adj y x := by
  classical
  simp only [externalNeighborhood, Finset.mem_sdiff, Finset.mem_biUnion,
    SimpleGraph.mem_neighborFinset]
  tauto

@[simp] theorem externalNeighborhood_empty [Fintype V] (G : SimpleGraph V) :
    externalNeighborhood G ∅ = ∅ := by
  classical
  ext x
  simp

@[simp] theorem externalNeighborhood_singleton [Fintype V] (G : SimpleGraph V) (x : V) :
    externalNeighborhood G {x} = G.neighborFinset x := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := ((mem_externalNeighborhood G {x} y).1 hy).2
    have hzx : z = x := by simpa using hz
    simpa [hzx] using hzy
  · intro hxy
    have hxy' : G.Adj x y := (G.mem_neighborFinset x y).mp hxy
    exact (mem_externalNeighborhood G {x} y).2
      ⟨by simpa using (G.ne_of_adj hxy').symm, ⟨x, by simp, hxy'⟩⟩

theorem externalNeighborhood_disjoint [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : Disjoint (externalNeighborhood G S) S := by
  classical
  exact Finset.disjoint_left.2 fun _ hx ↦ (mem_externalNeighborhood G S _).1 hx |>.1

theorem externalNeighborhood_mono_graph [Fintype V] {G G' : SimpleGraph V}
    (hGG' : G ≤ G') (S : Finset V) :
    externalNeighborhood G S ⊆ externalNeighborhood G' S := by
  classical
  intro x hx
  rw [mem_externalNeighborhood] at hx ⊢
  exact ⟨hx.1, hx.2.imp fun y hy ↦ ⟨hy.1, hGG' hy.2⟩⟩

/-- Enlarging the explored set can only absorb an old external neighbor or
leave it as an external neighbor of the enlarged set. -/
theorem externalNeighborhood_subset_union_of_subset [Fintype V]
    (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    externalNeighborhood G S ⊆ T ∪ externalNeighborhood G T := by
  classical
  intro x hx
  by_cases hxT : x ∈ T
  · exact Finset.mem_union_left _ hxT
  · rw [mem_externalNeighborhood] at hx
    exact Finset.mem_union_right _ <| (mem_externalNeighborhood G T x).2
      ⟨hxT, hx.2.imp fun y hy ↦ ⟨hST hy.1, hy.2⟩⟩

theorem externalNeighborhood_sdiff_subset_of_subset [Fintype V]
    (G : SimpleGraph V) {S T : Finset V} (hST : S ⊆ T) :
    externalNeighborhood G S \ T ⊆ externalNeighborhood G T := by
  classical
  intro x hx
  obtain ⟨hxN, hxT⟩ := Finset.mem_sdiff.mp hx
  have hxu := externalNeighborhood_subset_union_of_subset G hST hxN
  exact (Finset.mem_union.1 hxu).resolve_left hxT

/-! ## Avoiding paths and finite-radius balls -/

end Erdos63

namespace SimpleGraph.Walk

universe u

variable {V : Type u}
variable {G G' : SimpleGraph V}

/-- `p` only visits the forbidden set `X` at vertices belonging to `P`.

The permitted set is explicit.  In particular, callers can permit one or both
endpoints without accidentally exempting every possible endpoint from the
avoidance condition. -/
def Avoids (p : G.Walk x y) (X P : Set V) : Prop :=
  ∀ z : V, z ∈ p.support → z ∈ X → z ∈ P

@[simp] theorem avoids_empty (p : G.Walk x y) (P : Set V) : p.Avoids ∅ P := by
  simp [Avoids]

@[simp] theorem avoids_univ_right (p : G.Walk x y) (X : Set V) : p.Avoids X Set.univ := by
  simp [Avoids]

theorem Avoids.mono_forbidden {p : G.Walk x y} {X X' P : Set V}
    (h : p.Avoids X P) (hX : X' ⊆ X) : p.Avoids X' P := by
  intro z hz hzX
  exact h z hz (hX hzX)

theorem Avoids.mono_permitted {p : G.Walk x y} {X P P' : Set V}
    (h : p.Avoids X P) (hP : P ⊆ P') : p.Avoids X P' := by
  intro z hz hzX
  exact hP (h z hz hzX)

theorem Avoids.of_support_subset {x' y' : V} {p : G.Walk x y} {q : G.Walk x' y'}
    {X P : Set V}
    (hp : p.Avoids X P) (hsupport : q.support ⊆ p.support) : q.Avoids X P := by
  intro z hz hzX
  exact hp z (hsupport hz) hzX

@[simp] theorem avoids_nil_iff (x : V) (X P : Set V) :
    (Walk.nil : G.Walk x x).Avoids X P ↔ (x ∈ X → x ∈ P) := by
  simp [Avoids]

theorem Avoids.mapLe {G G' : SimpleGraph V} (hGG' : G ≤ G')
    {x y : V} {p : G.Walk x y} {X P : Set V} (h : p.Avoids X P) :
    (p.mapLe hGG').Avoids X P := by
  rw [Avoids, p.support_mapLe_eq_support]
  exact h

theorem Avoids.reverse {x y : V} {p : G.Walk x y} {X P : Set V}
    (h : p.Avoids X P) : p.reverse.Avoids X P := by
  intro z hz hzX
  apply h z _ hzX
  simpa [p.support_reverse] using hz

/-- A simple path satisfying an explicit forbidden/permitted policy. -/
def IsAvoidingPath (p : G.Walk x y) (X P : Set V) : Prop :=
  p.IsPath ∧ p.Avoids X P

theorem IsAvoidingPath.mono_forbidden {p : G.Walk x y} {X X' P : Set V}
    (h : p.IsAvoidingPath X P) (hX : X' ⊆ X) : p.IsAvoidingPath X' P :=
  ⟨h.1, h.2.mono_forbidden hX⟩

theorem IsAvoidingPath.mono_permitted {p : G.Walk x y} {X P P' : Set V}
    (h : p.IsAvoidingPath X P) (hP : P ⊆ P') : p.IsAvoidingPath X P' :=
  ⟨h.1, h.2.mono_permitted hP⟩

theorem IsAvoidingPath.mapLe {G G' : SimpleGraph V} (hGG' : G ≤ G')
    {x y : V} {p : G.Walk x y} {X P : Set V} (h : p.IsAvoidingPath X P) :
    (p.mapLe hGG').IsAvoidingPath X P :=
  ⟨h.1.mapLe hGG', h.2.mapLe hGG'⟩

theorem IsAvoidingPath.reverse {x y : V} {p : G.Walk x y} {X P : Set V}
    (h : p.IsAvoidingPath X P) : p.reverse.IsAvoidingPath X P :=
  ⟨h.1.reverse, h.2.reverse⟩

end SimpleGraph.Walk

namespace Erdos63

/-- `y` is reachable from `root` by a simple path of length at most `radius`
whose only permitted vertex in `forbidden` is `root` itself. -/
def ReachWithin (G : SimpleGraph V) (forbidden : Set V) (root : V)
    (radius : ℕ) (y : V) : Prop :=
  ∃ p : G.Walk root y,
    p.IsAvoidingPath forbidden ({root} : Set V) ∧ p.length ≤ radius

@[simp] theorem reachWithin_refl (G : SimpleGraph V) (forbidden : Set V)
    (root : V) (radius : ℕ) : ReachWithin G forbidden root radius root := by
  refine ⟨Walk.nil, ⟨Walk.IsPath.nil, ?_⟩, by simp⟩
  simp

theorem ReachWithin.radius_mono {forbidden : Set V} {root y : V} {r s : ℕ}
    (h : ReachWithin G forbidden root r y) (hrs : r ≤ s) :
    ReachWithin G forbidden root s y := by
  obtain ⟨p, hp, hlen⟩ := h
  exact ⟨p, hp, hlen.trans hrs⟩

theorem ReachWithin.forbidden_anti {X Y : Set V} {root y : V} {r : ℕ}
    (h : ReachWithin G X root r y) (hYX : Y ⊆ X) :
    ReachWithin G Y root r y := by
  obtain ⟨p, hp, hlen⟩ := h
  exact ⟨p, hp.mono_forbidden hYX, hlen⟩

theorem ReachWithin.mono_graph {G G' : SimpleGraph V} (hGG' : G ≤ G')
    {X : Set V} {root y : V} {r : ℕ} (h : ReachWithin G X root r y) :
    ReachWithin G' X root r y := by
  obtain ⟨p, hp, hlen⟩ := h
  exact ⟨p.mapLe hGG', hp.mapLe hGG', by simpa using hlen⟩

theorem ReachWithin.eq_root_or_not_mem {X : Set V} {root y : V} {r : ℕ}
    (h : ReachWithin G X root r y) : y = root ∨ y ∉ X := by
  obtain ⟨p, hp, -⟩ := h
  by_cases hyX : y ∈ X
  · left
    exact Set.mem_singleton_iff.1 (hp.2 y p.end_mem_support hyX)
  · exact Or.inr hyX

@[simp] theorem reachWithin_zero_iff (G : SimpleGraph V) (X : Set V) (root y : V) :
    ReachWithin G X root 0 y ↔ y = root := by
  constructor
  · rintro ⟨p, -, hlen⟩
    exact (p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)).symm
  · rintro rfl
    exact reachWithin_refl G X y 0

/-- The finite ball of radius `r` obtained while avoiding `forbidden`; the
root is retained even when it belongs to `forbidden`. -/
noncomputable def ballAvoiding [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) (r : ℕ) : Finset V := by
  classical
  exact Finset.univ.filter (ReachWithin G forbidden root r)

@[simp] theorem mem_ballAvoiding [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) (r : ℕ) (y : V) :
    y ∈ ballAvoiding G forbidden root r ↔ ReachWithin G forbidden root r y := by
  classical
  simp [ballAvoiding]

@[simp] theorem root_mem_ballAvoiding [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) (r : ℕ) :
    root ∈ ballAvoiding G forbidden root r := by
  simp

@[simp] theorem ballAvoiding_zero [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) : ballAvoiding G forbidden root 0 = {root} := by
  classical
  ext y
  simp

theorem ballAvoiding_radius_mono [Fintype V] (G : SimpleGraph V)
    (forbidden : Set V) (root : V) {r s : ℕ} (hrs : r ≤ s) :
    ballAvoiding G forbidden root r ⊆ ballAvoiding G forbidden root s := by
  classical
  intro y hy
  rw [mem_ballAvoiding] at hy ⊢
  exact hy.radius_mono hrs

theorem ballAvoiding_forbidden_anti [Fintype V] (G : SimpleGraph V)
    {X Y : Set V} (hYX : Y ⊆ X) (root : V) (r : ℕ) :
    ballAvoiding G X root r ⊆ ballAvoiding G Y root r := by
  classical
  intro y hy
  rw [mem_ballAvoiding] at hy ⊢
  exact hy.forbidden_anti hYX

theorem ballAvoiding_mono_graph [Fintype V] {G G' : SimpleGraph V}
    (hGG' : G ≤ G') (X : Set V) (root : V) (r : ℕ) :
    ballAvoiding G X root r ⊆ ballAvoiding G' X root r := by
  classical
  intro y hy
  rw [mem_ballAvoiding] at hy ⊢
  exact hy.mono_graph hGG'

theorem ballAvoiding_subset_insert_compl [Fintype V] (G : SimpleGraph V)
    (X : Set V) (root : V) (r : ℕ) :
    (ballAvoiding G X root r : Set V) ⊆ {root} ∪ Xᶜ := by
  intro y hy
  rcases (mem_ballAvoiding G X root r y).1 hy |>.eq_root_or_not_mem with h | h
  · exact Or.inl (by simpa [h])
  · exact Or.inr h

end Erdos63
