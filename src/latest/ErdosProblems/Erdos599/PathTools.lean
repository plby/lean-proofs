/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos599.DirectedPath
import ErdosProblems.Erdos599.Wave
import Mathlib.Data.Set.Countable

/-!
# Concrete operations on directed finite paths and rays

This file connects the elementary endpoint-indexed paths in
`DirectedPath.lean` to the abstract path interface used by the wave
calculus.  In particular it supplies the length-zero path, finite/ray
case operations, forward extension, set truncations and last exits,
change-of-graph lifts, and countability of every path support.
-/

namespace Erdos599.DirectedPath

open Function

universe u

variable {V : Type u}

namespace FinitePath

variable {D E : Digraph V}

/-- The length-zero finite path at `x`. -/
def trivial (D : Digraph V) (x : V) : FinitePath D where
  start := x
  finish := x
  walk := .nil
  isPath := Walk.isPath_nil x

@[simp] theorem trivial_start (D : Digraph V) (x : V) : (trivial D x).start = x := rfl

@[simp] theorem trivial_finish (D : Digraph V) (x : V) : (trivial D x).finish = x := rfl

@[simp] theorem trivial_walk (D : Digraph V) (x : V) :
    (trivial D x).walk = (.nil : Walk D x x) := rfl

@[simp] theorem support_trivial (D : Digraph V) (x : V) :
    (trivial D x).support = {x} := by
  ext y
  simp [support, trivial]

/-- The support of a finite path is finite. -/
theorem support_finite (p : FinitePath D) : p.support.Finite := by
  change {x | x ∈ p.walk.support}.Finite
  exact p.walk.support.finite_toSet

/-- Hence the support of a finite path is countable. -/
theorem support_countable (p : FinitePath D) : p.support.Countable :=
  p.support_finite.countable

@[simp] theorem support_length_pos (p : FinitePath D) : 0 < p.walk.support.length :=
  List.length_pos_iff.mpr p.walk.support_ne_nil

@[simp] theorem support_getElem_zero (p : FinitePath D) :
    p.walk.support[0] = p.start := by
  exact (List.getElem_zero p.support_length_pos).trans p.walk.head_support

/-- `p` is an initial finite segment of `q` when its ordered support is a
list prefix of the ordered support of `q`. -/
def IsPrefixOf (p q : FinitePath D) : Prop :=
  p.walk.support <+: q.walk.support

theorem isPrefixOf_refl (p : FinitePath D) : p.IsPrefixOf p :=
  List.prefix_rfl

theorem IsPrefixOf.trans {p q r : FinitePath D} (hpq : p.IsPrefixOf q)
    (hqr : q.IsPrefixOf r) : p.IsPrefixOf r :=
  List.IsPrefix.trans hpq hqr

theorem IsPrefixOf.support_subset {p q : FinitePath D} (h : p.IsPrefixOf q) :
    p.support ⊆ q.support :=
  h.subset

theorem IsPrefixOf.start_eq {p q : FinitePath D} (h : p.IsPrefixOf q) :
    p.start = q.start := by
  have hz := h.getElem (i := 0) p.support_length_pos
  simpa using hz

/-- A finite path is an initial segment of a ray when its ordered vertices
agree with the ray at every index occupied by the finite path. -/
def IsInitialSegmentOf (p : FinitePath D) (r : Ray D) : Prop :=
  ∀ n (hn : n < p.walk.support.length), p.walk.support[n] = r n

theorem IsInitialSegmentOf.start_eq {p : FinitePath D} {r : Ray D}
    (h : p.IsInitialSegmentOf r) : p.start = r.initial := by
  simpa [Ray.initial] using h 0 p.support_length_pos

theorem IsInitialSegmentOf.support_subset {p : FinitePath D} {r : Ray D}
    (h : p.IsInitialSegmentOf r) : p.support ⊆ r.support := by
  intro x hx
  change x ∈ p.walk.support at hx
  rcases List.mem_iff_getElem.mp hx with ⟨n, hn, hnx⟩
  refine ⟨n, ?_⟩
  calc
    r n = p.walk.support[n] := (h n hn).symm
    _ = x := hnx

/-- Bundle the append of a finite path and an endpoint-compatible walk.
The simplicity proof is explicit because append is only a path when the
two pieces have no repeated vertex away from their common endpoint. -/
def appendWalk (p : FinitePath D) {w : V} (q : Walk D p.finish w)
    (hpath : (p.walk.append q).IsPath) : FinitePath D where
  start := p.start
  finish := w
  walk := p.walk.append q
  isPath := hpath

@[simp] theorem appendWalk_start (p : FinitePath D) {w : V}
    (q : Walk D p.finish w) (hpath) : (p.appendWalk q hpath).start = p.start := rfl

@[simp] theorem appendWalk_finish (p : FinitePath D) {w : V}
    (q : Walk D p.finish w) (hpath) : (p.appendWalk q hpath).finish = w := rfl

@[simp] theorem appendWalk_support (p : FinitePath D) {w : V}
    (q : Walk D p.finish w) (hpath) :
    (p.appendWalk q hpath).walk.support = p.walk.support ++ q.support.tail :=
  Walk.support_append p.walk q

/-- Append a simple walk whose vertices after the common endpoint are
disjoint from the old path. -/
def appendWalkOfDisjoint (p : FinitePath D) {w : V} (q : Walk D p.finish w)
    (hq : q.IsPath) (hdisjoint : p.walk.support.Disjoint q.support.tail) :
    FinitePath D :=
  p.appendWalk q <| by
    rw [Walk.IsPath, Walk.support_append]
    exact p.isPath.append hq.tail hdisjoint

/-- Bundle the first hit of a set along a finite path. -/
noncomputable def firstHit (p : FinitePath D) (S : Set V) (h : p.walk.Meets S) :
    FinitePath D :=
  let F := p.walk.firstHit S h
  { start := p.start
    finish := F.endpoint
    walk := F.walk
    isPath := F.isPath p.isPath }

/-- Bundle the last hit (last exit point) of a set along a finite path. -/
noncomputable def lastHit (p : FinitePath D) (S : Set V) (h : p.walk.Meets S) :
    FinitePath D :=
  let L := p.walk.lastHit S h
  { start := L.startpoint
    finish := p.finish
    walk := L.walk
    isPath := L.isPath p.isPath }

/-- Source terminology for the suffix beginning at the last vertex in a
specified set. -/
noncomputable def lastExit (p : FinitePath D) (S : Set V) (h : p.walk.Meets S) :
    FinitePath D :=
  p.lastHit S h

theorem firstHit_support_subset (p : FinitePath D) (S : Set V) (h : p.walk.Meets S) :
    (p.firstHit S h).support ⊆ p.support :=
  (p.walk.firstHit S h).support_subset

theorem lastHit_support_subset (p : FinitePath D) (S : Set V) (h : p.walk.Meets S) :
    (p.lastHit S h).support ⊆ p.support :=
  (p.walk.lastHit S h).support_subset

@[simp] theorem firstHit_finish_mem (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) : (p.firstHit S h).finish ∈ S :=
  (p.walk.firstHit S h).endpoint_mem

@[simp] theorem lastHit_start_mem (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) : (p.lastHit S h).start ∈ S :=
  (p.walk.lastHit S h).startpoint_mem

theorem firstHit_no_mem_before (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) ⦃x : V⦄
    (hx : x ∈ (p.firstHit S h).walk.support.dropLast) : x ∉ S :=
  (p.walk.firstHit S h).no_mem_before hx

theorem lastHit_no_mem_after (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) ⦃x : V⦄
    (hx : x ∈ (p.lastHit S h).walk.support.tail) : x ∉ S :=
  (p.walk.lastHit S h).no_mem_after hx

/-- The suffix of `p` beginning at its unique occurrence of `u`.  This is
the convenient bundled form used when an alternating construction continues
along a reference path from a vertex already reached. -/
noncomputable def suffixFrom (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) : FinitePath D :=
  p.lastHit {u} ⟨u, hu, Set.mem_singleton u⟩

@[simp]
theorem suffixFrom_start (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) : (p.suffixFrom u hu).start = u := by
  unfold suffixFrom
  have hmem := p.lastHit_start_mem {u} ⟨u, hu, Set.mem_singleton u⟩
  simpa only [Set.mem_singleton_iff] using hmem

@[simp]
theorem suffixFrom_finish (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) : (p.suffixFrom u hu).finish = p.finish :=
  rfl

theorem suffixFrom_support_subset (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) : (p.suffixFrom u hu).support ⊆ p.support :=
  p.lastHit_support_subset {u} ⟨u, hu, Set.mem_singleton u⟩

theorem suffixFrom_no_u_after (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) {x : V}
    (hx : x ∈ (p.suffixFrom u hu).walk.support.tail) : x ≠ u := by
  intro hxu
  subst x
  exact p.lastHit_no_mem_after {u} ⟨u, hu, Set.mem_singleton u⟩ hx
    (Set.mem_singleton u)

/-- The segment beginning at `u` and ending at the first subsequent hit of
`S`.  Its input says exactly that the suffix beginning at `u` meets `S`. -/
noncomputable def firstHitAfter (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) : FinitePath D :=
  (p.suffixFrom u hu).firstHit S hS

@[simp]
theorem firstHitAfter_start (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) :
    (p.firstHitAfter u hu S hS).start = u := by
  change (p.suffixFrom u hu).start = u
  exact p.suffixFrom_start u hu

@[simp]
theorem firstHitAfter_finish_mem (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) :
    (p.firstHitAfter u hu S hS).finish ∈ S :=
  (p.suffixFrom u hu).firstHit_finish_mem S hS

theorem firstHitAfter_support_subset (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) :
    (p.firstHitAfter u hu S hS).support ⊆ p.support :=
  ((p.suffixFrom u hu).firstHit_support_subset S hS).trans
    (p.suffixFrom_support_subset u hu)

theorem firstHitAfter_no_mem_before (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) {x : V}
    (hx : x ∈ (p.firstHitAfter u hu S hS).walk.support.dropLast) : x ∉ S :=
  (p.suffixFrom u hu).firstHit_no_mem_before S hS hx

/-- A bundled finite-path version of `Walk.SetTruncation`. -/
structure SetTruncation (p : FinitePath D) (A B : Set V) where
  path : FinitePath D
  start_mem : path.start ∈ A
  finish_mem : path.finish ∈ B
  support_subset : path.support ⊆ p.support
  no_mem_left_after : ∀ ⦃x⦄, x ∈ path.walk.support.tail → x ∉ A
  no_mem_right_before : ∀ ⦃x⦄, x ∈ path.walk.support.dropLast → x ∉ B

/-- Truncate a finite path at the first `B`-vertex and then the last
`A`-vertex. -/
noncomputable def setTruncation (p : FinitePath D) (A B : Set V)
    (hA : p.start ∈ A) (hB : p.finish ∈ B) : SetTruncation p A B := by
  let T := Classical.choice (p.walk.exists_setTruncation A B hA hB)
  exact
    { path :=
        { start := T.startpoint
          finish := T.endpoint
          walk := T.walk
          isPath := T.isPath p.isPath }
      start_mem := T.startpoint_mem
      finish_mem := T.endpoint_mem
      support_subset := T.support_subset
      no_mem_left_after := T.no_mem_left_after
      no_mem_right_before := T.no_mem_right_before }

/-- Short name for the canonical two-sided set truncation. -/
noncomputable def truncate (p : FinitePath D) (A B : Set V)
    (hA : p.start ∈ A) (hB : p.finish ∈ B) : SetTruncation p A B :=
  p.setTruncation A B hA hB

end FinitePath

namespace Ray

variable {D : Digraph V}

/-- Every ray has countable support. -/
theorem support_countable (r : Ray D) : r.support.Countable :=
  Set.countable_range r.toFun

end Ray

namespace Path

variable {D E : Digraph V}

/-- The length-zero path at `x`, regarded as a finite-or-infinite path. -/
def trivial (D : Digraph V) (x : V) : Path D :=
  .inl (FinitePath.trivial D x)

/-- A finite path has its final vertex as terminal; a ray has no terminal. -/
def terminal? : Path D → Option V
  | .inl p => some p.finish
  | .inr _ => none

@[simp] theorem terminal?_finite (p : FinitePath D) : terminal? (.inl p) = some p.finish := rfl

@[simp] theorem terminal?_ray (r : Ray D) : terminal? (.inr r) = none := rfl

@[simp] theorem support_trivial (D : Digraph V) (x : V) :
    support (trivial D x) = {x} :=
  FinitePath.support_trivial D x

@[simp] theorem initial_trivial (D : Digraph V) (x : V) : initial (trivial D x) = x := rfl

@[simp] theorem terminal?_trivial (D : Digraph V) (x : V) :
    terminal? (trivial D x) = some x := rfl

theorem terminal_mem_support (p : Path D) (t : V) (h : p.terminal? = some t) :
    t ∈ p.support := by
  rcases p with p | r
  · have ht : p.finish = t := Option.some.inj h
    exact ht ▸ p.finish_mem_support
  · simp at h

/-- Concrete finiteness and ray predicates, stated through `terminal?` so
they match the abstract wave interface. -/
def IsFinite (p : Path D) : Prop := ∃ t, p.terminal? = some t

def IsRay (p : Path D) : Prop := p.terminal? = none

@[simp] theorem isFinite_finite (p : FinitePath D) : IsFinite (.inl p) :=
  ⟨p.finish, rfl⟩

@[simp] theorem not_isFinite_ray (r : Ray D) : ¬IsFinite (.inr r) := by
  rintro ⟨t, h⟩
  simp at h

@[simp] theorem not_isRay_finite (p : FinitePath D) : ¬IsRay (.inl p) := by
  simp [IsRay]

@[simp] theorem isRay_ray (r : Ray D) : IsRay (.inr r) := rfl

theorem finite_or_ray (p : Path D) :
    (∃ q : FinitePath D, p = .inl q) ∨ (∃ r : Ray D, p = .inr r) := by
  rcases p with p | r
  · exact Or.inl ⟨p, rfl⟩
  · exact Or.inr ⟨r, rfl⟩

/-- Forward extension of concrete paths.  A finite path may extend to a
longer finite prefix or to a ray with the same finite initial segment.  An
already infinite ray can only extend to itself. -/
def Extends : Path D → Path D → Prop
  | .inl p, .inl q => p.IsPrefixOf q
  | .inl p, .inr r => p.IsInitialSegmentOf r
  | .inr r, .inr s => r = s
  | .inr _, .inl _ => False

@[simp] theorem extends_finite_finite (p q : FinitePath D) :
    Extends (.inl p) (.inl q) ↔ p.IsPrefixOf q := Iff.rfl

@[simp] theorem extends_finite_ray (p : FinitePath D) (r : Ray D) :
    Extends (.inl p) (.inr r) ↔ p.IsInitialSegmentOf r := Iff.rfl

@[simp] theorem extends_ray_ray (r s : Ray D) :
    Extends (.inr r) (.inr s) ↔ r = s := Iff.rfl

@[simp] theorem not_extends_ray_finite (r : Ray D) (p : FinitePath D) :
    ¬Extends (.inr r) (.inl p) := by simp [Extends]

theorem extends_refl (p : Path D) : Extends p p := by
  rcases p with p | r
  · exact p.isPrefixOf_refl
  · rfl

theorem extends_trans {p q r : Path D} (hpq : Extends p q) (hqr : Extends q r) :
    Extends p r := by
  rcases p with p | p <;> rcases q with q | q <;> rcases r with r | r
  · exact hpq.trans hqr
  · intro n hn
    rw [hpq.getElem hn]
    exact hqr n (lt_of_lt_of_le hn hpq.length_le)
  · exact False.elim hqr
  · exact hqr ▸ hpq
  · exact False.elim hpq
  · exact False.elim hpq
  · exact False.elim hqr
  · exact hpq.trans hqr

theorem extends_initial {p q : Path D} (h : Extends p q) : p.initial = q.initial := by
  rcases p with p | p <;> rcases q with q | q
  · exact h.start_eq
  · exact h.start_eq
  · exact False.elim h
  · simpa [initial] using congrArg Ray.initial h

theorem support_mono_of_extends {p q : Path D} (h : Extends p q) :
    p.support ⊆ q.support := by
  rcases p with p | p <;> rcases q with q | q
  · exact h.support_subset
  · exact h.support_subset
  · exact False.elim h
  · change p = q at h
    subst q
    exact fun _ hx ↦ hx

/-- Every concrete path, finite or a ray, has countable support. -/
theorem support_countable (p : Path D) : p.support.Countable := by
  rcases p with p | r
  · exact p.support_countable
  · exact r.support_countable

end Path

/-! ## Change of graph and undirected lifting -/

namespace Walk

variable {D E : Digraph V} {u v : V}

/-- Lift a walk along an inclusion of directed edge relations. -/
def lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) {u v : V} :
    Walk D u v → Walk E u v
  | .nil => .nil
  | .cons h p => .cons (hDE h) (p.lift hDE)

@[simp] theorem support_lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (p : Walk D u v) : (p.lift hDE).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [lift, ih]

@[simp] theorem length_lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (p : Walk D u v) : (p.lift hDE).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [lift, ih]

theorem isPath_lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    {p : Walk D u v} (hp : p.IsPath) : (p.lift hDE).IsPath := by
  simpa [IsPath] using hp

/-- Regard a `SimpleGraph` walk as a directed walk in its bidirected graph. -/
def ofSimpleGraph {G : SimpleGraph V} {u v : V} :
    G.Walk u v → Walk (bidirect G) u v
  | .nil => .nil
  | .cons h p => .cons h (ofSimpleGraph p)

@[simp] theorem support_ofSimpleGraph {G : SimpleGraph V} (p : G.Walk u v) :
    (ofSimpleGraph p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change _ :: (ofSimpleGraph p).support = _ :: p.support
      rw [ih]

@[simp] theorem length_ofSimpleGraph {G : SimpleGraph V} (p : G.Walk u v) :
    (ofSimpleGraph p).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
      change (ofSimpleGraph p).length + 1 = p.length + 1
      rw [ih]

theorem isPath_ofSimpleGraph {G : SimpleGraph V} {p : G.Walk u v} (hp : p.IsPath) :
    (ofSimpleGraph p).IsPath := by
  rw [IsPath, support_ofSimpleGraph]
  exact hp.support_nodup

/-- Forget the directed orientation of a walk in a bidirected simple graph. -/
def toSimpleGraph {G : SimpleGraph V} {u v : V} :
    Walk (bidirect G) u v → G.Walk u v
  | .nil => .nil
  | .cons h p => .cons h (toSimpleGraph p)

@[simp] theorem toSimpleGraph_ofSimpleGraph {G : SimpleGraph V} (p : G.Walk u v) :
    toSimpleGraph (ofSimpleGraph p) = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ofSimpleGraph, toSimpleGraph, ih]

@[simp] theorem ofSimpleGraph_toSimpleGraph {G : SimpleGraph V}
    (p : Walk (bidirect G) u v) : ofSimpleGraph (toSimpleGraph p) = p := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [ofSimpleGraph, toSimpleGraph, ih]

end Walk

namespace FinitePath

variable {D E : Digraph V}

/-- Lift a finite path along an inclusion of directed edge relations. -/
def lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) (p : FinitePath D) : FinitePath E where
  start := p.start
  finish := p.finish
  walk := p.walk.lift hDE
  isPath := p.walk.isPath_lift hDE p.isPath

@[simp] theorem support_lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (p : FinitePath D) : (p.lift hDE).support = p.support := by
  ext x
  simp [support, lift]

/-- Lift a simple-graph path into the corresponding bidirected graph. -/
def ofSimpleGraph {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    FinitePath (bidirect G) where
  start := u
  finish := v
  walk := Walk.ofSimpleGraph p
  isPath := Walk.isPath_ofSimpleGraph hp

end FinitePath

namespace Ray

variable {D E : Digraph V}

/-- Lift a ray along an inclusion of directed edge relations. -/
def lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) (r : Ray D) : Ray E where
  toFun := r.toFun
  adj_succ n := hDE (r.adj_succ n)
  injective := r.injective

@[simp] theorem support_lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (r : Ray D) : (r.lift hDE).support = r.support := rfl

end Ray

namespace Path

variable {D E : Digraph V}

/-- Lift a finite-or-infinite path along an inclusion of edge relations. -/
def lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y) : Path D → Path E
  | .inl p => .inl (p.lift hDE)
  | .inr r => .inr (r.lift hDE)

@[simp] theorem support_lift (hDE : ∀ {x y}, D.Adj x y → E.Adj x y)
    (p : Path D) : (p.lift hDE).support = p.support := by
  rcases p with p | r
  · exact p.support_lift hDE
  · exact r.support_lift hDE

end Path

/-! ## Directed edge sets and subpaths -/

variable {D : Digraph V}

/-- The directed edges occurring in a finite walk. -/
def Walk.edgeSet {a b : V} : Walk D a b → Set (V × V)
  | .nil => ∅
  | @Walk.cons _ _ x y z h p => {(x, y)} ∪ Walk.edgeSet p

@[simp]
theorem Walk.edgeSet_nil (x : V) :
    (Walk.nil : Walk D x x).edgeSet = ∅ :=
  rfl

@[simp]
theorem Walk.edgeSet_cons {x y z : V} (h : D.Adj x y) (p : Walk D y z) :
    (Walk.cons h p).edgeSet = {(x, y)} ∪ p.edgeSet :=
  rfl

/-- The directed edges occurring in a finite path. -/
def FinitePath.edgeSet (p : FinitePath D) : Set (V × V) :=
  p.walk.edgeSet

/-- The directed edges occurring in a ray. -/
def Ray.edgeSet (r : Ray D) : Set (V × V) :=
  {e | ∃ n : ℕ, e = (r n, r (n + 1))}

/-- The directed edges occurring in a finite path or ray. -/
def Path.edgeSet : Path D → Set (V × V)
  | .inl p => p.edgeSet
  | .inr r => r.edgeSet

/-- An ordered support prefix of a walk uses only edges of the larger walk.
The ordered-list hypothesis is essential: a mere support inclusion would not
exclude taking a chord between two vertices of the larger walk. -/
theorem Walk.edgeSet_subset_of_support_prefix
    {a b c d : V} (p : Walk D a b) (q : Walk D c d)
    (hpq : p.support <+: q.support) : p.edgeSet ⊆ q.edgeSet := by
  induction q generalizing a b p with
  | nil =>
      cases p with
      | nil => simp
      | @cons a x b hp pt =>
          have hlen := hpq.length_le
          simp only [Walk.support_cons, Walk.support_nil, List.length_cons,
            List.length_nil] at hlen
          have hz : pt.support.length = 0 := by omega
          exact (pt.support_ne_nil (List.length_eq_zero_iff.mp hz)).elim
  | @cons c x d hq qt ih =>
      cases p with
      | nil => simp
      | @cons a y b hp pt =>
          simp only [Walk.support_cons] at hpq
          rcases List.cons_prefix_cons.mp hpq with ⟨hac, htail⟩
          have hyx : y = x := by
            have hpos : 0 < pt.support.length :=
              List.length_pos_iff.mpr pt.support_ne_nil
            have hqpos : 0 < qt.support.length :=
              List.length_pos_iff.mpr qt.support_ne_nil
            have hget := htail.getElem (i := 0) hpos
            calc
              y = pt.support.head pt.support_ne_nil := pt.head_support.symm
              _ = pt.support[0] := List.head_eq_getElem pt.support_ne_nil
              _ = qt.support[0]'hqpos := hget
              _ = qt.support.head qt.support_ne_nil :=
                (List.head_eq_getElem qt.support_ne_nil).symm
              _ = x := qt.head_support
          subst a
          subst y
          intro e he
          simp only [Walk.edgeSet_cons, Set.mem_union,
            Set.mem_singleton_iff] at he ⊢
          rcases he with rfl | he
          · exact Or.inl rfl
          · exact Or.inr (ih pt htail he)

/-- An ordered support suffix of a walk uses only edges of the larger walk. -/
theorem Walk.edgeSet_subset_of_support_suffix
    {a b c d : V} (p : Walk D a b) (q : Walk D c d)
    (hpq : p.support <:+ q.support) : p.edgeSet ⊆ q.edgeSet := by
  induction q generalizing a b p with
  | nil =>
      rcases List.suffix_cons_iff.mp hpq with heq | hempty
      · exact Walk.edgeSet_subset_of_support_prefix p (.nil)
          (heq ▸ List.prefix_rfl)
      · have hnil : p.support = [] := by
          simpa only [List.suffix_nil] using hempty
        exact (p.support_ne_nil hnil).elim
  | @cons c x d hq qt ih =>
      rcases List.suffix_cons_iff.mp hpq with heq | htail
      · exact Walk.edgeSet_subset_of_support_prefix p (.cons hq qt)
          (heq ▸ List.prefix_rfl)
      · exact (ih p htail).trans Set.subset_union_right

@[simp]
theorem Path.edgeSet_finite (p : FinitePath D) :
    Path.edgeSet (Sum.inl p) = p.edgeSet :=
  rfl

@[simp]
theorem Path.edgeSet_ray (r : Ray D) :
    Path.edgeSet (Sum.inr r) = r.edgeSet :=
  rfl

theorem Walk.edgeSet_subset_support_prod {a b : V} (p : Walk D a b) :
    p.edgeSet ⊆ {e | e.1 ∈ p.support ∧ e.2 ∈ p.support} := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
      intro e he
      simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff] at he
      rcases he with rfl | he
      · exact ⟨by simp, by simp⟩
      · have hp := ih he
        exact ⟨by simp [hp.1], by simp [hp.2]⟩

theorem FinitePath.edgeSet_subset_support_prod (p : FinitePath D) :
    p.edgeSet ⊆ {e | e.1 ∈ p.support ∧ e.2 ∈ p.support} :=
  p.walk.edgeSet_subset_support_prod

theorem Ray.edgeSet_subset_support_prod (r : Ray D) :
    r.edgeSet ⊆ {e | e.1 ∈ r.support ∧ e.2 ∈ r.support} := by
  rintro e ⟨n, rfl⟩
  exact ⟨r.apply_mem_support n, r.apply_mem_support (n + 1)⟩

theorem Path.edgeSet_subset_support_prod (p : Path D) :
    p.edgeSet ⊆ {e | e.1 ∈ p.support ∧ e.2 ∈ p.support} := by
  rcases p with p | r
  · exact p.edgeSet_subset_support_prod
  · exact r.edgeSet_subset_support_prod

theorem Walk.edgeSet_subset_adj {a b : V} (p : Walk D a b) :
    p.edgeSet ⊆ {e | D.Adj e.1 e.2} := by
  induction p with
  | nil => simp
  | @cons x y z h p ih =>
      intro e he
      simp only [Walk.edgeSet_cons, Set.mem_union, Set.mem_singleton_iff] at he
      rcases he with rfl | he
      · exact h
      · exact ih he

theorem FinitePath.edgeSet_subset_adj (p : FinitePath D) :
    p.edgeSet ⊆ {e | D.Adj e.1 e.2} :=
  p.walk.edgeSet_subset_adj

theorem Ray.edgeSet_subset_adj (r : Ray D) :
    r.edgeSet ⊆ {e | D.Adj e.1 e.2} := by
  rintro e ⟨n, rfl⟩
  exact r.adj_succ n

theorem Path.edgeSet_subset_adj (p : Path D) :
    p.edgeSet ⊆ {e | D.Adj e.1 e.2} := by
  rcases p with p | r
  · exact p.edgeSet_subset_adj
  · exact r.edgeSet_subset_adj

/-- A path is a subpath of `p` when all its vertices and directed edges occur
on `p`.  Since both objects are simple directed paths, connectedness makes
this equivalent to being an interval of `p`. -/
def Path.IsSubpathOf (q p : Path D) : Prop :=
  q.support ⊆ p.support ∧ q.edgeSet ⊆ p.edgeSet

/-- The finite-path specialization of `Path.IsSubpathOf`. -/
def FinitePath.IsSubpathOf (q : FinitePath D) (p : Path D) : Prop :=
  Path.IsSubpathOf (.inl q) p

theorem FinitePath.isSubpathOf_self (p : FinitePath D) :
    p.IsSubpathOf (Sum.inl p) :=
  ⟨Set.Subset.rfl, Set.Subset.rfl⟩

theorem Path.isSubpathOf_self (p : Path D) : p.IsSubpathOf p :=
  ⟨Set.Subset.rfl, Set.Subset.rfl⟩

theorem FinitePath.firstHit_edgeSet_subset (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) : (p.firstHit S h).edgeSet ⊆ p.edgeSet := by
  apply Walk.edgeSet_subset_of_support_prefix
  exact (p.walk.firstHit S h).support_prefix

theorem FinitePath.lastHit_edgeSet_subset (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) : (p.lastHit S h).edgeSet ⊆ p.edgeSet := by
  apply Walk.edgeSet_subset_of_support_suffix
  exact (p.walk.lastHit S h).support_suffix

theorem FinitePath.suffixFrom_edgeSet_subset (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) : (p.suffixFrom u hu).edgeSet ⊆ p.edgeSet :=
  p.lastHit_edgeSet_subset {u} ⟨u, hu, Set.mem_singleton u⟩

theorem FinitePath.firstHitAfter_edgeSet_subset (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) :
    (p.firstHitAfter u hu S hS).edgeSet ⊆ p.edgeSet :=
  ((p.suffixFrom u hu).firstHit_edgeSet_subset S hS).trans
    (p.suffixFrom_edgeSet_subset u hu)

theorem FinitePath.firstHit_isSubpathOf (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) : (p.firstHit S h).IsSubpathOf (Sum.inl p) :=
  ⟨p.firstHit_support_subset S h, p.firstHit_edgeSet_subset S h⟩

theorem FinitePath.lastHit_isSubpathOf (p : FinitePath D) (S : Set V)
    (h : p.walk.Meets S) : (p.lastHit S h).IsSubpathOf (Sum.inl p) :=
  ⟨p.lastHit_support_subset S h, p.lastHit_edgeSet_subset S h⟩

theorem FinitePath.suffixFrom_isSubpathOf (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) : (p.suffixFrom u hu).IsSubpathOf (Sum.inl p) :=
  ⟨p.suffixFrom_support_subset u hu, p.suffixFrom_edgeSet_subset u hu⟩

theorem FinitePath.firstHitAfter_isSubpathOf (p : FinitePath D) (u : V)
    (hu : u ∈ p.support) (S : Set V)
    (hS : (p.suffixFrom u hu).walk.Meets S) :
    (p.firstHitAfter u hu S hS).IsSubpathOf (Sum.inl p) :=
  ⟨p.firstHitAfter_support_subset u hu S hS,
    p.firstHitAfter_edgeSet_subset u hu S hS⟩

/-- The concrete directed paths form the path system required by the
abstract wave calculus. -/
def directedPathSystem (D : Digraph V) :
    WaveCore.DirectedPathSystem V (Path D) where
  support := Path.support
  initial := Path.initial
  terminal := Path.terminal?
  initial_mem := Path.initial_mem_support
  terminal_mem := Path.terminal_mem_support
  trivial := Path.trivial D
  support_trivial := Path.support_trivial D
  initial_trivial := Path.initial_trivial D
  terminal_trivial := Path.terminal?_trivial D
  Extends := Path.Extends
  extends_refl := Path.extends_refl
  extends_trans := Path.extends_trans
  extends_initial := Path.extends_initial
  support_mono_of_extends := Path.support_mono_of_extends

end Erdos599.DirectedPath
