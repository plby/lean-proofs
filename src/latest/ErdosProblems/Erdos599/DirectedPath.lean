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
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.List.Infix

/-!
# Finite directed paths and rays

This file supplies the small amount of directed-path infrastructure used by
the Erdős--Menger development.  Mathlib's `Digraph` is used for the directed
adjacency relation.  Its graph-theory API currently has no walk type, so we
provide an endpoint-indexed finite walk, simple finite paths, and injective
one-way rays.

The constructions are deliberately elementary:

* `Walk.append`, `Walk.concat`, and `Walk.reverse`;
* the bidirected digraph associated to a `SimpleGraph`;
* certified first and last hits of a vertex set;
* truncation of a finite path between two endpoint sets;
* `Ray.tail`, with preservation of adjacency and injectivity;
* `Path`, the disjoint sum of bundled finite paths and rays.
-/

namespace Erdos599.DirectedPath

open Function

universe u

variable {V : Type u}

/-- Replace every undirected edge by the two corresponding directed edges. -/
def bidirect (G : SimpleGraph V) : Digraph V where
  Adj := G.Adj

@[simp]
theorem bidirect_adj (G : SimpleGraph V) (u v : V) :
    (bidirect G).Adj u v ↔ G.Adj u v :=
  Iff.rfl

/-- Reverse every edge of a digraph. -/
def transpose (D : Digraph V) : Digraph V where
  Adj u v := D.Adj v u

@[simp]
theorem transpose_adj (D : Digraph V) (u v : V) :
    (transpose D).Adj u v ↔ D.Adj v u :=
  Iff.rfl

@[simp]
theorem transpose_transpose (D : Digraph V) : transpose (transpose D) = D := by
  ext
  rfl

/-- A finite directed walk, with its initial and terminal vertices in the type. -/
inductive Walk (D : Digraph V) : V → V → Type u
  | nil {u : V} : Walk D u u
  | cons {u v w : V} (h : D.Adj u v) (p : Walk D v w) : Walk D u w

namespace Walk

variable {D : Digraph V} {u v w x : V}

/-- The vertices of a finite directed walk, in traversal order. -/
def support {u v : V} : Walk D u v → List V
  | .nil => [u]
  | .cons _ p => u :: p.support

/-- The number of edges of a finite directed walk. -/
def length {u v : V} : Walk D u v → ℕ
  | .nil => 0
  | .cons _ p => p.length + 1

@[simp] theorem support_nil (u : V) : support (.nil : Walk D u u) = [u] := rfl

@[simp] theorem support_cons (h : D.Adj u v) (p : Walk D v w) :
    support (.cons h p) = u :: p.support := rfl

@[simp] theorem length_nil (u : V) : length (.nil : Walk D u u) = 0 := rfl

@[simp] theorem length_cons (h : D.Adj u v) (p : Walk D v w) :
    length (.cons h p) = p.length + 1 := rfl

@[simp] theorem support_ne_nil (p : Walk D u v) : p.support ≠ [] := by
  cases p <;> simp

@[simp] theorem start_mem_support (p : Walk D u v) : u ∈ p.support := by
  cases p <;> simp

@[simp] theorem end_mem_support (p : Walk D u v) : v ∈ p.support := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]

@[simp] theorem head_support (p : Walk D u v) :
    p.support.head p.support_ne_nil = u := by
  cases p <;> simp

@[simp] theorem getLast_support (p : Walk D u v) :
    p.support.getLast p.support_ne_nil = v := by
  induction p with
  | nil => simp
  | cons h p ih => simpa using ih

/-- Concatenation of composable directed walks. -/
def append {u v w : V} : Walk D u v → Walk D v w → Walk D u w
  | .nil, q => q
  | .cons h p, q => Walk.cons h (p.append q)

/-- Append one directed edge to a directed walk. -/
def concat {u v w : V} (p : Walk D u v) (h : D.Adj v w) : Walk D u w :=
  p.append (Walk.cons h .nil)

@[simp] theorem nil_append (q : Walk D u v) : (.nil : Walk D u u).append q = q := rfl

@[simp] theorem cons_append (h : D.Adj u v) (p : Walk D v w) {z : V}
    (q : Walk D w z) : (Walk.cons h p).append q = Walk.cons h (p.append q) := rfl

@[simp] theorem append_nil : ∀ {u v : V} (p : Walk D u v), p.append .nil = p
  | _, _, .nil => rfl
  | _, _, .cons h p => congrArg (Walk.cons h) (append_nil p)

@[simp] theorem append_assoc : ∀ {u v w z : V} (p : Walk D u v) (q : Walk D v w)
    (r : Walk D w z), (p.append q).append r = p.append (q.append r)
  | _, _, _, _, .nil, q, r => rfl
  | _, _, _, _, .cons h p, q, r => congrArg (Walk.cons h) (append_assoc p q r)

@[simp] theorem length_append : ∀ {u v w : V} (p : Walk D u v) (q : Walk D v w),
    (p.append q).length = p.length + q.length
  | _, _, _, .nil, q => by simp
  | _, _, _, .cons h p, q => by
      change (p.append q).length + 1 = (p.length + 1) + q.length
      rw [length_append p q]
      omega

@[simp] theorem length_concat (p : Walk D u v) (h : D.Adj v w) :
    (p.concat h).length = p.length + 1 := by simp [concat]

@[simp] theorem support_append : ∀ {u v w : V} (p : Walk D u v) (q : Walk D v w),
    (p.append q).support = p.support ++ q.support.tail
  | _, _, _, .nil, q => by
      cases q <;> simp
  | _, _, _, .cons h p, q => congrArg (List.cons _) (support_append p q)

@[simp] theorem support_concat (p : Walk D u v) (h : D.Adj v w) :
    (p.concat h).support = p.support ++ [w] := by
  simp [concat]

/-- Reverse a walk while reversing every directed edge. -/
def reverse {u v : V} : Walk D u v → Walk (transpose D) v u
  | .nil => .nil
  | .cons h p =>
      p.reverse.concat (D := transpose D) (show (transpose D).Adj _ _ from h)

@[simp] theorem support_reverse : ∀ {u v : V} (p : Walk D u v),
    p.reverse.support = p.support.reverse
  | _, _, .nil => by simp [reverse]
  | _, _, .cons h p => by
      rw [reverse, support_concat (D := transpose D), support_reverse]
      simp

@[simp] theorem length_reverse : ∀ {u v : V} (p : Walk D u v), p.reverse.length = p.length
  | _, _, .nil => by simp [reverse]
  | _, _, .cons h p => by
      rw [reverse, length_concat (D := transpose D), length_reverse]
      rfl

@[simp] theorem reverse_append : ∀ {u v w : V} (p : Walk D u v) (q : Walk D v w),
    (p.append q).reverse = q.reverse.append p.reverse
  | _, _, _, .nil, q => by simp [reverse]
  | _, _, _, .cons h p, q => by
      simp [reverse, reverse_append p q, concat, append_assoc]

@[simp] theorem reverse_concat (p : Walk D u v) (h : D.Adj v w) :
    (p.concat h).reverse = Walk.cons (D := transpose D) h p.reverse := by
  rw [concat, reverse_append]
  rfl

@[simp] theorem reverse_reverse : ∀ {u v : V} (p : Walk D u v), p.reverse.reverse = p
  | _, _, .nil => rfl
  | _, _, .cons h p => by
      rw [reverse, reverse_concat, reverse_reverse p]
      congr

/-- A directed walk is a finite path when no vertex is repeated. -/
def IsPath (p : Walk D u v) : Prop := p.support.Nodup

theorem isPath_iff (p : Walk D u v) : p.IsPath ↔ p.support.Nodup := Iff.rfl

@[simp] theorem isPath_nil (u : V) : IsPath (.nil : Walk D u u) := by simp [IsPath]

@[simp] theorem isPath_reverse (p : Walk D u v) : p.reverse.IsPath ↔ p.IsPath := by
  simp [IsPath]

theorem IsPath.reverse {p : Walk D u v} (hp : p.IsPath) : p.reverse.IsPath :=
  (isPath_reverse p).2 hp

/-- A finite endpoint-indexed directed path. -/
abbrev PathTo (D : Digraph V) (u v : V) := {p : Walk D u v // p.IsPath}

/-- A walk meets a set when one of its support vertices belongs to the set. -/
def Meets (p : Walk D u v) (S : Set V) : Prop :=
  ∃ x, x ∈ p.support ∧ x ∈ S

theorem meets_iff (p : Walk D u v) (S : Set V) :
    p.Meets S ↔ ∃ x ∈ p.support, x ∈ S := by rfl

/-- The prefix ending at the first vertex of `S` on `original`. -/
structure FirstHit (original : Walk D u v) (S : Set V) where
  endpoint : V
  walk : Walk D u endpoint
  endpoint_mem : endpoint ∈ S
  support_prefix : walk.support <+: original.support
  no_mem_before : ∀ ⦃x⦄, x ∈ walk.support.dropLast → x ∉ S

/-- The suffix beginning at the last vertex of `S` on `original`. -/
structure LastHit (original : Walk D u v) (S : Set V) where
  startpoint : V
  walk : Walk D startpoint v
  startpoint_mem : startpoint ∈ S
  support_suffix : walk.support <:+ original.support
  no_mem_after : ∀ ⦃x⦄, x ∈ walk.support.tail → x ∉ S

theorem exists_firstHit : ∀ {u v : V} (p : Walk D u v) (S : Set V),
    p.Meets S → Nonempty (FirstHit p S)
  | u, _, .nil, S, hmeet => by
      rcases hmeet with ⟨x, hx, hxS⟩
      have hxu : x = u := by simpa using hx
      subst x
      exact ⟨{
        endpoint := u
        walk := .nil
        endpoint_mem := hxS
        support_prefix := List.prefix_rfl
        no_mem_before := by simp }⟩
  | _, _, .cons (u := u) h p, S, hmeet => by
      by_cases hu : u ∈ S
      · exact ⟨{
          endpoint := u
          walk := .nil
          endpoint_mem := hu
          support_prefix := by simp
          no_mem_before := by simp }⟩
      · have hpmeet : p.Meets S := by
          rcases hmeet with ⟨x, hx, hxS⟩
          simp only [support_cons, List.mem_cons] at hx
          exact hx.elim (fun hxu ↦ (hu (hxu ▸ hxS)).elim) (fun hxp ↦ ⟨x, hxp, hxS⟩)
        obtain ⟨F⟩ := exists_firstHit p S hpmeet
        exact ⟨{
          endpoint := F.endpoint
          walk := .cons h F.walk
          endpoint_mem := F.endpoint_mem
          support_prefix := by
            simp only [support_cons]
            exact (List.prefix_cons_inj u).2 F.support_prefix
          no_mem_before := by
            intro x hx
            rw [support_cons, List.dropLast_cons_of_ne_nil F.walk.support_ne_nil] at hx
            simp only [List.mem_cons] at hx
            exact hx.elim (fun hxu ↦ hxu ▸ hu) (fun hx ↦ F.no_mem_before hx) }⟩

theorem exists_lastHit : ∀ {u v : V} (p : Walk D u v) (S : Set V),
    p.Meets S → Nonempty (LastHit p S)
  | u, _, .nil, S, hmeet => by
      rcases hmeet with ⟨x, hx, hxS⟩
      have hxu : x = u := by simpa using hx
      subst x
      exact ⟨{
        startpoint := u
        walk := .nil
        startpoint_mem := hxS
        support_suffix := List.suffix_rfl
        no_mem_after := by simp }⟩
  | _, _, .cons (u := u) h p, S, hmeet => by
      by_cases hpmeet : p.Meets S
      · obtain ⟨L⟩ := exists_lastHit p S hpmeet
        exact ⟨{
          startpoint := L.startpoint
          walk := L.walk
          startpoint_mem := L.startpoint_mem
          support_suffix := by
            exact L.support_suffix.trans (by simpa using List.suffix_cons u p.support)
          no_mem_after := L.no_mem_after }⟩
      · have hu : u ∈ S := by
          rcases hmeet with ⟨x, hx, hxS⟩
          simp only [support_cons, List.mem_cons] at hx
          exact hx.elim (fun hxu ↦ hxu ▸ hxS)
            (fun hxp ↦ (hpmeet ⟨x, hxp, hxS⟩).elim)
        exact ⟨{
          startpoint := u
          walk := .cons h p
          startpoint_mem := hu
          support_suffix := List.suffix_rfl
          no_mem_after := by
            intro x hx hxS
            exact hpmeet ⟨x, by simpa using hx, hxS⟩ }⟩

/-- The canonical first hit, selected classically from `exists_firstHit`. -/
noncomputable def firstHit (p : Walk D u v) (S : Set V) (h : p.Meets S) : FirstHit p S :=
  Classical.choice (exists_firstHit p S h)

/-- The canonical last hit, selected classically from `exists_lastHit`. -/
noncomputable def lastHit (p : Walk D u v) (S : Set V) (h : p.Meets S) : LastHit p S :=
  Classical.choice (exists_lastHit p S h)

theorem FirstHit.support_subset {p : Walk D u v} {S : Set V} (F : FirstHit p S) :
    F.walk.support ⊆ p.support := F.support_prefix.subset

theorem LastHit.support_subset {p : Walk D u v} {S : Set V} (L : LastHit p S) :
    L.walk.support ⊆ p.support := L.support_suffix.subset

theorem FirstHit.isPath {p : Walk D u v} {S : Set V} (F : FirstHit p S)
    (hp : p.IsPath) : F.walk.IsPath :=
  F.support_prefix.nodup hp

theorem LastHit.isPath {p : Walk D u v} {S : Set V} (L : LastHit p S)
    (hp : p.IsPath) : L.walk.IsPath :=
  L.support_suffix.nodup hp

/-- A subpath whose first vertex is in `A`, last vertex is in `B`, and whose
remaining vertices contain no further `A`-vertex and no earlier `B`-vertex. -/
structure SetTruncation (original : Walk D u v) (A B : Set V) where
  startpoint : V
  endpoint : V
  walk : Walk D startpoint endpoint
  startpoint_mem : startpoint ∈ A
  endpoint_mem : endpoint ∈ B
  support_sublist : walk.support.Sublist original.support
  no_mem_left_after : ∀ ⦃x⦄, x ∈ walk.support.tail → x ∉ A
  no_mem_right_before : ∀ ⦃x⦄, x ∈ walk.support.dropLast → x ∉ B

theorem SetTruncation.support_subset {p : Walk D u v} {A B : Set V}
    (T : SetTruncation p A B) : T.walk.support ⊆ p.support :=
  T.support_sublist.subset

/-- Truncate a directed walk with left endpoint in `A` and right endpoint in
`B` at its first `B`-vertex and then its last `A`-vertex. -/
theorem exists_setTruncation (p : Walk D u v) (A B : Set V) (hu : u ∈ A) (hv : v ∈ B) :
    Nonempty (SetTruncation p A B) := by
  have hB : p.Meets B := ⟨v, p.end_mem_support, hv⟩
  obtain ⟨F⟩ := exists_firstHit p B hB
  have hA : F.walk.Meets A := ⟨u, F.walk.start_mem_support, hu⟩
  obtain ⟨L⟩ := exists_lastHit F.walk A hA
  refine ⟨{
    startpoint := L.startpoint
    endpoint := F.endpoint
    walk := L.walk
    startpoint_mem := L.startpoint_mem
    endpoint_mem := F.endpoint_mem
    support_sublist := L.support_suffix.sublist.trans F.support_prefix.sublist
    no_mem_left_after := L.no_mem_after
    no_mem_right_before := ?_ }⟩
  intro x hx
  apply F.no_mem_before
  rcases L.support_suffix with ⟨pre, hpre⟩
  rw [← hpre, List.dropLast_append_of_ne_nil L.walk.support_ne_nil]
  exact List.mem_append_right pre hx

theorem SetTruncation.isPath {p : Walk D u v} {A B : Set V}
    (T : SetTruncation p A B) (hp : p.IsPath) : T.walk.IsPath := by
  exact T.support_sublist.nodup hp

end Walk

/-- A bundled finite directed path, with both endpoints retained as data. -/
structure FinitePath (D : Digraph V) where
  start : V
  finish : V
  walk : Walk D start finish
  isPath : walk.IsPath

namespace FinitePath

variable {D : Digraph V}

/-- The vertex set of a bundled finite path. -/
def support (p : FinitePath D) : Set V := {x | x ∈ p.walk.support}

@[simp] theorem start_mem_support (p : FinitePath D) : p.start ∈ p.support :=
  p.walk.start_mem_support

@[simp] theorem finish_mem_support (p : FinitePath D) : p.finish ∈ p.support :=
  p.walk.end_mem_support

theorem support_nonempty (p : FinitePath D) : p.support.Nonempty :=
  ⟨p.start, p.start_mem_support⟩

/-- Reverse a finite path and transpose its digraph. -/
def reverse (p : FinitePath D) : FinitePath (transpose D) where
  start := p.finish
  finish := p.start
  walk := p.walk.reverse
  isPath := p.isPath.reverse

@[simp] theorem support_reverse (p : FinitePath D) : p.reverse.support = p.support := by
  ext x
  simp [support, reverse]

end FinitePath

/-- An injective one-way infinite directed path. -/
@[ext]
structure Ray (D : Digraph V) where
  toFun : ℕ → V
  adj_succ : ∀ n, D.Adj (toFun n) (toFun (n + 1))
  injective : Injective toFun

namespace Ray

variable {D : Digraph V}

instance : CoeFun (Ray D) (fun _ ↦ ℕ → V) := ⟨Ray.toFun⟩

/-- The set of vertices of a ray. -/
def support (r : Ray D) : Set V := Set.range r.toFun

/-- The initial vertex of a ray. -/
def initial (r : Ray D) : V := r 0

@[simp] theorem initial_mem_support (r : Ray D) : r.initial ∈ r.support :=
  Set.mem_range_self 0

@[simp] theorem apply_mem_support (r : Ray D) (n : ℕ) : r n ∈ r.support :=
  Set.mem_range_self n

/-- Delete the first `k` vertices of a ray. -/
def tail (r : Ray D) (k : ℕ) : Ray D where
  toFun n := r (k + n)
  adj_succ n := by simpa [Nat.add_assoc] using r.adj_succ (k + n)
  injective := by
    intro m n h
    exact Nat.add_left_cancel (r.injective h)

@[simp] theorem tail_apply (r : Ray D) (k n : ℕ) : r.tail k n = r (k + n) := rfl

@[simp] theorem initial_tail (r : Ray D) (k : ℕ) : (r.tail k).initial = r k := by
  simp [initial]

theorem support_tail_subset (r : Ray D) (k : ℕ) : (r.tail k).support ⊆ r.support := by
  rintro x ⟨n, rfl⟩
  exact ⟨k + n, rfl⟩

@[simp] theorem tail_zero (r : Ray D) : r.tail 0 = r := by
  apply Ray.ext
  funext n
  simp

@[simp] theorem tail_tail (r : Ray D) (k l : ℕ) : (r.tail k).tail l = r.tail (k + l) := by
  apply Ray.ext
  funext n
  simp [Nat.add_assoc]

end Ray

/-- A directed path for a warp: either a finite simple path or a one-way ray. -/
abbrev Path (D : Digraph V) := FinitePath D ⊕ Ray D

namespace Path

variable {D : Digraph V}

/-- The support of a finite-or-infinite directed path. -/
def support : Path D → Set V
  | .inl p => p.support
  | .inr r => r.support

/-- The initial vertex of a finite-or-infinite directed path. -/
def initial : Path D → V
  | .inl p => p.start
  | .inr r => r.initial

@[simp] theorem initial_mem_support (p : Path D) : p.initial ∈ p.support := by
  rcases p with p | r
  · exact p.start_mem_support
  · exact r.initial_mem_support

theorem support_nonempty (p : Path D) : p.support.Nonempty :=
  ⟨p.initial, p.initial_mem_support⟩

end Path

end Erdos599.DirectedPath
