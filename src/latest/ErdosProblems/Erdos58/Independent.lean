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
import ErdosProblems.Erdos58.Basic
import ErdosProblems.Erdos58.Boundary
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-!
# Gyárfás's independent-exterior case

This file fixes a concrete interface for a designated longest odd cycle.  In
particular, its carrier is not an arbitrary set asserted to be a cycle: it is
the range of an injective graph homomorphism from `cycleGraph n`.

The final part of Gyárfás's Lemma 5 is also isolated here.  Once the cyclic
gap argument has shown that the longest cycle has `2 * j + 1` vertices and
that its exterior consists of exactly one vertex, the minimum-degree
hypothesis forces every possible edge.  Keeping this cardinal argument as a
separate theorem makes the remaining gap formalization independent of all
degree API bookkeeping.
-/

open Set
open scoped SimpleGraph

namespace Erdos58

noncomputable section

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- A particular longest odd cycle in `G`, represented by an actual copy of a
cycle graph.  `maximal` says maximal by length among *all* odd cycles of `G`.

The explicit copy is convenient in the independent-exterior argument: its
range gives a finite carrier with a canonical cyclic ordering. -/
structure LongestOddCycle (G : SimpleGraph V) where
  length : ℕ
  three_le : 3 ≤ length
  odd : Odd length
  copy : SimpleGraph.Copy (SimpleGraph.cycleGraph length) G
  maximal : ∀ {m : ℕ}, m ∈ oddCycleLengths G → m ≤ length

namespace LongestOddCycle

/-- The vertex set of the designated cycle. -/
def carrier (C : LongestOddCycle G) : Set V := Set.range C.copy

lemma finite_carrier (C : LongestOddCycle G) : C.carrier.Finite := by
  classical
  exact Set.finite_range C.copy

@[simp] lemma ncard_carrier (C : LongestOddCycle G) : C.carrier.ncard = C.length := by
  classical
  change (Set.range (fun x => C.copy x)).ncard = C.length
  simpa using Set.ncard_range_of_injective C.copy.injective

lemma length_mem_oddCycleLengths (C : LongestOddCycle G) :
    C.length ∈ oddCycleLengths G := by
  rw [mem_oddCycleLengths_iff_cycleGraph_isContained (G := G) C.three_le]
  exact ⟨C.odd, ⟨C.copy⟩⟩

lemma nonempty_carrier (C : LongestOddCycle G) : C.carrier.Nonempty := by
  have hpos : 0 < C.length := Nat.zero_lt_of_lt C.three_le
  let i : Fin C.length := ⟨0, hpos⟩
  exact ⟨C.copy i, ⟨i, rfl⟩⟩

/-- The designated copy with its source written in Mathlib's native
`m + 3` presentation.  Transporting the copy, rather than a dependent walk,
keeps all walk endpoints definitionally aligned. -/
def normalizedCopy (C : LongestOddCycle G) :
    SimpleGraph.Copy
      (SimpleGraph.cycleGraph (C.length - 3 + 3)) G :=
  (Nat.sub_add_cancel C.three_le).symm ▸ C.copy

private lemma cast_copy_apply {m n : ℕ} (h : m = n)
    (f : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G) (z : Fin m) :
    (h.symm ▸ f) z = f (Fin.cast h z) := by
  cases h
  rfl

@[simp] lemma normalizedCopy_apply (C : LongestOddCycle G)
    (z : Fin (C.length - 3 + 3)) :
    C.normalizedCopy z =
      C.copy (Fin.cast (Nat.sub_add_cancel C.three_le) z) := by
  exact cast_copy_apply (Nat.sub_add_cancel C.three_le) C.copy z

/-- The concrete closed walk obtained by mapping the canonical cycle through
the designated copy. -/
def walk (C : LongestOddCycle G) :
    G.Walk (C.normalizedCopy 0) (C.normalizedCopy 0) :=
  (SimpleGraph.cycleGraph.cycle (C.length - 3)).map C.normalizedCopy.toHom

@[simp] lemma walk_length (C : LongestOddCycle G) : C.walk.length = C.length := by
  simp [walk, Nat.sub_add_cancel C.three_le]

lemma walk_isCycle (C : LongestOddCycle G) : C.walk.IsCycle :=
  SimpleGraph.cycleGraph.isCycle_cycle.map C.normalizedCopy.injective

/-- Rebase the designated cycle at `x`, oriented so that the canonical
Mathlib walk proceeds from `x` to `x+1`, rather than from `0` downwards. -/
def rebaseCopy (C : LongestOddCycle G) (x : Fin C.length) :
    SimpleGraph.Copy (SimpleGraph.cycleGraph C.length) G := by
  letI : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  exact
    { toHom :=
        { toFun := fun z => C.copy (x - z)
          map_rel' := by
            intro a b hab
            apply C.copy.toHom.map_adj
            rw [SimpleGraph.cycleGraph_adj'] at hab ⊢
            rcases hab with hab | hab
            · right
              have heq : x - b - (x - a) = a - b := by abel
              rw [heq]
              exact hab
            · left
              have heq : x - a - (x - b) = b - a := by abel
              rw [heq]
              exact hab }
      injective' := by
        intro a b hab
        have hab' : x - a = x - b := C.copy.injective hab
        have h := congrArg (fun z => x - z) hab'
        have hxa : x - (x - a) = a := by abel
        have hxb : x - (x - b) = b := by abel
        rwa [hxa, hxb] at h }

@[simp] lemma rebaseCopy_apply (C : LongestOddCycle G)
    (x z : Fin C.length) :
    C.rebaseCopy x z = C.copy (x - z) := by
  unfold rebaseCopy
  rfl

/-- The same designated longest odd cycle, with its copy parametrization
rebased at `x`.  Length, parity, and maximality are unchanged. -/
def rebase (C : LongestOddCycle G) (x : Fin C.length) :
    LongestOddCycle G where
  length := C.length
  three_le := C.three_le
  odd := C.odd
  copy := C.rebaseCopy x
  maximal := C.maximal

@[simp] lemma rebase_length (C : LongestOddCycle G) (x : Fin C.length) :
    (C.rebase x).length = C.length := rfl

@[simp] lemma rebase_copy_apply (C : LongestOddCycle G)
    (x z : Fin C.length) :
    (C.rebase x).copy z = C.copy (x - z) := by
  change C.rebaseCopy x z = C.copy (x - z)
  exact C.rebaseCopy_apply x z

/-- Rebasing changes only the cyclic parametrization, not the underlying
set of vertices. -/
@[simp] lemma rebase_carrier (C : LongestOddCycle G) (x : Fin C.length) :
    (C.rebase x).carrier = C.carrier := by
  change Set.range (C.rebaseCopy x) = Set.range C.copy
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨x - z, (C.rebaseCopy_apply x z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨x - z, ?_⟩
    rw [C.rebaseCopy_apply]
    congr 1
    let : NeZero C.length :=
      ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
    abel

/-- The full designated rim, based at `x` and traversed in increasing
`Fin C.length` order. -/
def canonicalCycleWalk (n : ℕ) (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).Walk
      ⟨0, Nat.zero_lt_of_lt hn⟩ ⟨0, Nat.zero_lt_of_lt hn⟩ := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · exact SimpleGraph.cycleGraph.cycle n

@[simp] lemma canonicalCycleWalk_length (n : ℕ) (hn : 3 ≤ n) :
    (canonicalCycleWalk n hn).length = n := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · simp [canonicalCycleWalk]

lemma canonicalCycleWalk_isCycle (n : ℕ) (hn : 3 ≤ n) :
    (canonicalCycleWalk n hn).IsCycle := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · simpa [canonicalCycleWalk] using
      SimpleGraph.cycleGraph.isCycle_cycle (n := n)

lemma canonicalCycleWalk_getVert (n : ℕ) (hn : 3 ≤ n)
    (i : ℕ) (hi : i ≤ n) :
    (canonicalCycleWalk n hn).getVert i =
      ⟨(n - i) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt hn)⟩ := by
  obtain _ | _ | _ | n := n
  · omega
  · omega
  · omega
  · simpa [canonicalCycleWalk, Nat.add_assoc] using
      (SimpleGraph.cycleGraph.getVert_cycle (n := n) hi)

def rimWalkFrom (C : LongestOddCycle G) (x : Fin C.length) :
    G.Walk (C.copy x) (C.copy x) := by
  letI : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let q := (canonicalCycleWalk C.length C.three_le).map
    (C.rebaseCopy x).toHom
  exact q.copy (by change C.copy (x - 0) = C.copy x; simp)
    (by change C.copy (x - 0) = C.copy x; simp)

@[simp] lemma rimWalkFrom_length (C : LongestOddCycle G)
    (x : Fin C.length) : (C.rimWalkFrom x).length = C.length := by
  simp [rimWalkFrom]

lemma rimWalkFrom_isCycle (C : LongestOddCycle G) (x : Fin C.length) :
    (C.rimWalkFrom x).IsCycle := by
  rw [rimWalkFrom]
  simpa only [SimpleGraph.Walk.isCycle_copy] using
    (canonicalCycleWalk_isCycle C.length C.three_le).map
      (C.rebaseCopy x).injective

lemma rimWalkFrom_getVert (C : LongestOddCycle G) (x : Fin C.length)
    (i : ℕ) (hi : i ≤ C.length) :
    (C.rimWalkFrom x).getVert i =
      C.copy (x + ⟨i % C.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩) := by
  rw [rimWalkFrom]
  simp only [SimpleGraph.Walk.getVert_copy]
  rw [SimpleGraph.Walk.getVert_map]
  simp only [rebaseCopy]
  rw [canonicalCycleWalk_getVert C.length C.three_le i hi]
  change C.copy
      (x - ⟨(C.length - i) % C.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩) =
    C.copy (x + ⟨i % C.length,
      Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩)
  congr 1
  let : NeZero C.length :=
    ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
  let a : Fin C.length := ⟨i % C.length,
    Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩
  have hz : (⟨(C.length - i) % C.length,
      Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩ : Fin C.length) = -a := by
    by_cases hieq : i = C.length
    · subst i
      apply Fin.ext
      simp [a]
    · have hilt : i < C.length := lt_of_le_of_ne hi hieq
      by_cases hi0 : i = 0
      · subst i
        apply Fin.ext
        simp [a]
      · have hsub : C.length - i < C.length :=
          Nat.sub_lt (Nat.zero_lt_of_lt C.three_le) (Nat.zero_lt_of_ne_zero hi0)
        apply Fin.ext
        simp [a, Fin.val_neg, Nat.mod_eq_of_lt hilt,
          Nat.mod_eq_of_lt hsub, hi0]
  change x - _ = x + a
  rw [hz]
  abel

/-- The rebased rim visits exactly the original designated carrier.  This
is the support equality used to transport exterior constructions across a
change of cyclic origin. -/
lemma rimWalkFrom_support (C : LongestOddCycle G) (x : Fin C.length) :
    {v | v ∈ (C.rimWalkFrom x).support} = C.carrier := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hiv, hi⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hv
    have hiC : i ≤ C.length := by simpa using hi
    refine ⟨x + ⟨i % C.length,
      Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩, ?_⟩
    calc
      C.copy (x + ⟨i % C.length,
        Nat.mod_lt _ (Nat.zero_lt_of_lt C.three_le)⟩) =
          (C.rimWalkFrom x).getVert i :=
            (C.rimWalkFrom_getVert x i hiC).symm
      _ = v := hiv
  · rintro ⟨z, rfl⟩
    let d := (z - x).val
    have hdlt : d < C.length := (z - x).isLt
    have hget : (C.rimWalkFrom x).getVert d = C.copy z := by
      rw [C.rimWalkFrom_getVert x d hdlt.le]
      congr 1
      let : NeZero C.length :=
        ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
      have hz : (⟨d % C.length, Nat.mod_lt _
          (Nat.zero_lt_of_lt C.three_le)⟩ : Fin C.length) = z - x := by
        apply Fin.ext
        simp [d, Nat.mod_eq_of_lt hdlt]
      rw [hz]
      abel
    rw [← hget]
    exact SimpleGraph.Walk.getVert_mem_support _ _

/-- A chord whose two rim arcs both contain at least two edges closes either
arc into a genuine simple cycle.  This is the exact geometric constructor
needed in the empty-exterior branch of the cyclic-gap argument. -/
theorem chordArc_cycleAtLength [Finite V] (C : LongestOddCycle G)
    {x y : Fin C.length} (hxy : y ≠ x)
    (hchord : G.Adj (C.copy x) (C.copy y))
    (hforward : 2 ≤ (y - x).val) (hreverse : 2 ≤ (x - y).val) :
    CycleAtLength G ((y - x).val + 1) := by
  let d := (y - x).val
  have hdlt : d < C.length := (y - x).isLt
  let p := (C.rimWalkFrom x).take d
  have hpPath : p.IsPath :=
    (C.rimWalkFrom_isCycle x).isPath_take (by simpa [d] using hdlt)
  have hpEnd : (C.rimWalkFrom x).getVert d = C.copy y := by
    rw [C.rimWalkFrom_getVert x d hdlt.le]
    congr 1
    let : NeZero C.length :=
      ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt C.three_le)⟩
    have hz : (⟨d % C.length, Nat.mod_lt _
        (Nat.zero_lt_of_lt C.three_le)⟩ : Fin C.length) = y - x := by
      apply Fin.ext
      simp [d, Nat.mod_eq_of_lt hdlt]
    rw [hz]
    abel
  let p' : G.Walk (C.copy x) (C.copy y) := p.copy rfl hpEnd
  have hp'Path : p'.IsPath := by simpa [p'] using hpPath
  let q : G.Walk (C.copy x) (C.copy x) :=
    SimpleGraph.Walk.cons hchord p'.reverse
  refine ⟨C.copy x, q, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa [q] using hp'Path.reverse
    · simp [q, p', p, d, hdlt.le]
      omega
  · simp [q, p', p, d, hdlt.le]


end LongestOddCycle

/-- The exact graph-theoretic hypothesis that the vertices off the designated
cycle form an independent set. -/
def HasIndependentExterior (C : LongestOddCycle G) : Prop :=
  G.IsIndepSet C.carrierᶜ

@[simp] lemma hasIndependentExterior_rebase (C : LongestOddCycle G)
    (x : Fin C.length) :
    HasIndependentExterior (C.rebase x) ↔ HasIndependentExterior C := by
  simp [HasIndependentExterior]

/-- The output of the cyclic-gap portion of Gyárfás's Lemma 5.

For a graph of minimum degree at least `2*j+1` whose longest odd cycle has an
independent exterior and which has only `j` odd cycle lengths, the gap
argument proves these three assertions: the cycle has length `2*j+1`, there
is a vertex outside it, and there cannot be two such vertices.  They are
packaged to give the gap proof a small, typed target. -/
structure IndependentExteriorRigidity (j : ℕ) (C : LongestOddCycle G) : Prop where
  length_eq : C.length = 2 * j + 1
  exterior_nonempty : C.carrierᶜ.Nonempty
  exterior_subsingleton : C.carrierᶜ.Subsingleton

namespace IndependentExteriorRigidity

lemma ncard_exterior_eq_one {j : ℕ} {C : LongestOddCycle G}
    (h : IndependentExteriorRigidity j C) : C.carrierᶜ.ncard = 1 := by
  obtain ⟨x, hx⟩ := h.exterior_nonempty
  have heq : C.carrierᶜ = {x} := by
    ext y
    constructor
    · intro hy
      simp [h.exterior_subsingleton hy hx]
    · intro hy
      have hyx : y = x := by simpa using hy
      simpa [hyx] using hx
  simp [heq]

lemma card_vertex_eq {j : ℕ} {C : LongestOddCycle G}
    [Fintype V] (h : IndependentExteriorRigidity j C) :
    Fintype.card V = 2 * j + 2 := by
  classical
  have hsplit : C.carrier.ncard + C.carrierᶜ.ncard = Fintype.card V := by
    simpa using Set.ncard_add_ncard_compl C.carrier
  rw [C.ncard_carrier, h.length_eq, h.ncard_exterior_eq_one] at hsplit
  omega

end IndependentExteriorRigidity

/-- Once the gap argument has established `|C| = 2*j+1`, every exterior
vertex is adjacent to every vertex of `C`.  Indeed all its neighbors lie on
`C` (the exterior is independent), while the lower degree bound already
equals the cardinality of `C`. -/
lemma exterior_complete_to_cycle [Fintype V] [DecidableRel G.Adj]
    {j : ℕ} {C : LongestOddCycle G}
    (hind : HasIndependentExterior C)
    (hlength : C.length = 2 * j + 1)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    {t : V} (ht : t ∈ C.carrierᶜ) :
    ∀ {c : V}, c ∈ C.carrier → G.Adj t c := by
  classical
  have hsubset : G.neighborFinset t ⊆ C.finite_carrier.toFinset := by
    intro x hx
    have hadj : G.Adj t x :=
      (SimpleGraph.mem_neighborFinset (G := G) (v := t) x).mp hx
    have hxC : x ∈ C.carrier := by
      by_contra hxC
      exact hind ht hxC (G.ne_of_adj hadj) hadj
    simpa using hxC
  have hcard_le : C.finite_carrier.toFinset.card ≤ (G.neighborFinset t).card := by
    rw [← Set.ncard_eq_toFinset_card C.carrier C.finite_carrier,
      SimpleGraph.card_neighborFinset_eq_degree,
      C.ncard_carrier, hlength]
    exact hdegree t
  have heq : G.neighborFinset t = C.finite_carrier.toFinset :=
    Finset.eq_of_subset_of_card_le hsubset hcard_le
  intro c hc
  exact (SimpleGraph.mem_neighborFinset (G := G) (v := t) c).mp (by
    rw [heq]
    simpa using hc)

/-- At the extremal cycle length `2*j+1`, the degree bound itself guarantees
that at least one vertex lies outside the cycle. -/
lemma exterior_nonempty_of_cycle_length [Fintype V] [DecidableRel G.Adj]
    {j : ℕ} {C : LongestOddCycle G}
    (hlength : C.length = 2 * j + 1)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v) :
    C.carrierᶜ.Nonempty := by
  classical
  let c : V := C.nonempty_carrier.some
  have hcard : 2 * j + 1 < Fintype.card V :=
    (hdegree c).trans_lt (G.degree_lt_card_verts c)
  rw [← Set.ncard_pos]
  rw [Set.ncard_compl C.carrier, Nat.card_eq_fintype_card,
    C.ncard_carrier, hlength]
  omega

/-- A cycle cut open immediately after one distinguished vertex.

For the canonical copy of a cycle graph such a certificate is obtained by
deleting the distinguished vertex and the two incident cycle edges.  Its
path has `C.length - 1` vertices and hence `C.length - 2` edges.  This small
interface avoids committing the later graph proof to a particular normal
form for `Fin`-indexed walks. -/
structure CycleCutPath (C : LongestOddCycle G) where
  cut : V
  start : V
  finish : V
  walk : G.Walk start finish
  isPath : walk.IsPath
  support_subset : ∀ {v : V}, v ∈ walk.support → v ∈ C.carrier
  cut_mem : cut ∈ C.carrier
  cut_notMem_support : cut ∉ walk.support
  length_add_two : walk.length + 2 = C.length

/-- Every designated cycle copy has a canonical cut-open path: remove the
base vertex from the mapped canonical cycle, together with the two incident
edges. -/
def LongestOddCycle.cutPath (C : LongestOddCycle G) : CycleCutPath C := by
  let p := C.walk
  let q := p.tail.dropLast
  have hp_cycle : p.IsCycle := by simpa [p] using C.walk_isCycle
  have hp_notNil : ¬p.Nil := hp_cycle.not_nil
  have hp_length : p.length = C.length := by simp [p]
  have htail_notNil : ¬p.tail.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    have hpositive : 0 < C.length - 1 := by
      have := C.three_le
      omega
    simpa [SimpleGraph.Walk.length_tail, hp_length] using hpositive
  have hq_support : q.support = p.support.tail.dropLast := by
    rw [show q.support = p.tail.dropLast.support by rfl,
      SimpleGraph.Walk.support_dropLast htail_notNil,
      SimpleGraph.Walk.support_tail_of_not_nil p hp_notNil]
  refine {
    cut := C.normalizedCopy 0
    start := p.snd
    finish := p.tail.penultimate
    walk := q
    isPath := hp_cycle.isPath_tail.dropLast
    support_subset := ?_
    cut_mem := ⟨Fin.cast (Nat.sub_add_cancel C.three_le) 0, by simp⟩
    cut_notMem_support := ?_
    length_add_two := ?_ }
  · intro v hv
    have hvp : v ∈ p.support := by
      rw [hq_support] at hv
      exact List.mem_of_mem_tail (List.mem_of_mem_dropLast hv)
    simp only [p, LongestOddCycle.walk,
      SimpleGraph.Walk.support_map] at hvp
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hvp
    exact ⟨Fin.cast (Nat.sub_add_cancel C.three_le) z, by simp⟩
  · intro hcut
    rw [hq_support] at hcut
    have hne := hp_cycle.support_nodup.rel_dropLast_getLast hcut
    apply hne
    simpa only [SimpleGraph.Walk.support_tail_of_not_nil p hp_notNil] using
      (SimpleGraph.Walk.getLast_support p.tail).symm
  · simp [q, p, SimpleGraph.Walk.length_tail, hp_length]
    have := C.three_le
    omega

/-- Two different exterior vertices, both complete to a cut-open longest odd
cycle, create an odd cycle two edges longer than the designated cycle. -/
lemma exterior_subsingleton_of_cutPath [Fintype V] [DecidableRel G.Adj]
    {j : ℕ} {C : LongestOddCycle G}
    (hind : HasIndependentExterior C)
    (hlength : C.length = 2 * j + 1)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (P : CycleCutPath C) : C.carrierᶜ.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hcomplete_x : ∀ {c : V}, c ∈ C.carrier → G.Adj x c :=
    exterior_complete_to_cycle (C := C) hind hlength hdegree (t := x) hx
  have hcomplete_y : ∀ {c : V}, c ∈ C.carrier → G.Adj y c :=
    exterior_complete_to_cycle (C := C) hind hlength hdegree (t := y) hy
  have hxa : G.Adj x P.cut := hcomplete_x P.cut_mem
  have hay : G.Adj P.cut y := (hcomplete_y P.cut_mem).symm
  have hstart_mem : P.start ∈ C.carrier :=
    P.support_subset P.walk.start_mem_support
  have hfinish_mem : P.finish ∈ C.carrier :=
    P.support_subset P.walk.end_mem_support
  have hys : G.Adj y P.start := hcomplete_y hstart_mem
  have hfx : G.Adj P.finish x := (hcomplete_x hfinish_mem).symm
  have hx_notMem : x ∉ P.walk.support := fun h ↦ hx (P.support_subset h)
  have hy_notMem : y ∉ P.walk.support := fun h ↦ hy (P.support_subset h)
  have hcut_ne_x : P.cut ≠ x := fun h ↦ hx (h ▸ P.cut_mem)
  have hcut_ne_y : P.cut ≠ y := fun h ↦ hy (h ▸ P.cut_mem)
  let r : G.Walk P.start x := P.walk.concat hfx
  have hr_path : r.IsPath := P.isPath.concat hx_notMem hfx
  have hy_notMem_r : y ∉ r.support := by
    simp [r, SimpleGraph.Walk.support_concat, hy_notMem, Ne.symm hxy]
  let s : G.Walk y x := SimpleGraph.Walk.cons hys r
  have hs_path : s.IsPath := hr_path.cons hy_notMem_r
  have hcut_notMem_r : P.cut ∉ r.support := by
    simp [r, SimpleGraph.Walk.support_concat, P.cut_notMem_support, hcut_ne_x]
  have hcut_notMem_s : P.cut ∉ s.support := by
    simp [s, hcut_ne_y, hcut_notMem_r]
  let tail : G.Walk P.cut x := SimpleGraph.Walk.cons hay s
  have htail_path : tail.IsPath := hs_path.cons hcut_notMem_s
  let q : G.Walk x x := SimpleGraph.Walk.cons hxa tail
  have hq_length : q.length = C.length + 2 := by
    have hP_length := P.length_add_two
    simp [q, tail, s, r]
    omega
  have hq_cycle : q.IsCycle := by
    rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
    constructor
    · simpa [q] using htail_path
    · rw [hq_length]
      omega
  have hq_odd : Odd q.length := by
    obtain ⟨a, ha⟩ := C.odd
    refine ⟨a + 1, ?_⟩
    rw [hq_length]
    omega
  have hq_mem : q.length ∈ oddCycleLengths G :=
    ⟨hq_odd, x, q, hq_cycle, rfl⟩
  have := C.maximal hq_mem
  omega

/-- Assemble the exact rigidity record once the cyclic-gap calculation has
identified the extremal length and the canonical cycle has been cut open. -/
theorem independentExteriorRigidity_of_length_and_cutPath
    [Fintype V] [DecidableRel G.Adj]
    {j : ℕ} {C : LongestOddCycle G}
    (hind : HasIndependentExterior C)
    (hlength : C.length = 2 * j + 1)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (P : CycleCutPath C) : IndependentExteriorRigidity j C := by
  exact ⟨hlength, exterior_nonempty_of_cycle_length hlength hdegree,
    exterior_subsingleton_of_cutPath hind hlength hdegree P⟩

/-- Once the cyclic-gap calculation has supplied the cycle length, no
additional path certificate is needed: the designated copy itself provides
the canonical cut-open path. -/
theorem independentExteriorRigidity_of_length
    [Fintype V] [DecidableRel G.Adj]
    {j : ℕ} {C : LongestOddCycle G}
    (hind : HasIndependentExterior C)
    (hlength : C.length = 2 * j + 1)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v) :
    IndependentExteriorRigidity j C :=
  independentExteriorRigidity_of_length_and_cutPath
    hind hlength hdegree C.cutPath

/-- A simple graph on at most `d+1` vertices in which every vertex has degree
at least `d` is complete when the bound is tight enough to cover all other
vertices.  This is the finite cardinal endpoint of Gyárfás's Lemma 5. -/
theorem eq_top_of_card_le_degree_add_one [Fintype V] [DecidableRel G.Adj]
    {d : ℕ} (hcard : Fintype.card V ≤ d + 1)
    (hdegree : ∀ v : V, d ≤ G.degree v) : G = ⊤ := by
  classical
  apply le_antisymm le_top
  intro v w hvw
  have hvw' : v ≠ w := by simpa using hvw
  have hdle : d ≤ G.degree v := hdegree v
  have hdeg_lt : G.degree v < Fintype.card V := G.degree_lt_card_verts v
  have hcard_eq : Fintype.card V = d + 1 := by omega
  have hdeg_eq_d : G.degree v = d := by omega
  have hdeg_eq : G.degree v = Fintype.card V - 1 := by
    rw [hcard_eq, hdeg_eq_d]
    omega
  exact ((G.degree_eq_card_sub_one v).mp hdeg_eq) hvw'

/-- The checked final implication of the independent-exterior case.

The hypotheses in `IndependentExteriorRigidity` are exactly the conclusions
of the preceding cyclic-gap analysis, not a reformulation of completeness.
Together with the original minimum-degree bound they force `G` to be the
complete graph on `2*j+2` vertices. -/
theorem independent_exterior_forces_complete_of_rigidity
    [Fintype V] [DecidableRel G.Adj] {j : ℕ} {C : LongestOddCycle G}
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v)
    (hrigid : IndependentExteriorRigidity j C) :
    G = SimpleGraph.completeGraph V := by
  rw [SimpleGraph.completeGraph_eq_top]
  apply eq_top_of_card_le_degree_add_one
  · rw [hrigid.card_vertex_eq]
  · exact hdegree

/-- Certificate-free endpoint of Gyárfás's independent-exterior case.  The
only input still delegated to the cyclic-gap calculation is the sharp
identity `C.length = 2*j+1`. -/
theorem independent_exterior_forces_complete_of_length
    [Fintype V] [DecidableRel G.Adj] {j : ℕ} {C : LongestOddCycle G}
    (hind : HasIndependentExterior C)
    (hlength : C.length = 2 * j + 1)
    (hdegree : ∀ v : V, 2 * j + 1 ≤ G.degree v) :
    G = SimpleGraph.completeGraph V :=
  independent_exterior_forces_complete_of_rigidity hdegree
    (independentExteriorRigidity_of_length hind hlength hdegree)

end

end Erdos58
