/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.HullOrder
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Gift-wrapping interface for the planar convex hull

The geometric part of a gift-wrapping proof naturally produces a successor
permutation of the hull vertices.  This file proves that it is enough to show
that this permutation is one cycle and to verify the supporting-edge and turn
conditions locally.  The conversion to a `Fin h`-indexed cyclic enumeration
is then completely finite and contains no planar geometry.

The definitions in the first section are deliberately local copies of the
small interface in `_scratch/Erdos957HullOrder.lean`; this lets the finite
orbit construction be checked independently while that geometric scratch
module is under development.
-/

open Set
open scoped EuclideanGeometry

namespace Erdos957

noncomputable section

/-- Number of extreme points of the finite convex hull. -/
abbrev chainHullVertexCount (A : Finset Point) : ℕ := (hullVertices A).card

/-- Signed twice-area of an oriented triangle. -/
def chainOrientedTurn (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - q 1) - (q 1 - p 1) * (r 0 - q 0)

/-- The local supporting-edge property needed by the hull-cycle consumer. -/
def IsStrictChainEdge (A : Finset Point) (p q : Point) : Prop :=
  p ≠ q ∧
    ∃ l : Point →L[ℝ] ℝ, l ≠ 0 ∧ l p = l q ∧
      (∀ x ∈ A, l x ≤ l p) ∧
      (∀ x ∈ hullVertices A, x ≠ p → x ≠ q → l x < l p)

/-- A `Fin h`-indexed cyclic hull interface, independent of how the order was
constructed. -/
structure ChainCyclicHullOrder (A : Finset Point) where
  vertex : Fin (chainHullVertexCount A) ↪ Point
  range_vertex : Set.range vertex = (hullVertices A : Set Point)
  edge_support : ∀ i,
    IsStrictChainEdge A (vertex i) (vertex (finRotate _ i))
  strict_turn : ∀ i,
    0 < chainOrientedTurn (vertex i) (vertex (finRotate _ i))
      (vertex (finRotate _ (finRotate _ i)))

@[simp]
theorem chainOrientedTurn_eq_orientedTurn (p q r : Point) :
    chainOrientedTurn p q r = orientedTurn p q r :=
  rfl

theorem isStrictChainEdge_iff_isStrictSupportingEdge
    (A : Finset Point) (p q : Point) :
    IsStrictChainEdge A p q ↔ IsStrictSupportingEdge A p q :=
  Iff.rfl

namespace ChainCyclicHullOrder

variable {A : Finset Point}

/-- Forget the standalone names and obtain the exact cyclic-hull API used by
the rest of the Erdős 957 development. -/
def toCyclicHullOrder (P : ChainCyclicHullOrder A) : CyclicHullOrder A where
  vertex := P.vertex
  range_vertex := P.range_vertex
  edge_support i :=
    (isStrictChainEdge_iff_isStrictSupportingEdge A _ _).mp (P.edge_support i)
  strict_turn i := by
    simpa using P.strict_turn i

end ChainCyclicHullOrder

/-- Local data produced by a gift-wrapping construction.  In contrast to a
global indexed polygon, the geometric obligations are stated at an arbitrary
hull vertex and its first two successors.

`isCycle` is stated as `IsCycleOn univ`, rather than `IsCycle`, so the finite
orbit lemmas also cover the formal singleton case.  The edge and strict-turn
fields themselves force the geometrically relevant case to have at least
three vertices. -/
structure GiftWrapCycle (A : Finset Point) where
  next : Equiv.Perm {x // x ∈ hullVertices A}
  start : {x // x ∈ hullVertices A}
  isCycle : next.IsCycleOn (Finset.univ : Finset {x // x ∈ hullVertices A})
  edge_support : ∀ p,
    IsStrictChainEdge A p.1 (next p).1
  strict_turn : ∀ p,
    0 < chainOrientedTurn p.1 (next p).1 (next (next p)).1

namespace GiftWrapCycle

variable {A : Finset Point} (W : GiftWrapCycle A)

include W

/-- The local edge and turn conditions rule out the degenerate one- and
two-vertex cases.  This is why the gift-wrapping certificate carries a
starting vertex explicitly. -/
theorem three_le_chainHullVertexCount : 3 ≤ chainHullVertexCount A := by
  let p := W.start
  let q := W.next p
  let r := W.next q
  have hpq : p.1 ≠ q.1 := (W.edge_support p).1
  have hqr : q.1 ≠ r.1 := (W.edge_support q).1
  have hpr : p.1 ≠ r.1 := by
    intro h
    have ht := W.strict_turn p
    change 0 < chainOrientedTurn p.1 q.1 r.1 at ht
    rw [← h] at ht
    simp only [chainOrientedTurn] at ht
    nlinarith
  have hsub : ({p.1, q.1, r.1} : Finset Point) ⊆ hullVertices A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact p.2
    · exact q.2
    · exact r.2
  have hcard := Finset.card_le_card hsub
  simpa [chainHullVertexCount, hpq, hpr, hqr] using hcard

/-- The orbit of the chosen starting point, indexed before wrap-around. -/
def orbitVertex (i : Fin (chainHullVertexCount A)) : Point :=
  ((W.next ^ i.1) W.start).1

/-- Distinct indices before the first wrap-around give distinct hull
vertices.  This is exactly the finite-cycle congruence theorem from Mathlib. -/
theorem orbitVertex_injective : Function.Injective W.orbitVertex := by
  intro i j hij
  apply Fin.ext
  have hpowers : (W.next ^ i.1) W.start = (W.next ^ j.1) W.start :=
    Subtype.ext hij
  have hmod : i.1 ≡ j.1 [MOD chainHullVertexCount A] := by
    simpa [chainHullVertexCount] using
      (W.isCycle.pow_apply_eq_pow_apply (Finset.mem_univ W.start)).mp hpowers
  simpa [Nat.ModEq, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] using hmod

/-- The orbit as an embedding into the plane. -/
def orbitEmbedding : Fin (chainHullVertexCount A) ↪ Point :=
  ⟨W.orbitVertex, W.orbitVertex_injective⟩

@[simp]
theorem orbitVertex_mem_hullVertices (i : Fin (chainHullVertexCount A)) :
    W.orbitVertex i ∈ hullVertices A :=
  ((W.next ^ i.1) W.start).2

/-- Every hull vertex occurs in the finite initial orbit. -/
theorem range_orbitVertex :
    Set.range W.orbitVertex = (hullVertices A : Set Point) := by
  apply Set.Subset.antisymm
  · rintro x ⟨i, rfl⟩
    exact W.orbitVertex_mem_hullVertices i
  · intro x hx
    let y : {x // x ∈ hullVertices A} := ⟨x, hx⟩
    obtain ⟨n, hnlt, hn⟩ := W.isCycle.exists_pow_eq
      (Finset.mem_univ W.start) (Finset.mem_univ y)
    have hnlt' : n < chainHullVertexCount A := by
      simpa [chainHullVertexCount] using hnlt
    refine ⟨⟨n, hnlt'⟩, ?_⟩
    exact congrArg Subtype.val hn

/-- Advancing the cyclic index is the same operation as applying the
gift-wrapping successor. -/
theorem orbitVertex_finRotate (i : Fin (chainHullVertexCount A)) :
    W.orbitVertex (finRotate _ i) = (W.next ((W.next ^ i.1) W.start)).1 := by
  have := i.neZero
  have hmod : (finRotate _ i).1 ≡ i.1 + 1 [MOD chainHullVertexCount A] := by
    rw [finRotate_apply]
    simp [Nat.ModEq, Fin.add_def, chainHullVertexCount]
  have hpowers :
      (W.next ^ (finRotate _ i).1) W.start =
        (W.next ^ (i.1 + 1)) W.start :=
    (W.isCycle.pow_apply_eq_pow_apply (Finset.mem_univ W.start)).2 (by
      simpa [chainHullVertexCount] using hmod)
  change ((W.next ^ (finRotate _ i).1) W.start).1 = _
  rw [hpowers, pow_succ']
  rfl

/-- Applying cyclic successor twice agrees with applying `next` twice. -/
theorem orbitVertex_finRotate_finRotate (i : Fin (chainHullVertexCount A)) :
    W.orbitVertex (finRotate _ (finRotate _ i)) =
      (W.next (W.next ((W.next ^ i.1) W.start))).1 := by
  rw [W.orbitVertex_finRotate (finRotate _ i)]
  have hstep :
      (W.next ^ (finRotate _ i).1) W.start =
        W.next ((W.next ^ i.1) W.start) :=
    Subtype.ext (W.orbitVertex_finRotate i)
  rw [hstep]

/-- A one-cycle gift-wrapping successor canonically supplies the global
`Fin h`-indexed cyclic hull order. -/
def toChainCyclicHullOrder : ChainCyclicHullOrder A where
  vertex := W.orbitEmbedding
  range_vertex := W.range_orbitVertex
  edge_support i := by
    change IsStrictChainEdge A (W.orbitVertex i)
      (W.orbitVertex (finRotate _ i))
    rw [W.orbitVertex_finRotate i]
    exact W.edge_support ((W.next ^ i.1) W.start)
  strict_turn i := by
    change 0 < chainOrientedTurn (W.orbitVertex i)
      (W.orbitVertex (finRotate _ i))
      (W.orbitVertex (finRotate _ (finRotate _ i)))
    rw [W.orbitVertex_finRotate i, W.orbitVertex_finRotate_finRotate i]
    exact W.strict_turn ((W.next ^ i.1) W.start)

/-- The final bridge from local gift-wrapping data to the shared cyclic hull
order interface. -/
def toCyclicHullOrder : CyclicHullOrder A :=
  W.toChainCyclicHullOrder.toCyclicHullOrder

end GiftWrapCycle

end

end Erdos957
