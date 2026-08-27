/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveBlockSampling

/-!
# Reserve wedges for the internal-edge cover step

For a fixed edge `uv` outside the next vortex set, a candidate third vertex
`w` inside that set needs the two crossing reserve edges `uw` and `vw`.
Different third vertices use disjoint two-edge blocks.  This file verifies
that geometry and specializes the disjoint-block concentration theorem to
the exact candidate supply in KSSS Section 10.2.1.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The two reserve edges needed to attach `w` to the fixed pair `u,v`. -/
def reserveWedgeBlock
    {V : Type*} [DecidableEq V] (u v w : V) : Finset (Sym2 V) :=
  {s(u, w), s(v, w)}

lemma card_reserveWedgeBlock
    {V : Type*} [DecidableEq V] {u v w : V} (huv : u ≠ v) :
    (reserveWedgeBlock u v w).card = 2 := by
  rw [reserveWedgeBlock, card_insert_of_notMem]
  · simp
  · simp only [mem_singleton, Sym2.eq_iff]
    aesop

lemma reserveWedgeBlock_disjoint
    {V : Type*} [DecidableEq V] {u v w x : V}
    (huv : u ≠ v) (hux : u ≠ x) (hvx : v ≠ x) (hwx : w ≠ x) :
    Disjoint (reserveWedgeBlock u v w) (reserveWedgeBlock u v x) := by
  rw [Finset.disjoint_left]
  intro e hew hex
  simp only [reserveWedgeBlock, mem_insert, mem_singleton] at hew hex
  rcases hew with rfl | rfl <;> rcases hex with h | h <;>
    simp only [Sym2.eq_iff] at h <;> aesop

lemma crossingEdge_mk_of_outside_inside
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {u w : V}
    (hu : u ∉ U) (hw : w ∈ U) (huw : G.Adj u w) :
    s(u, w) ∈ crossingEdges G U := by
  rw [mem_crossingEdges_iff]
  refine ⟨huw, ?_⟩
  constructor
  · exact ⟨w, by simp [Sym2.mem_iff, hw]⟩
  · exact ⟨u, by simp [Sym2.mem_iff, hu]⟩

lemma reserveWedgeBlock_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {u v w : V}
    (hu : u ∉ U) (hv : v ∉ U) (hw : w ∈ U)
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    reserveWedgeBlock u v w ⊆ crossingEdges G U := by
  intro e he
  simp only [reserveWedgeBlock, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact crossingEdge_mk_of_outside_inside hu hw huw
  · exact crossingEdge_mk_of_outside_inside hv hw hvw

/-- Candidate vertices whose two wedge edges were retained in the reserve. -/
noncomputable def activeReserveWedgeVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (u v : V)
    (ω : Sym2 V → Bool) : Finset V := by
  classical
  exact S.filter fun w ↦
    reserveWedgeBlock u v w ⊆ reserveEdges G U ω

@[simp]
lemma mem_activeReserveWedgeVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U S : Finset V} {u v w : V}
    {ω : Sym2 V → Bool} :
    w ∈ activeReserveWedgeVertices G U S u v ω ↔
      w ∈ S ∧ reserveWedgeBlock u v w ⊆ reserveEdges G U ω := by
  classical
  simp [activeReserveWedgeVertices]

lemma activeReserveWedgeVertices_eq_activeBlocks
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U S : Finset V} {u v : V}
    {ω : Sym2 V → Bool}
    (hcross : ∀ w ∈ S,
      reserveWedgeBlock u v w ⊆ crossingEdges G U) :
    activeReserveWedgeVertices G U S u v ω =
      activeBlocks (reserveWedgeBlock u v) S ω := by
  ext w
  rw [mem_activeReserveWedgeVertices_iff, mem_activeBlocks_iff]
  constructor
  · rintro ⟨hwS, hwsub⟩
    refine ⟨hwS, ?_⟩
    intro e he
    exact (mem_reserveEdges_iff.mp (hwsub he)).2
  · rintro ⟨hwS, hwactive⟩
    refine ⟨hwS, ?_⟩
    intro e he
    exact mem_reserveEdges_iff.mpr ⟨hcross w hwS he, hwactive e he⟩

/-- If every crossing edge is reserved, every geometrically valid wedge
candidate is active. -/
lemma activeReserveWedgeVertices_eq_of_reserveEdges_eq_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U S : Finset V} {u v : V}
    {ω : Sym2 V → Bool}
    (hcross : ∀ w ∈ S,
      reserveWedgeBlock u v w ⊆ crossingEdges G U)
    (hfull : reserveEdges G U ω = crossingEdges G U) :
    activeReserveWedgeVertices G U S u v ω = S := by
  ext w
  rw [mem_activeReserveWedgeVertices_iff]
  constructor
  · exact fun hw ↦ hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    rw [hfull]
    exact hcross w hw

/-- Exact lower-tail union bound for the number of reserve-supported
candidate triangles through a fixed internal edge. -/
theorem reserveEdgeLaw_probability_activeReserveWedgeVertices_card_le_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (u v : V)
    (r : ℝ≥0) (hr : r ≤ 1)
    (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (hSU : S ⊆ U)
    (hadj : ∀ w ∈ S, G.Adj u w ∧ G.Adj v w)
    (k : ℕ) :
    (reserveEdgeLaw G U r hr).probability
        (fun ω ↦
          (activeReserveWedgeVertices G U S u v ω).card ≤ k) ≤
      (Nat.choose S.card (S.card - k) : ℝ≥0) *
        (1 - r ^ 2) ^ (S.card - k) := by
  let blocks : V → Finset (Sym2 V) := reserveWedgeBlock u v
  have hcross : ∀ w ∈ S, blocks w ⊆ crossingEdges G U := by
    intro w hw
    exact reserveWedgeBlock_subset_crossingEdges hu hv (hSU hw)
      (hadj w hw).1 (hadj w hw).2
  have hpair : (S : Set V).PairwiseDisjoint blocks := by
    intro w hw x hx hwx
    apply reserveWedgeBlock_disjoint huv
    · intro hux
      subst x
      exact hu (hSU hx)
    · intro hvx
      subst x
      exact hv (hSU hx)
    · exact hwx
  have hcard : ∀ w ∈ S, (blocks w).card = 2 := by
    intro w _hw
    exact card_reserveWedgeBlock huv
  have htail := reserveEdgeLaw_probability_activeBlocks_card_le_le
    G U r hr blocks S hcross hpair 2 k hcard
  simpa only [blocks, activeReserveWedgeVertices_eq_activeBlocks hcross] using htail

/-- Exponential version of the reserve-wedge lower tail.  This is the form
used when the reserve density tends to zero with the ambient order. -/
theorem reserveEdgeLaw_probability_activeReserveWedgeVertices_card_le_le_exp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U S : Finset V) (u v : V)
    (r : ℝ≥0) (hr : r ≤ 1)
    (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (hSU : S ⊆ U)
    (hadj : ∀ w ∈ S, G.Adj u w ∧ G.Adj v w)
    (k : ℕ)
    (hk : (k : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * S.card / 4) :
    ((reserveEdgeLaw G U r hr).probability
        (fun ω ↦
          (activeReserveWedgeVertices G U S u v ω).card ≤ k) : ℝ) ≤
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * S.card) / 4) := by
  let blocks : V → Finset (Sym2 V) := reserveWedgeBlock u v
  have hcross : ∀ w ∈ S, blocks w ⊆ crossingEdges G U := by
    intro w hw
    exact reserveWedgeBlock_subset_crossingEdges hu hv (hSU hw)
      (hadj w hw).1 (hadj w hw).2
  have hpair : (S : Set V).PairwiseDisjoint blocks := by
    intro w hw x hx hwx
    apply reserveWedgeBlock_disjoint huv
    · intro hux
      subst x
      exact hu (hSU hx)
    · intro hvx
      subst x
      exact hv (hSU hx)
    · exact hwx
  have hcard : ∀ w ∈ S, (blocks w).card = 2 := by
    intro w _hw
    exact card_reserveWedgeBlock huv
  have htail := reserveEdgeLaw_probability_activeBlocks_card_le_le_exp
    G U r hr blocks S hcross hpair 2 k hcard hk
  simpa only [blocks, activeReserveWedgeVertices_eq_activeBlocks hcross] using htail

end

end Erdos207
