/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AvailablePairDegree
import ErdosProblems.Erdos207.CompatibleCandidateDegree

/-!
# Available pair-codegree from the leave degree

For an invariant greedy state, every available triangle through `uv` has a
third vertex joined to `u` in the leave.  Injectivity of the third vertex
therefore bounds the available codegree by the current leave degree.  This
connects the refined deletion envelope to the usual cover-down degree
trajectory.
-/

namespace Erdos207

open Finset

noncomputable section

noncomputable def singletonElement
    {V : Type*} (S : SingletonOn V) : V :=
  Classical.choose (card_eq_one.mp S.2)

lemma singleton_eq_singletonElement
    {V : Type*} (S : SingletonOn V) :
    S.1 = {singletonElement S} :=
  Classical.choose_spec (card_eq_one.mp S.2)

lemma singletonElement_mem
    {V : Type*} [DecidableEq V] (S : SingletonOn V) :
    singletonElement S ∈ S.1 := by
  rw [singleton_eq_singletonElement]
  simp

lemma singletonElement_injective
    {V : Type*} [DecidableEq V] :
    Function.Injective (singletonElement : SingletonOn V → V) := by
  intro S T h
  apply Subtype.ext
  rw [singleton_eq_singletonElement S, singleton_eq_singletonElement T, h]

/-- The third vertex of an available triangle through `uv`, regarded as a
neighbor of `u` in the leave. -/
noncomputable def availableThroughPairLeaveNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) {u v : V} (huv : u ≠ v)
    (T : availableTrianglesContainingPair S {u, v}) :
    (leaveGraph S.chosen).neighborFinset u := by
  let Troot : universeTriplesThroughPair u v :=
    ⟨T.1, by
      rw [mem_universeTriplesThroughPair_iff]
      have hpair := (mem_availableTrianglesContainingPair_iff.mp T.2).2
      exact ⟨hpair (by simp), hpair (by simp)⟩⟩
  let W : SingletonOn V := eraseThroughPair huv Troot
  let w : V := singletonElement W
  have hwErase : w ∈ (T.1.1.erase u).erase v := by
    exact singletonElement_mem W
  have hwT : w ∈ T.1.1 := mem_of_mem_erase (mem_of_mem_erase hwErase)
  have hwu : w ≠ u := by
    exact (mem_erase.mp (mem_of_mem_erase hwErase)).1
  have hlegal := hInv.2.2 T.1
    (mem_availableTrianglesContainingPair_iff.mp T.2).1
  have huT : u ∈ T.1.1 := by
    have hpair := (mem_availableTrianglesContainingPair_iff.mp T.2).2
    exact hpair (by simp)
  have hlocal := (isLegalExtension_iff hInv.1 hInv.2.1 T.1).mp hlegal
  have hnotCovered : ¬(coveredGraph S.chosen).Adj u w :=
    hlocal.2.1 u huT w hwT hwu.symm
  exact ⟨w, by
    rw [SimpleGraph.mem_neighborFinset]
    change u ≠ w ∧ ¬(coveredGraph S.chosen).Adj u w
    exact ⟨hwu.symm, hnotCovered⟩⟩

/-- The leave-neighbor extracted from an available triangle is its third
vertex, and in particular is a vertex of that triangle. -/
lemma availableThroughPairLeaveNeighbor_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) {u v : V} (huv : u ≠ v)
    (T : availableTrianglesContainingPair S {u, v}) :
    (availableThroughPairLeaveNeighbor hInv huv T).1 ∈ T.1.1 := by
  let Troot : universeTriplesThroughPair u v :=
    ⟨T.1, by
      rw [mem_universeTriplesThroughPair_iff]
      have hpair := (mem_availableTrianglesContainingPair_iff.mp T.2).2
      exact ⟨hpair (by simp), hpair (by simp)⟩⟩
  let W : SingletonOn V := eraseThroughPair huv Troot
  have hwErase : singletonElement W ∈ (T.1.1.erase u).erase v := by
    exact singletonElement_mem W
  have hwT : singletonElement W ∈ T.1.1 :=
    mem_of_mem_erase (mem_of_mem_erase hwErase)
  simpa only [availableThroughPairLeaveNeighbor, Troot, W] using hwT

lemma availableThroughPairLeaveNeighbor_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) {u v : V} (huv : u ≠ v) :
    Function.Injective (availableThroughPairLeaveNeighbor hInv huv) := by
  intro T U hTU
  apply Subtype.ext
  let Troot : universeTriplesThroughPair u v :=
    ⟨T.1, by
      rw [mem_universeTriplesThroughPair_iff]
      have hpair := (mem_availableTrianglesContainingPair_iff.mp T.2).2
      exact ⟨hpair (by simp), hpair (by simp)⟩⟩
  let Uroot : universeTriplesThroughPair u v :=
    ⟨U.1, by
      rw [mem_universeTriplesThroughPair_iff]
      have hpair := (mem_availableTrianglesContainingPair_iff.mp U.2).2
      exact ⟨hpair (by simp), hpair (by simp)⟩⟩
  have hw : singletonElement (eraseThroughPair huv Troot) =
      singletonElement (eraseThroughPair huv Uroot) :=
    congrArg Subtype.val hTU
  have herase : eraseThroughPair huv Troot = eraseThroughPair huv Uroot :=
    singletonElement_injective hw
  have hroot : Troot = Uroot := eraseThroughPair_injective huv herase
  exact congrArg (fun R : universeTriplesThroughPair u v ↦ R.1) hroot

/-- Available codegree through an uncovered pair is at most either endpoint's
degree in the leave. -/
theorem card_availableTrianglesContainingPair_le_leave_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) {u v : V} (huv : u ≠ v) :
    (availableTrianglesContainingPair S {u, v}).card ≤
      (leaveGraph S.chosen).degree u := by
  calc
    (availableTrianglesContainingPair S {u, v}).card =
        Fintype.card (availableTrianglesContainingPair S {u, v}) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card ((leaveGraph S.chosen).neighborFinset u) :=
      Fintype.card_le_of_injective
        (availableThroughPairLeaveNeighbor hInv huv)
        (availableThroughPairLeaveNeighbor_injective hInv huv)
    _ = ((leaveGraph S.chosen).neighborFinset u).card :=
      Fintype.card_coe _
    _ = (leaveGraph S.chosen).degree u :=
      by simpa using
        (SimpleGraph.card_neighborFinset_eq_degree
          (leaveGraph S.chosen) u)

/-- A maximum leave-degree bound implies the available-pair cutoff required
by the refined deletion envelope. -/
theorem hasAvailablePairCutoff_of_leave_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {Δ : ℕ}
    (hInv : GreedyInvariant F S)
    (hdeg : ∀ u : V, (leaveGraph S.chosen).degree u ≤ Δ) :
    HasAvailablePairCutoff Δ S := by
  intro P hP
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hP
  exact (card_availableTrianglesContainingPair_le_leave_degree
    hInv huv).trans (hdeg u)

/-- Exact leave degree of a packing in terms of its selected vertex star. -/
theorem IsPackingOn.leaveGraph_degree_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) (v : V) :
    (leaveGraph P).degree v =
      Fintype.card V - 1 - 2 * (triplesThrough P v).card := by
  change (coveredGraph P)ᶜ.degree v = _
  rw [SimpleGraph.degree_compl,
    hP.coveredGraph_degree_eq_two_mul_triplesThrough]

/-- Every packing vertex star has size at most half the ambient degree. -/
theorem IsPackingOn.card_triplesThrough_le_half
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) (v : V) :
    2 * (triplesThrough P v).card ≤ Fintype.card V - 1 := by
  have hdeg : (coveredGraph P).degree v ≤ Fintype.card V - 1 :=
    Nat.le_sub_one_of_lt ((coveredGraph P).degree_lt_card_verts v)
  simpa [hP.coveredGraph_degree_eq_two_mul_triplesThrough] using hdeg

/-- The sum of all selected vertex-star sizes is three times the packing
size. -/
theorem sum_card_triplesThrough
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : TripleSystemOn V) :
    ∑ v : V, (triplesThrough P v).card = 3 * P.card := by
  calc
    ∑ v : V, (triplesThrough P v).card =
        ∑ v : V, ∑ T ∈ P, if v ∈ T.1 then 1 else 0 := by
      apply sum_congr rfl
      intro v _hv
      simp [triplesThrough]
    _ = ∑ T ∈ P, ∑ v : V, if v ∈ T.1 then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ _T ∈ P, 3 := by
      apply sum_congr rfl
      intro T _hT
      simpa [T.2]
    _ = 3 * P.card := by simp [Nat.mul_comm]

/-- A packing has at most `|V|(|V|-1)/6` triples, in division-free form. -/
theorem IsPackingOn.six_mul_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) :
    6 * P.card ≤ Fintype.card V * (Fintype.card V - 1) := by
  have hsum : ∑ v : V, 2 * (triplesThrough P v).card ≤
      ∑ _v : V, (Fintype.card V - 1) := by
    apply sum_le_sum
    intro v _hv
    exact hP.card_triplesThrough_le_half v
  rw [← mul_sum, sum_card_triplesThrough] at hsum
  calc
    6 * P.card = 2 * (3 * P.card) := by omega
    _ ≤ Fintype.card V * (Fintype.card V - 1) := by simpa using hsum

/-- Once a packing is globally close to maximum size, every individual
vertex is close to saturated. -/
theorem IsPackingOn.star_lower_bound_from_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) (v : V) :
    6 * P.card - (Fintype.card V - 1) ^ 2 ≤
      2 * (triplesThrough P v).card := by
  let d : V → ℕ := fun w ↦ 2 * (triplesThrough P w).card
  have hsum : ∑ w : V, d w = 6 * P.card := by
    simp only [d, ← mul_sum, sum_card_triplesThrough]
    ring
  have hothers : ∑ w ∈ (univ.erase v), d w ≤
      (Fintype.card V - 1) ^ 2 := by
    calc
      ∑ w ∈ (univ.erase v), d w ≤
          ∑ _w ∈ (univ.erase v), (Fintype.card V - 1) := by
        apply sum_le_sum
        intro w _hw
        exact hP.card_triplesThrough_le_half w
      _ = (univ.erase v).card * (Fintype.card V - 1) := by simp
      _ = (Fintype.card V - 1) ^ 2 := by
        rw [card_erase_of_mem (mem_univ v), card_univ]
        ring
  have hsplit : ∑ w : V, d w = d v + ∑ w ∈ (univ.erase v), d w := by
    rw [add_comm]
    exact (sum_erase_add _ _ (mem_univ v)).symm
  rw [hsum] at hsplit
  simp only [d] at hsplit hothers
  omega

/-- Explicit maximum leave-degree envelope obtained from only packinghood
and the total number of selected triples. -/
theorem IsPackingOn.leaveGraph_degree_le_of_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P) (v : V) :
    (leaveGraph P).degree v ≤
      (Fintype.card V - 1) -
        (6 * P.card - (Fintype.card V - 1) ^ 2) := by
  rw [hP.leaveGraph_degree_eq]
  exact Nat.sub_le_sub_left (hP.star_lower_bound_from_card v) _

/-- The deterministic pair-codegree envelope supplied solely by packinghood
and the number of selected triples.  It is coarse during the bulk of the
process, but becomes small once the packing is globally close to maximum. -/
def packingPairEnvelope (V : Type*) [Fintype V] (m : ℕ) : ℕ :=
  (Fintype.card V - 1) -
    (6 * m - (Fintype.card V - 1) ^ 2)

/-- Every invariant packing state satisfies the deterministic pair envelope
at its current selected-edge count. -/
theorem hasAvailablePairCutoff_packingPairEnvelope
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V}
    (hInv : GreedyInvariant F S) :
    HasAvailablePairCutoff (packingPairEnvelope V S.chosen.card) S := by
  apply hasAvailablePairCutoff_of_leave_degree hInv
  intro v
  exact hInv.1.leaveGraph_degree_le_of_card v

end

end Erdos207
