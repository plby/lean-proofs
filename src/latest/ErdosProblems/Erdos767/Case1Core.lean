import Mathlib

open Finset
open SimpleGraph
open scoped SimpleGraph

namespace E767DiracCase1

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

/-- The zero-based positions on a cycle at which its vertex is adjacent to
the terminal vertex of the lollipop handle.  We use `range C.length`, so the
repeated terminal copy of the initial cycle vertex is not counted twice. -/
def cycleNeighborIndices {V : Type u} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x : V}
    (C : G.Walk x x) (y : V) : Finset ℕ :=
  (Finset.range C.length).filter fun i ↦ G.Adj y (C.getVert i)

/-- Every neighbor of `y` which belongs to the non-repeated cycle carrier is
represented by an index in `cycleNeighborIndices`. -/
lemma cycle_neighbors_subset_index_image {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    {C : G.Walk x x} (hC : C.IsCycle) :
    G.neighborFinset y ∩ C.support.dropLast.toFinset ⊆
      (cycleNeighborIndices G C y).image C.getVert := by
  intro z hz
  have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp
    (Finset.mem_inter.mp hz).1
  have hzdrop : z ∈ C.support.dropLast :=
    List.mem_toFinset.mp (Finset.mem_inter.mp hz).2
  have hzdrop' : z ∈ C.dropLast.support := by
    rw [C.support_dropLast hC.not_nil]
    exact hzdrop
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzdrop'
  have hilt : i < C.length := by
    have hlenDrop : C.dropLast.length = C.length - 1 := C.length_dropLast
    rw [hlenDrop] at hile
    have hpos : 0 < C.length := by
      rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
      exact hC.not_nil
    omega
  apply Finset.mem_image.mpr
  refine ⟨i, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hilt, ?_⟩
    rw [← C.getVert_dropLast hilt]
    exact hi.symm ▸ hyz
  · rw [← C.getVert_dropLast hilt, hi]

/-- The cycle-side neighbors of `y` are no more numerous than their index
set.  This form avoids choosing an inverse indexing map explicitly. -/
lemma card_cycle_neighbors_le_indices {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    {C : G.Walk x x} (hC : C.IsCycle) :
    (G.neighborFinset y ∩ C.support.dropLast.toFinset).card ≤
      (cycleNeighborIndices G C y).card := by
  calc
    (G.neighborFinset y ∩ C.support.dropLast.toFinset).card ≤
        ((cycleNeighborIndices G C y).image C.getVert).card :=
      Finset.card_le_card (cycle_neighbors_subset_index_image G hC)
    _ ≤ (cycleNeighborIndices G C y).card := Finset.card_image_le

/-- For a path ending at `y`, at most `P.length` vertices of the path are
neighbors of `y`.  The extra support vertex is `y` itself, which cannot be
its own neighbor in a simple graph. -/
lemma card_path_neighbors_le_length {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y : V}
    {P : G.Walk x y} (hP : P.IsPath) :
    (G.neighborFinset y ∩ P.support.toFinset).card ≤ P.length := by
  have hsub : G.neighborFinset y ∩ P.support.toFinset ⊆
      P.support.toFinset.erase y := by
    intro z hz
    have hyz : G.Adj y z := (G.mem_neighborFinset y z).mp
      (Finset.mem_inter.mp hz).1
    exact Finset.mem_erase.mpr
      ⟨hyz.ne.symm, (Finset.mem_inter.mp hz).2⟩
  calc
    (G.neighborFinset y ∩ P.support.toFinset).card ≤
        (P.support.toFinset.erase y).card := Finset.card_le_card hsub
    _ = P.length := by
      rw [Finset.card_erase_of_mem
        (List.mem_toFinset.mpr P.end_mem_support)]
      rw [List.toFinset_card_of_nodup hP.support_nodup, P.length_support]
      omega

/-- Maximality of the lollipop says that every neighbor of the terminal
vertex is already on the cycle or handle.  Under that cover, its degree is
bounded by the handle length plus the number of cycle-neighbor indices. -/
lemma degree_le_handle_add_cycle_indices {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {C : G.Walk x x} {P : G.Walk x y}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset) :
    G.degree y ≤ P.length + (cycleNeighborIndices G C y).card := by
  let A : Finset V := G.neighborFinset y ∩ C.support.dropLast.toFinset
  let B : Finset V := G.neighborFinset y ∩ P.support.toFinset
  have hAB : G.neighborFinset y ⊆ A ∪ B := by
    intro z hz
    rcases Finset.mem_union.mp (hcover hz) with hzC | hzP
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hz, hzC⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hz, hzP⟩)
  rw [← G.card_neighborFinset_eq_degree]
  calc
    (G.neighborFinset y).card ≤ (A ∪ B).card :=
      Finset.card_le_card hAB
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ (cycleNeighborIndices G C y).card + P.length :=
      Nat.add_le_add (card_cycle_neighbors_le_indices G hC)
        (card_path_neighbors_le_length G hP)
    _ = P.length + (cycleNeighborIndices G C y).card := Nat.add_comm _ _

/-- A finite set of natural numbers contained in `[ell, c-ell)` and never
containing a number together with its successor occupies at most half of
that interval.  The strict upper bound is the exact one delivered by the two
cycle-splice inequalities in the lollipop argument. -/
lemma two_mul_card_le_of_nonconsecutive
    {S : Finset ℕ} {ell c : ℕ}
    (hS : S.Nonempty)
    (hbounds : ∀ i ∈ S, ell ≤ i ∧ i + 1 < c - ell)
    (hnext : ∀ i ∈ S, i + 1 ∉ S) :
    2 * S.card ≤ c - 2 * ell := by
  let T : Finset ℕ := S.image Nat.succ
  have hTcard : T.card = S.card := by
    dsimp [T]
    exact Finset.card_image_of_injective S Nat.succ_injective
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    obtain ⟨j, hjS, hji⟩ := Finset.mem_image.mp hiT
    have : j + 1 = i := by simpa [Nat.succ_eq_add_one] using hji
    exact hnext j hjS (this ▸ hiS)
  have hunion : S ∪ T ⊆ Finset.Ico ell (c - ell) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hiS | hiT
    · have hiB := hbounds i hiS
      exact Finset.mem_Ico.mpr ⟨hiB.1, by omega⟩
    · obtain ⟨j, hjS, rfl⟩ := Finset.mem_image.mp hiT
      have hjB := hbounds j hjS
      exact Finset.mem_Ico.mpr ⟨by omega, by
        simpa [Nat.succ_eq_add_one] using hjB.2⟩
  obtain ⟨i, hiS⟩ := hS
  have hiB := hbounds i hiS
  have hell : 2 * ell ≤ c := by omega
  have hcard : 2 * S.card ≤ (c - ell) - ell := by
    calc
      2 * S.card = S.card + T.card := by rw [hTcard]; omega
      _ = (S ∪ T).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (Finset.Ico ell (c - ell)).card := Finset.card_le_card hunion
      _ = (c - ell) - ell := Nat.card_Ico ell (c - ell)
  omega

/-- Dirac's best-lollipop argument, Case 1 (the terminal vertex has a
neighbor on the cycle), reduced to its checked counting core.

`hbounds` and `hnext` are exactly the facts obtained from the two possible
cycle splices: every cycle-neighbor index is separated from both ends by the
handle length, and two such indices cannot be consecutive. -/
theorem best_lollipop_case1 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {C : G.Walk x x} {P : G.Walk x y} {k : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset)
    (hcycle : (cycleNeighborIndices G C y).Nonempty)
    (hbounds : ∀ i ∈ cycleNeighborIndices G C y,
      P.length ≤ i ∧ i + 1 < C.length - P.length)
    (hnext : ∀ i ∈ cycleNeighborIndices G C y,
      i + 1 ∉ cycleNeighborIndices G C y)
    (hdegree : k ≤ G.degree y) :
    2 * k ≤ C.length := by
  have hdegUpper := degree_le_handle_add_cycle_indices G hC hP hcover
  have hindex := two_mul_card_le_of_nonconsecutive hcycle hbounds hnext
  obtain ⟨i, hi⟩ := hcycle
  have hiB := hbounds i hi
  have hlen : 2 * P.length ≤ C.length := by omega
  omega

/-- The contradiction form used in the proof of Dirac's theorem: Case 1 is
impossible when the chosen longest cycle has length strictly below `2*k`. -/
theorem best_lollipop_case1_false {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} {C : G.Walk x x} {P : G.Walk x y} {k : ℕ}
    (hC : C.IsCycle) (hP : P.IsPath)
    (hcover : G.neighborFinset y ⊆
      C.support.dropLast.toFinset ∪ P.support.toFinset)
    (hcycle : (cycleNeighborIndices G C y).Nonempty)
    (hbounds : ∀ i ∈ cycleNeighborIndices G C y,
      P.length ≤ i ∧ i + 1 < C.length - P.length)
    (hnext : ∀ i ∈ cycleNeighborIndices G C y,
      i + 1 ∉ cycleNeighborIndices G C y)
    (hdegree : k ≤ G.degree y) (hshort : C.length < 2 * k) : False := by
  have := best_lollipop_case1 G hC hP hcover hcycle hbounds hnext hdegree
  omega

end

end E767DiracCase1

