import ErdosProblems.Erdos556.IndexedCyclePaths
import ErdosProblems.Erdos556.DenseNeighborPatterns

/-!
# Finite vertex sets and their cycle positions
-/

namespace Erdos556

open SimpleGraph Finset

def cycleIndexSet {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z : V}
    (c : G.Walk z z) (W : Finset V) : Finset ℕ :=
  (range c.length).filter (fun i => c.getVert i ∈ W)

theorem cycleIndexSet_image {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z : V}
    (c : G.Walk z z) (hc : c.IsCycle) (W : Finset V) (hW : ∀ x ∈ W, x ∈ c.support) :
    (cycleIndexSet c W).image c.getVert = W := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := mem_image.mp hx
    exact hix ▸ (mem_filter.mp hi).2
  · intro hx
    obtain ⟨i, hix, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hW x hx)
    by_cases hie : i = c.length
    · have hzx : z = x := by simpa only [hie, Walk.getVert_length] using hix
      apply mem_image.mpr
      refine ⟨0, mem_filter.mpr ⟨mem_range.mpr (by have h := hc.three_le_length; omega), ?_⟩, ?_⟩
      · simpa only [Walk.getVert_zero, hzx] using hx
      · simpa only [Walk.getVert_zero] using hzx
    · exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr (by omega), hix ▸ hx⟩, hix⟩

theorem cycleIndexSet_card {V : Type*} [DecidableEq V] {G : SimpleGraph V} {z : V}
    (c : G.Walk z z) (hc : c.IsCycle) (W : Finset V) (hW : ∀ x ∈ W, x ∈ c.support) :
    (cycleIndexSet c W).card = W.card := by
  have hinj : Set.InjOn c.getVert (cycleIndexSet c W : Set ℕ) := by
    intro i hi j hj hij
    have hi' := mem_range.mp (mem_filter.mp hi).1
    have hj' := mem_range.mp (mem_filter.mp hj).1
    exact hc.getVert_injOn' (by change i ≤ c.length - 1; omega)
      (by change j ≤ c.length - 1; omega) hij
  have hcard := card_image_of_injOn hinj
  rw [cycleIndexSet_image c hc W hW] at hcard
  exact hcard.symm

theorem exists_cycle_interval_common_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (D L d : ℕ) (hL : 0 < L) (hscale : Fintype.card V ≤ D * d)
    (hdegree : ∀ v, d ≤ G.degree v) (hlen : 4 * D * L ≤ c.length) :
    ∃ (A : Finset ℕ) (W : Finset V), A.card = L ∧
      (∀ i ∈ A, i < 4 * D * L ∧ Even i) ∧
      (A.image c.getVert).card = L ∧
      Fintype.card V ≤ 2 * D * 2 ^ (2 * D * L) * W.card ∧
      ∀ i ∈ A, ∀ w ∈ W, G.Adj (c.getVert i) w := by
  classical
  obtain ⟨I, W, hI, hW, hcommon⟩ := exists_large_common_neighbor_class D L d hL
    (Fintype.card_pos_iff.mpr ⟨z⟩) hscale
    (fun i => G.neighborFinset (c.getVert (2 * i.val)))
    (fun i => by simpa only [G.card_neighborFinset_eq_degree] using hdegree (c.getVert (2 * i.val)))
  obtain ⟨J, hJI, hJ⟩ := exists_subset_card_eq hI
  let f : Fin (2 * D * L) ↪ ℕ :=
    ⟨fun i => 2 * i.val, by
      intro i j h
      change 2 * i.val = 2 * j.val at h
      exact Fin.ext (by omega)⟩
  let A := J.map f
  have hA : A.card = L := by simpa only [A, card_map] using hJ
  have hpos (i : ℕ) (hi : i ∈ A) : i < 4 * D * L ∧ Even i := by
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
    have hat := a.isLt
    change 2 * a.val < 4 * D * L ∧ Even (2 * a.val)
    have hb := Nat.mul_lt_mul_of_pos_left hat (by decide : 0 < 2)
    have he : 2 * (2 * D * L) = 4 * D * L := by ring
    rw [he] at hb
    exact ⟨hb, ⟨a.val, by omega⟩⟩
  have hinj : Set.InjOn c.getVert (A : Set ℕ) := by
    intro i hi j hj hij
    have hi' := (hpos i hi).1
    have hj' := (hpos j hj).1
    exact hc.getVert_injOn' (by change i ≤ c.length - 1; omega)
      (by change j ≤ c.length - 1; omega) hij
  refine ⟨A, W, hA, hpos, (card_image_of_injOn hinj).trans hA, hW, ?_⟩
  intro i hi w hw
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
  exact (G.mem_neighborFinset _ _).mp (hcommon a (hJI ha) w hw)

#print axioms cycleIndexSet_card
#print axioms exists_cycle_interval_common_neighbors

end Erdos556
