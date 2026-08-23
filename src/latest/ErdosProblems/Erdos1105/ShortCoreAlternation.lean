import ErdosProblems.Erdos1105.LowCoreEndpointData
import ErdosProblems.Erdos1105.ShortCoreNeighborPattern

namespace Erdos1105

open SimpleGraph Finset

/-- Between the first end-neighbor and last start-neighbor, the two
endpoints have exactly the same, alternating neighbors. -/
theorem short_low_core_middle_alternates {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) :
    ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b < p.length ∧ Even (b - a) ∧
      (∀ j < a, ¬G.Adj y (p.getVert j)) ∧
      (∀ j, b < j → j ≤ p.length → ¬G.Adj x (p.getVert j)) ∧
      (∀ t, a ≤ t → t ≤ b →
        (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
        (G.Adj y (p.getVert t) ↔ Even (t - a))) := by
  classical
  have hlong : 2 * d + 3 ≤ p.length + 1 := by omega
  obtain ⟨a, b, ha0, hab, hbL, hya, hxb, hbefore, hafter, hnoA, hnoB⟩ :=
    low_core_endpoint_data hG hu hconn p hp hlong
  have hflip (t : ℕ) (hat : a ≤ t) (htb : t < b) :
      G.Adj y (p.getVert (t + 1)) ↔ ¬G.Adj y (p.getVert t) := by
    have h₁ := short_low_core_neighbor_iff hG hu hconn p hp hlen
      (show t < p.length by omega)
    have h₂ := short_low_core_neighbor_iff hG hu hconn p hp hlen
      (show t + 1 < p.length by omega)
    have hnA := hnoA (t + 1) (by omega) (by omega)
    have hnB := hnoB t htb
    tauto
  have heven (r : ℕ) (hr : r ≤ b - a) :
      G.Adj y (p.getVert (a + r)) ↔ Even r := by
    induction r with
    | zero => simpa only [Nat.add_zero, Even.zero, iff_true] using hya
    | succ r ih =>
      have h := hflip (a + r) (by omega) (by omega)
      have hi := ih (by omega)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.even_add_one] using h.trans (not_congr hi)
  have hmiddle (t : ℕ) (hat : a ≤ t) (htb : t ≤ b) :
      G.Adj y (p.getVert t) ↔ Even (t - a) := by
    simpa only [Nat.add_sub_of_le hat] using heven (t - a) (by omega)
  have hyb : G.Adj y (p.getVert b) := by
    by_contra h
    exact hafter (b + 1) (by omega) (by omega)
      ((short_low_core_neighbor_iff hG hu hconn p hp hlen hbL).mpr h)
  refine ⟨a, b, ha0, hab, hbL, (hmiddle b hab.le le_rfl).mp hyb,
    hbefore, hafter, ?_⟩
  intro t hat htb
  refine ⟨?_, hmiddle t hat htb⟩
  by_cases hta : t = a
  · subst t
    have hxa := low_core_start_neighbors_before hG hu hconn p hp hlong
      (show a ≤ p.length by omega) hbefore (a - 1) (by omega)
    rw [Nat.sub_add_cancel ha0] at hxa
    simpa only [Nat.sub_self, Even.zero, iff_true] using hxa
  · have h₁ := short_low_core_neighbor_iff hG hu hconn p hp hlen
      (show t - 1 < p.length by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at h₁
    have h₂ := hflip (t - 1) (by omega) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ t)] at h₂
    exact (h₁.trans h₂.symm).trans (hmiddle t hat htb)

/-- Counting the alternating middle shows that the two initial cliques
have equal size. -/
theorem short_low_core_complete_pattern {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ d ∧
      endNeighborIndices p =
        (range (d + 1 - a)).image (fun j ↦ a + 2 * j) ∪ Ico (p.length - a) p.length ∧
      (∀ j < a, ¬G.Adj y (p.getVert j)) ∧
      (∀ j, p.length - a < j → j ≤ p.length → ¬G.Adj x (p.getVert j)) ∧
      (∀ t, a ≤ t → t ≤ p.length - a →
        (G.Adj x (p.getVert t) ↔ Even (t - a)) ∧
        (G.Adj y (p.getVert t) ↔ Even (t - a))) := by
  classical
  obtain ⟨a, b, ha0, hab, hbL, habEven, hbefore, hafter, hmiddle⟩ :=
    short_low_core_middle_alternates hG hu hconn p hp hlen
  obtain ⟨r, hr⟩ := habEven
  have hbr : b = a + 2 * r := by omega
  let M := (range r).image (fun j ↦ a + 2 * j)
  have hBeq : endNeighborIndices p = M ∪ Ico b p.length := by
    ext t
    constructor
    · intro ht
      have htL := mem_range.mp (mem_filter.mp ht).1
      have hyt := (mem_filter.mp ht).2
      have hat : a ≤ t := by
        by_contra h
        exact hbefore t (by omega) hyt
      by_cases htb : t < b
      · apply mem_union_left
        obtain ⟨j, hj⟩ := (hmiddle t hat htb.le).2.mp hyt
        exact mem_image.mpr ⟨j, mem_range.mpr (by omega), by omega⟩
      · exact mem_union_right _ (mem_Ico.mpr ⟨by omega, htL⟩)
    · intro ht
      apply mem_filter.mpr
      rcases mem_union.mp ht with htM | htI
      · obtain ⟨j, hj, rfl⟩ := mem_image.mp htM
        have hjr := mem_range.mp hj
        refine ⟨mem_range.mpr (by omega), ?_⟩
        apply (hmiddle _ (by omega) (by omega)).2.mpr
        exact ⟨j, by omega⟩
      · have hbt := (mem_Ico.mp htI).1
        have htL := (mem_Ico.mp htI).2
        refine ⟨mem_range.mpr htL, ?_⟩
        by_contra hnot
        exact hafter (t + 1) (by omega) (by omega)
          ((short_low_core_neighbor_iff hG hu hconn p hp hlen htL).mpr hnot)
  have hMcard : M.card = r := by
    dsimp only [M]
    rw [card_image_of_injective _ (by intro i j h; dsimp at h; omega), card_range]
  have hdisj : Disjoint M (Ico b p.length) := by
    rw [Finset.disjoint_left]
    intro t htM htI
    obtain ⟨j, hj, rfl⟩ := mem_image.mp htM
    have := mem_range.mp hj
    have := (mem_Ico.mp htI).1
    omega
  have hBcard : (endNeighborIndices p).card = d + 1 := by
    rw [endNeighborIndices_card p hp.isPath]
    exact (longest_low_core_path_degrees hG hu hconn p hp (by omega)).2.2.2
  rw [hBeq, card_union_of_disjoint hdisj, hMcard, Nat.card_Ico] at hBcard
  have hb : b = p.length - a := by omega
  have hr' : r = d + 1 - a := by omega
  refine ⟨a, ha0, by omega, ?_, hbefore, ?_, ?_⟩
  · simpa only [M, hb, hr'] using hBeq
  · simpa only [hb] using hafter
  · simpa only [hb] using hmiddle

theorem short_low_core_end_pattern {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {u x y : V} {d : ℕ}
    (hG : NoLongCycle G (2 * d + 3)) (hu : G.IsUniversal u)
    (hconn : (G.induce {v | v ≠ u}).Preconnected)
    (p : G.Walk x y) (hp : IsLongestSetPath (vertexCore G d : Set V) p)
    (hlen : p.length = 2 * d + 2) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ d ∧
      endNeighborIndices p =
        (range (d + 1 - a)).image (fun j ↦ a + 2 * j) ∪ Ico (p.length - a) p.length := by
  obtain ⟨a, ha, had, hB, _⟩ := short_low_core_complete_pattern hG hu hconn p hp hlen
  exact ⟨a, ha, had, hB⟩

end Erdos1105

#print axioms Erdos1105.short_low_core_end_pattern
