import ErdosProblems.Erdos19.Core

/-! # Integral rank separation in a neighbor family

The two-weight pair budget is expressed as a baseline charge for every
neighbor and an extra charge for the larger neighbors. No real division or
rounding convention is needed in this form.
-/

namespace Erdos19.SetHypergraph

open Finset

variable {X : Type*} [Fintype X]

theorem neighbor_rank_excess_budget (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (S T : Finset H)
    (hSN : ∀ f ∈ S, f ∈ H.neighborEdges e) (hTS : T ⊆ S)
    (r R : ℕ) (hr : 1 ≤ r) (hR : r ≤ R)
    (hmin : ∀ f ∈ S, r ≤ f.1.ncard)
    (hlarge : ∀ f ∈ T, R ≤ f.1.ncard) :
    S.card * (r - 1) + T.card * (R - r) ≤
      e.1.ncard * (Fintype.card X - e.1.ncard) := by
  classical
  have hbudget := H.two_family_pairBudget hlinear e
    (T : Set H) ((S \ T : Finset H) : Set H)
    (fun f hf ↦ hSN f (hTS hf))
    (fun f hf ↦ hSN f (mem_sdiff.mp hf).1)
    (by simpa only [Finset.coe_sdiff] using
      (Set.disjoint_sdiff_right : Disjoint (T : Set H) ((S : Set H) \ T)))
    (R - 1) (r - 1)
    (fun f hf ↦ Nat.sub_le_sub_right (hlarge f hf) 1)
    (fun f hf ↦ Nat.sub_le_sub_right (hmin f (mem_sdiff.mp hf).1) 1)
  simp only [Set.ncard_coe_finset] at hbudget
  have hcard : (S \ T).card + T.card = S.card := card_sdiff_add_card_eq_card hTS
  have hweight : R - 1 = (r - 1) + (R - r) := by omega
  rw [hweight, Nat.mul_add] at hbudget
  nlinarith only [hbudget, hcard]

theorem dense_neighbor_rank_excess_budget (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (S T : Finset H)
    (hSN : ∀ f ∈ S, f ∈ H.neighborEdges e) (hTS : T ⊆ S)
    (m r R : ℕ) (hr : 1 ≤ r) (hR : r ≤ R) (hm : m ≤ S.card)
    (hmin : ∀ f ∈ S, r ≤ f.1.ncard)
    (hlarge : ∀ f ∈ T, R ≤ f.1.ncard) :
    m * (r - 1) + T.card * (R - r) ≤
      e.1.ncard * (Fintype.card X - e.1.ncard) := by
  exact (Nat.add_le_add_right (Nat.mul_le_mul_right (r - 1) hm) _).trans
    (H.neighbor_rank_excess_budget hlinear e S T hSN hTS r R hr hR hmin hlarge)

/-- If the reference edge has the minimum rank, its larger neighbors are
charged against the slack in its minimum-degree budget. -/
theorem large_neighbors_mul_gap_le (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (S : Finset H)
    (hSN : ∀ f ∈ S, f ∈ H.neighborEdges e)
    (m r R : ℕ) (hr : 1 ≤ r) (hR : r ≤ R) (hm : m ≤ S.card)
    (hmin : ∀ f ∈ S, r ≤ f.1.ncard) :
    (S.filter fun f ↦ R ≤ f.1.ncard).card * (R - r) ≤
      e.1.ncard * (Fintype.card X - e.1.ncard) - m * (r - 1) := by
  classical
  have hb := H.dense_neighbor_rank_excess_budget hlinear e S
    (S.filter fun f ↦ R ≤ f.1.ncard) hSN (filter_subset _ _) m r R hr hR hm hmin
    (fun f hf ↦ (mem_filter.mp hf).2)
  omega

#print axioms neighbor_rank_excess_budget
#print axioms large_neighbors_mul_gap_le

/-- A family of neighbors whose ranks are large compared with the reference
edge has few members. This version permits an upper bound `R` on its rank. -/
theorem neighbor_card_le_div_of_scaled_rank (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e : H) (T : Finset H)
    (hTN : ∀ f ∈ T, f ∈ H.neighborEdges e)
    (a R q : ℕ) (ha : 0 < a) (hR : 0 < R) (heR : e.1.ncard ≤ R)
    (hq : a * R ≤ q) (hweight : ∀ f ∈ T, q ≤ f.1.ncard - 1) :
    T.card ≤ Fintype.card X / a := by
  classical
  have hb := H.ncard_mul_le_pairBudget hlinear e (T : Set H) hTN q hweight
  simp only [Set.ncard_coe_finset] at hb
  apply (Nat.le_div_iff_mul_le ha).2
  apply Nat.le_of_mul_le_mul_left (c := R) _ hR
  calc
    R * (T.card * a) = T.card * (a * R) := by ring
    _ ≤ T.card * q := Nat.mul_le_mul_left _ hq
    _ ≤ e.1.ncard * (Fintype.card X - e.1.ncard) := hb
    _ ≤ R * Fintype.card X := Nat.mul_le_mul heR (Nat.sub_le _ _)

#print axioms neighbor_card_le_div_of_scaled_rank

end Erdos19.SetHypergraph
