import ErdosProblems.Erdos745.Core
import Mathlib.Data.List.GetD

/-!
# Component orders and counting witnesses

These finite statements connect the ranked second component to counts of
components above a threshold, including ties.
-/

open scoped BigOperators

namespace Erdos745

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_componentOrders (G : SimpleGraph V) :
    (componentOrders G).sum = Fintype.card V := by
  classical
  have hcover : (Finset.univ.biUnion fun C : G.ConnectedComponent ↦
      C.supp.toFinset) = (Finset.univ : Finset V) := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, Set.mem_toFinset, true_and,
      iff_true]
    exact ⟨G.connectedComponentMk v,
      SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  have hdis : ∀ C ∈ (Finset.univ : Finset G.ConnectedComponent),
      ∀ D ∈ (Finset.univ : Finset G.ConnectedComponent), C ≠ D →
        Disjoint C.supp.toFinset D.supp.toFinset := by
    intro C _ D _ hCD
    exact Set.disjoint_toFinset.mpr
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent G hCD)
  have hcard := congrArg Finset.card hcover
  rw [Finset.card_biUnion hdis, Finset.card_univ] at hcard
  change (∑ C : G.ConnectedComponent, C.supp.ncard) = Fintype.card V
  simpa only [← Set.ncard_eq_toFinset_card'] using hcard

theorem sum_rankedComponentOrders (G : SimpleGraph V) :
    (rankedComponentOrders G).sum = Fintype.card V := by
  have h := congrArg Multiset.sum
    (Multiset.sort_eq (componentOrders G) (· ≥ ·))
  exact h.trans (sum_componentOrders G)

theorem pairwise_rankedComponentOrders (G : SimpleGraph V) :
    (rankedComponentOrders G).Pairwise (· ≥ ·) :=
  Multiset.pairwise_sort _ _

/-- The second component is at most half the vertex set, also when orders tie. -/
theorem twice_secondLargestComponentOrder_le (G : SimpleGraph V) :
    2 * secondLargestComponentOrder G ≤ Fintype.card V := by
  have hs := sum_rankedComponentOrders G
  have hp := pairwise_rankedComponentOrders G
  unfold secondLargestComponentOrder
  cases hL : rankedComponentOrders G with
  | nil => simp
  | cons a L =>
    cases L with
    | nil => simp
    | cons b L =>
      rw [hL] at hs hp
      have hab : b ≤ a := (List.pairwise_cons.mp hp).1 b (by simp)
      simp only [List.sum_cons] at hs
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      omega

theorem secondLargestComponentOrder_le_half (G : SimpleGraph V) :
    secondLargestComponentOrder G ≤ Fintype.card V / 2 := by
  have h := twice_secondLargestComponentOrder_le G
  omega

/-- Number of components whose orders are at least `k`. -/
noncomputable def largeComponentCount (G : SimpleGraph V) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun C : G.ConnectedComponent ↦ k ≤ C.supp.ncard).card

theorem largeComponentCount_eq_filter_length (G : SimpleGraph V) (k : ℕ) :
    largeComponentCount G k =
      ((rankedComponentOrders G).filter (k ≤ ·)).length := by
  classical
  change largeComponentCount G k =
    (Multiset.filter (k ≤ ·) (rankedComponentOrders G : Multiset ℕ)).card
  rw [show (rankedComponentOrders G : Multiset ℕ) = componentOrders G from
    Multiset.sort_eq _ _]
  simp only [componentOrders, Multiset.filter_map, Multiset.card_map]
  rfl

private theorem second_getD_ge_iff_filter_length (L : List ℕ)
    (hL : L.Pairwise (· ≥ ·)) {k : ℕ} (hk : 0 < k) :
    k ≤ L.getD 1 0 ↔ 2 ≤ (L.filter (k ≤ ·)).length := by
  cases L with
  | nil => simp; omega
  | cons a L =>
    cases L with
    | nil =>
      simp only [List.getD_cons_succ, List.getD_nil, List.filter_cons,
        List.filter_nil]
      split <;> simp <;> omega
    | cons b L =>
      have hab : b ≤ a := (List.pairwise_cons.mp hL).1 b (by simp)
      have hbL : ∀ c ∈ L, c ≤ b :=
        (List.pairwise_cons.mp (List.pairwise_cons.mp hL).2).1
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      by_cases hkb : k ≤ b
      · have hka : k ≤ a := hkb.trans hab
        simp [hkb, hka]
      · have hfilter : L.filter (k ≤ ·) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro c hc
          simpa using
            (Nat.not_le.mpr (lt_of_le_of_lt (hbL c hc) (Nat.lt_of_not_ge hkb)))
        simp only [List.filter_cons, hkb, decide_false, Bool.false_eq_true,
          ↓reduceIte, hfilter]
        by_cases hka : k ≤ a <;> simp [hka]

/-- Two distinct components of order at least `k` are exactly the witness
needed for the second-largest order to be at least `k`. -/
theorem le_secondLargestComponentOrder_iff_count (G : SimpleGraph V)
    {k : ℕ} (hk : 0 < k) :
    k ≤ secondLargestComponentOrder G ↔ 2 ≤ largeComponentCount G k := by
  rw [largeComponentCount_eq_filter_length]
  exact second_getD_ge_iff_filter_length _ (pairwise_rankedComponentOrders G) hk

theorem le_secondLargestComponentOrder_iff_exists (G : SimpleGraph V)
    {k : ℕ} (hk : 0 < k) :
    k ≤ secondLargestComponentOrder G ↔
      ∃ C D : G.ConnectedComponent,
        C ≠ D ∧ k ≤ C.supp.ncard ∧ k ≤ D.supp.ncard := by
  classical
  rw [le_secondLargestComponentOrder_iff_count G hk, largeComponentCount]
  change 1 < _ ↔ _
  rw [Finset.one_lt_card]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨C, hC, D, hD, hCD⟩
    exact ⟨C, D, hCD, hC, hD⟩
  · rintro ⟨C, D, hCD, hC, hD⟩
    exact ⟨C, hC, D, hD, hCD⟩

/-- A positive second-ranked order is attained by an actual component. -/
theorem exists_component_order_eq_second (G : SimpleGraph V)
    (hpos : 0 < secondLargestComponentOrder G) :
    ∃ C : G.ConnectedComponent, C.supp.ncard = secondLargestComponentOrder G := by
  classical
  have hmem : secondLargestComponentOrder G ∈ rankedComponentOrders G := by
    cases hL : rankedComponentOrders G with
    | nil => simp [secondLargestComponentOrder, hL] at hpos
    | cons a L =>
      cases L with
      | nil => simp [secondLargestComponentOrder, hL] at hpos
      | cons b L => simp [secondLargestComponentOrder, hL]
  simpa only [rankedComponentOrders, Multiset.mem_sort, componentOrders,
    Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] using hmem

end Erdos745
