import ErdosProblems.Erdos547.ReservedAllocation

/-!
# Greedy allocations with vertex capacities

The skew is positive. The first result uses disjoint tail and head sets;
the second reserves tail space and permits overlap.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

theorem SkewMatching.weight_zero_of_outLoad_zero (σ : SkewMatching G γ)
    {u : V} (hu : σ.outLoad u = 0) (v : V) : σ.weight u v = 0 := by
  have hz := (div_eq_iff (ne_of_gt σ.denominator_pos)).mp hu
  have hsingle : σ.weight u v ≤ ∑ y, σ.weight u y :=
    Finset.single_le_sum (fun y _ ↦ σ.nonnegative u y) (Finset.mem_univ v)
  exact le_antisymm (by simpa only [zero_mul] using hsingle.trans_eq hz) (σ.nonnegative u v)

open scoped Classical in
theorem exists_greedy_disjoint (A B : Finset V) (hdis : Disjoint A B) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u) (hb : ∀ u, b u ≤ 1)
    (hsupp : ∀ u ∉ A, a u = 0) (κ : ℝ) (hκ : 0 ≤ κ) (hs : κ ≤ ∑ u, a u)
    (γ : ℝ) (hγ : 0 < γ)
    (hN : ∀ x ∈ A, γ * κ ≤ ∑ y ∈ B.filter (G.Adj x), b y) :
    ∃ σ : SkewMatching G γ, (∀ u, σ.outLoad u ≤ a u) ∧ (∀ u, σ.load u ≤ b u) ∧
      (∀ u v, ¬ (u ∈ A ∧ v ∈ B) → σ.weight u v = 0) ∧ σ.total = (1 + γ) * κ := by
  classical
  obtain ⟨r, hr, hra, hrsum⟩ := exists_capped_reservation a ha κ hκ hs
  have hrzero (u : V) (hu : u ∉ A) : r u = 0 :=
    le_antisymm ((hra u).trans_eq (hsupp u hu)) (hr u)
  let P := fun x y ↦ G.Adj x y ∧ y ∈ B
  have hN' (x : V) (hx : 0 < r x) : γ * (∑ u, r u) ≤
      ∑ y ∈ Finset.univ.filter (P x), (b y - r y) := by
    have hxA : x ∈ A := by
      by_contra hn
      rw [hrzero x hn] at hx
      exact (lt_irrefl 0) hx
    have hset : Finset.univ.filter (P x) = B.filter (G.Adj x) := by ext y; simp [P, and_comm]
    rw [hrsum, hset]
    convert hN x hxA using 1
    apply Finset.sum_congr rfl
    intro y hy
    have hyB := (Finset.mem_filter.mp hy).1
    have hyA : y ∉ A := fun hyA ↦ Finset.disjoint_left.mp hdis hyA hyB
    rw [hrzero y hyA, sub_zero]
  obtain ⟨σ, hout, hload, hweight, htotal⟩ := exists_allocation_with_reserved_tails P
    (fun _ _ h ↦ h.1) r b hr (fun u ↦ (hra u).trans (hab u)) hb γ hγ
    (by
      intro x hx
      convert hN' x hx using 1
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter]
      · intro y _
        rfl)
  refine ⟨σ, fun u ↦ (hout u).trans_le (hra u), hload, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ A
    · exact hweight u v (fun hp ↦ huv ⟨hu, hp.2⟩)
    · exact σ.weight_zero_of_outLoad_zero ((hout u).trans (hrzero u hu)) v
  · simpa only [hrsum] using htotal

open scoped Classical in
theorem exists_greedy_overlapping (A B : Finset V) (a b : V → ℝ)
    (ha : ∀ u, 0 ≤ a u) (hab : ∀ u, a u ≤ b u) (hb : ∀ u, b u ≤ 1)
    (hsupp : ∀ u ∉ A, a u = 0) (κ : ℝ) (hκ : 0 ≤ κ) (hs : κ ≤ ∑ u, a u)
    (γ : ℝ) (hγ : 0 < γ)
    (hN : ∀ x ∈ A, (1 + γ) * κ ≤ ∑ y ∈ B.filter (G.Adj x), b y) :
    ∃ σ : SkewMatching G γ, (∀ u, σ.outLoad u ≤ a u) ∧ (∀ u, σ.load u ≤ b u) ∧
      (∀ u v, ¬ (u ∈ A ∧ v ∈ B) → σ.weight u v = 0) ∧ σ.total = (1 + γ) * κ := by
  classical
  obtain ⟨r, hr, hra, hrsum⟩ := exists_capped_reservation a ha κ hκ hs
  have hrzero (u : V) (hu : u ∉ A) : r u = 0 :=
    le_antisymm ((hra u).trans_eq (hsupp u hu)) (hr u)
  let P := fun x y ↦ G.Adj x y ∧ y ∈ B
  have hN' (x : V) (hx : 0 < r x) : γ * (∑ u, r u) ≤
      ∑ y ∈ Finset.univ.filter (P x), (b y - r y) := by
    have hxA : x ∈ A := by
      by_contra hn
      rw [hrzero x hn] at hx
      exact (lt_irrefl 0) hx
    have hset : Finset.univ.filter (P x) = B.filter (G.Adj x) := by ext y; simp [P, and_comm]
    rw [hrsum, hset, Finset.sum_sub_distrib]
    have hpartial : (∑ y ∈ B.filter (G.Adj x), r y) ≤ κ := by
      rw [← hrsum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun y _ _ ↦ hr y)
    nlinarith only [hN x hxA, hpartial]
  obtain ⟨σ, hout, hload, hweight, htotal⟩ := exists_allocation_with_reserved_tails P
    (fun _ _ h ↦ h.1) r b hr (fun u ↦ (hra u).trans (hab u)) hb γ hγ
    (by
      intro x hx
      convert hN' x hx using 1
      apply Finset.sum_congr
      · ext y
        simp only [Finset.mem_filter]
      · intro y _
        rfl)
  refine ⟨σ, fun u ↦ (hout u).trans_le (hra u), hload, ?_, ?_⟩
  · intro u v huv
    by_cases hu : u ∈ A
    · exact hweight u v (fun hp ↦ huv ⟨hu, hp.2⟩)
    · exact σ.weight_zero_of_outLoad_zero ((hout u).trans (hrzero u hu)) v
  · simpa only [hrsum] using htotal

/-- At skew zero, empty head sets satisfy the numerical capacity condition
but cannot support a positive allocation. -/
theorem zero_skew_disjoint_capacity_counterexample :
    Disjoint (Finset.univ : Finset (Fin 1)) ∅ ∧
    (1 : ℝ) ≤ (∑ _u : Fin 1, (1 : ℝ)) ∧
    (∀ _x : Fin 1, (0 : ℝ) * 1 ≤ ∑ _y ∈ (∅ : Finset (Fin 1)), (1 : ℝ)) ∧
    ¬ ∃ σ : SkewMatching (⊥ : SimpleGraph (Fin 1)) 0, σ.total = 1 := by
  refine ⟨by simp, by simp, by simp, ?_⟩
  rintro ⟨σ, htotal⟩
  have hz (u v : Fin 1) : σ.weight u v = 0 := σ.supported u v (by simp)
  have ht : σ.total = 0 := by simp only [SkewMatching.total, hz, Finset.sum_const_zero]
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_greedy_disjoint
#print axioms Erdos547.DPRS.exists_greedy_overlapping
