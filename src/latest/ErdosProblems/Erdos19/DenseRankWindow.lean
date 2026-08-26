import ErdosProblems.Erdos19.CoreConcentration
import ErdosProblems.Erdos19.RankWindowArithmetic

/-! # Explicit rank concentration in a dense core

A core of minimum line-graph degree `n - n / h^4`, whose smallest edge has
rank at least `h^4`, has a large family in the window `[r, r + r/h]`.
All thresholds and rounding operations are natural-number expressions.
-/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {X : Type*} [Fintype X]

theorem dense_core_rank_window_explicit (H : SetHypergraph X)
    (hlinear : H.IsLinear) (S : Finset H) (h r : ℕ)
    (hh : 2 ≤ h) (hr : h ^ 4 ≤ r)
    (hmin : ∀ f ∈ S, r ≤ f.1.ncard)
    (hdense : IsDenseCore H.lineGraph S (Fintype.card X - Fintype.card X / h ^ 4))
    (e : H) (heS : e ∈ S) (her : e.1.ncard = r) :
    (Fintype.card X - Fintype.card X / h ^ 4 - 2 * Fintype.card X / h ^ 2) *
        (Fintype.card X - Fintype.card X / h ^ 4 -
          (3 * Fintype.card X / h + (Fintype.card X - 1) / (r - 1) + 1)) ≤
      (S.filter fun f ↦ f.1.ncard ≤ r + r / h).card * (r * (r + r / h)) := by
  classical
  let n := Fintype.card X
  let m := n - n / h ^ 4
  have hhpos : 0 < h := by omega
  have hh2 : 2 ≤ h ^ 2 := by nlinarith only [hh]
  have h24 : h ^ 2 ≤ h ^ 4 := by
    nlinarith only [Nat.mul_le_mul_left (h ^ 2) (show 1 ≤ h ^ 2 by omega)]
  have hr2 : 2 ≤ r := hh2.trans (h24.trans hr)
  have hdiv₁ : 0 ≤ r / h ^ 2 := Nat.zero_le _
  have hdiv₂ : 0 ≤ r / h := Nat.zero_le _
  have hR : r + r / h ^ 2 ≤ r + r / h := by
    exact Nat.add_le_add_left (Nat.div_le_div_left (by nlinarith only [hh]) hhpos) r
  apply H.dense_core_rank_window_card hlinear S m r (r + r / h ^ 2)
    (r + r / h) (2 * n / h ^ 2) (3 * n / h) hr2 hR hmin hdense e heS her
  · let N := S.filter (H.lineGraph.Adj e)
    let T := N.filter fun f ↦ r + r / h ^ 2 < f.1.ncard
    have hb := H.dense_neighbor_rank_excess_budget hlinear e N T
      (fun f hf ↦ (mem_filter.mp hf).2) (filter_subset _ _) m r
      (r + r / h ^ 2 + 1) (by omega) (by omega) (hdense e heS)
      (fun f hf ↦ hmin f (mem_filter.mp hf).1)
      (fun f hf ↦ by have := (mem_filter.mp hf).2; omega)
    have hgap : r + r / h ^ 2 + 1 - r = r / h ^ 2 + 1 := by omega
    rw [hgap, her] at hb
    have hb' : m * (r - 1) + T.card * (r / h ^ 2 + 1) ≤ r * n :=
      hb.trans (Nat.mul_le_mul_left r (Nat.sub_le n r))
    exact (Nat.le_div_iff_mul_le (pow_pos hhpos 2)).2
      (first_rank_tail_bound n r h T.card hh hr hb')
  · intro f hfS hef hfsize
    let N := S.filter (H.lineGraph.Adj f)
    let T := N.filter fun g ↦ r + r / h < g.1.ncard
    have hb := H.dense_neighbor_rank_excess_budget hlinear f N T
      (fun g hg ↦ (mem_filter.mp hg).2) (filter_subset _ _) m r
      (r + r / h + 1) (by omega) (by omega) (hdense f hfS)
      (fun g hg ↦ hmin g (mem_filter.mp hg).1)
      (fun g hg ↦ by have := (mem_filter.mp hg).2; omega)
    have hgap : r + r / h + 1 - r = r / h + 1 := by omega
    rw [hgap] at hb
    have hb' : m * (r - 1) + T.card * (r / h + 1) ≤ (r + r / h ^ 2) * n :=
      hb.trans (Nat.mul_le_mul hfsize (Nat.sub_le n f.1.ncard))
    exact (Nat.le_div_iff_mul_le hhpos).2
      (second_rank_tail_bound n r h T.card hh hr hb')

#print axioms dense_core_rank_window_explicit

/-- A nonempty dense core contains a rank window consuming almost all
available ordered vertex pairs. This statement includes explicit constants. -/
theorem exists_dense_core_rank_window (H : SetHypergraph X)
    (hlinear : H.IsLinear) (S : Finset H) (h : ℕ)
    (hh : 16 ≤ h) (hmin : ∀ f ∈ S, h ^ 4 ≤ f.1.ncard)
    (hdense : IsDenseCore H.lineGraph S (Fintype.card X - Fintype.card X / h ^ 4))
    (hne : S.Nonempty) :
    ∃ r : ℕ, ∃ W : Finset H, h ^ 4 ≤ r ∧ W ⊆ S ∧
      (∀ f ∈ S, r ≤ f.1.ncard) ∧
      (∀ f ∈ W, f.1.ncard ≤ r + r / h) ∧
      (h - 10) * (Fintype.card X) ^ 2 ≤
        h * (∑ f ∈ W, f.1.ncard * (f.1.ncard - 1)) := by
  classical
  obtain ⟨e, heS, hemin⟩ := exists_min_image S (fun f : H ↦ f.1.ncard) hne
  let r := e.1.ncard
  let W := S.filter fun f ↦ f.1.ncard ≤ r + r / h
  have hr : h ^ 4 ≤ r := hmin e heS
  have hrn : r ≤ Fintype.card X := by
    have hx := Set.ncard_le_ncard (Set.subset_univ e.1)
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hx
  have hcount := H.dense_core_rank_window_explicit hlinear S h r (by omega) hr
    hemin hdense e heS rfl
  have hweight := rank_window_pair_weight_bound (Fintype.card X) r h W.card
    hh hr hrn hcount
  have hsum : W.card * r * (r - 1) ≤ ∑ f ∈ W, f.1.ncard * (f.1.ncard - 1) := by
    calc
      W.card * r * (r - 1) = ∑ _f ∈ W, r * (r - 1) := by simp [Nat.mul_assoc]
      _ ≤ ∑ f ∈ W, f.1.ncard * (f.1.ncard - 1) := by
        apply sum_le_sum
        intro f hf
        have hrf := hemin f (mem_filter.mp hf).1
        exact Nat.mul_le_mul hrf (Nat.sub_le_sub_right hrf 1)
  refine ⟨r, W, hr, filter_subset _ _, hemin, ?_, ?_⟩
  · exact fun f hf ↦ (mem_filter.mp hf).2
  · exact hweight.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left h hsum)

#print axioms exists_dense_core_rank_window

end Erdos19.SetHypergraph
