import Arxiv.Arxiv2411_18291.FrozenEdgeDegreeBounds
import Mathlib.Tactic.FieldSimp

/-!
# An increment with both the edge degree and its comparison value frozen

The deterministic comparison changes only if the selected clique leaves
the tracked edge alive. Its drift therefore contains the survival factor
`1-degree(e)/|H|`; this factor must not be silently omitted.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def frozenTrackingIncrement (H : Finset (Block V q)) (e : Block V r) (δ : ℝ)
    (Q : Block V q) : ℝ :=
  -(frozenEdgeLoss H e Q : ℝ) - if ¬e.val ⊆ Q.val then δ else 0

theorem frozenTrackingIncrement_removed (H : Finset (Block V q)) (e : Block V r)
    (δ : ℝ) (Q : Block V q) (heQ : e.val ⊆ Q.val) :
    frozenTrackingIncrement H e δ Q = 0 := by
  simp [frozenTrackingIncrement, frozenEdgeLoss, heQ]

theorem frozenTrackingIncrement_abs_le (H : Finset (Block V q)) (e : Block V r)
    (δ : ℝ) (Q : Block V q) :
    |frozenTrackingIncrement H e δ Q| ≤ (frozenEdgeLoss H e Q : ℝ) + |δ| := by
  have h := abs_sub (-(frozenEdgeLoss H e Q : ℝ)) (if ¬e.val ⊆ Q.val then δ else 0)
  have hnonneg : (0 : ℝ) ≤ (frozenEdgeLoss H e Q : ℝ) := Nat.cast_nonneg _
  simp only [abs_neg, abs_of_nonneg hnonneg] at h
  apply h.trans
  have hδ : |if ¬e.val ⊆ Q.val then δ else 0| ≤ |δ| := by
    by_cases heQ : e.val ⊆ Q.val <;> simp [heQ]
  exact add_le_add le_rfl hδ

theorem frozenTrackingIncrement_abs_bound (hqr : r < q) (H : Finset (Block V q))
    (e : Block V r) (δ : ℝ) (Q : Block V q) :
    |frozenTrackingIncrement H e δ Q| ≤
      (q.choose r : ℝ) * (Fintype.card V : ℝ) ^ (q - r - 1) + |δ| := by
  apply (frozenTrackingIncrement_abs_le H e δ Q).trans
  exact add_le_add (by exact_mod_cast frozenEdgeLoss_le hqr H e Q) le_rfl

omit [Fintype V] in
theorem sum_surviving_cliques_scalar (H : Finset (Block V q)) (e : Block V r) (δ : ℝ) :
    (∑ Q ∈ H, if ¬e.val ⊆ Q.val then δ else 0) =
      ((H.card : ℝ) - (H.filter fun Q => e.val ⊆ Q.val).card) * δ := by
  have heq : H.filter (fun Q => ¬e.val ⊆ Q.val) = H \ H.filter (fun Q => e.val ⊆ Q.val) := by
    ext Q
    simp only [mem_filter, mem_sdiff]
    tauto
  have hcard := card_sdiff_add_card_eq_card (filter_subset (fun Q => e.val ⊆ Q.val) H)
  rw [← heq] at hcard
  have hc : ((H.filter fun Q => ¬e.val ⊆ Q.val).card : ℝ) +
      (H.filter fun Q => e.val ⊆ Q.val).card = H.card := by exact_mod_cast hcard
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  congr 1
  linarith only [hc]

theorem frozenTrackingIncrement_average (H : Finset (Block V q)) (hH : H.Nonempty)
    (e : Block V r) (δ : ℝ) :
    (∑ Q ∈ H, frozenTrackingIncrement H e δ Q) / H.card =
      -(∑ Q ∈ H, (frozenEdgeLoss H e Q : ℝ)) / H.card -
        (1 - ((H.filter fun P => e.val ⊆ P.val).card : ℝ) / H.card) * δ := by
  have hc : (H.card : ℝ) ≠ 0 := by exact_mod_cast hH.card_pos.ne'
  simp only [frozenTrackingIncrement, sum_sub_distrib, sum_neg_distrib,
    sum_surviving_cliques_scalar]
  field_simp [hc]

theorem frozenTrackingIncrement_abs_average_le (H : Finset (Block V q)) (hH : H.Nonempty)
    (e : Block V r) (δ : ℝ) :
    (∑ Q ∈ H, |frozenTrackingIncrement H e δ Q|) / H.card ≤
      (∑ Q ∈ H, (frozenEdgeLoss H e Q : ℝ)) / H.card + |δ| := by
  have hc : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hs := sum_le_sum (s := H) (fun Q _ => frozenTrackingIncrement_abs_le H e δ Q)
  have h := div_le_div_of_nonneg_right hs hc.le
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, add_div] at h
  simpa only [mul_div_cancel_left₀ _ hc.ne'] using h

end Arxiv2411_18291
