import ErdosProblems.Erdos547.BalancedNumbers
import ErdosProblems.Erdos547.BipartiteFractional
import ErdosProblems.Erdos547.PairFromWeights

/-!
# Improved balancing across a fractional matching

Two prescribed allocations fill a bipartite fractional matching. The first
has all its tails on the designated side. No matching existence theorem is
assumed: the allocations are explicit multiples of the original rows.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

theorem proportional_endpoint (a b M t : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 < M) :
    (t * (a + b) / M + (b / a) * ((1 - t) * (a + b) / M)) / (1 + b / a) =
      (t * a + (1 - t) * b) / M := by
  have hab : a + b ≠ 0 := by linarith
  field_simp [ne_of_gt ha, ne_of_gt hM, hab]

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exists_improved_balancing_le (μ : FractionalMatching G) (U W : Finset V)
    (hdis : Disjoint U W) (hruns : μ.RunsBetween U W) (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (hsum : a₁ + a₂ + b₁ + b₂ ≤ 2 * μ.total)
    (hbound : max a₁ a₂ + min b₁ b₂ ≤ μ.total) :
    ∃ σ : SkewMatching G (a₂ / a₁), ∃ τ : SkewMatching G (b₂ / b₁),
      PairDominated σ τ μ ∧ σ.total = a₁ + a₂ ∧ τ.total = b₁ + b₂ ∧
      (∀ u ∉ U, σ.outLoad u = 0) ∧ (∀ u ∉ U ∪ W, τ.outLoad u = 0) := by
  have hM : 0 < μ.total := by linarith
  have hcross := hruns.crosses hdis
  obtain ⟨t, ht0, ht1, hleft, hright⟩ :=
    exists_balanced_coefficient a₁ a₂ b₁ b₂ μ.total hsum hbound
  let p := (a₁ + a₂) / μ.total
  let r := t * (b₁ + b₂) / μ.total
  let s := (1 - t) * (b₁ + b₂) / μ.total
  have hp : 0 ≤ p := div_nonneg (by linarith) hM.le
  have hr : 0 ≤ r := div_nonneg (mul_nonneg ht0 (by linarith)) hM.le
  have hs : 0 ≤ s := div_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (by linarith)) hM.le
  have heA₁ : (p + (a₂ / a₁) * 0) / (1 + a₂ / a₁) = a₁ / μ.total := by
    simpa only [one_mul, sub_self, zero_mul, zero_div, mul_zero, add_zero] using
      proportional_endpoint a₁ a₂ μ.total 1 ha₁ ha₂ hM
  have heA₂ : (0 + (a₂ / a₁) * p) / (1 + a₂ / a₁) = a₂ / μ.total := by
    simpa only [zero_mul, zero_div, sub_zero, one_mul, zero_add] using
      proportional_endpoint a₁ a₂ μ.total 0 ha₁ ha₂ hM
  have heB₁ : (r + (b₂ / b₁) * s) / (1 + b₂ / b₁) =
      (t * b₁ + (1 - t) * b₂) / μ.total :=
    proportional_endpoint b₁ b₂ μ.total t hb₁ hb₂ hM
  have heB₂ : (s + (b₂ / b₁) * r) / (1 + b₂ / b₁) =
      ((1 - t) * b₁ + t * b₂) / μ.total := by
    have hh := proportional_endpoint b₁ b₂ μ.total (1 - t) hb₁ hb₂ hM
    simpa only [sub_sub_cancel] using hh
  have hcoefL : (p + (a₂ / a₁) * 0) / (1 + a₂ / a₁) +
      (r + (b₂ / b₁) * s) / (1 + b₂ / b₁) ≤ 1 := by
    rw [heA₁, heB₁, ← add_div]
    apply (div_le_one hM).mpr
    linarith
  have hcoefR : (0 + (a₂ / a₁) * p) / (1 + a₂ / a₁) +
      (s + (b₂ / b₁) * r) / (1 + b₂ / b₁) ≤ 1 := by
    rw [heA₂, heB₂, ← add_div]
    apply (div_le_one hM).mpr
    linarith
  have hc (u v : V) :
      (μ.rowWeight U p 0 u v + (a₂ / a₁) * μ.rowWeight U p 0 v u) / (1 + a₂ / a₁) +
      (μ.rowWeight U r s u v + (b₂ / b₁) * μ.rowWeight U r s v u) / (1 + b₂ / b₁) ≤
        μ.weight u v := by
    rw [hcross.rowWeight_endpoint, hcross.rowWeight_endpoint, ← add_mul]
    apply (mul_le_mul_of_nonneg_right _ (μ.nonnegative u v)).trans_eq (one_mul _)
    by_cases hu : u ∈ U
    · simpa only [if_pos hu] using hcoefL
    · simpa only [if_neg hu] using hcoefR
  obtain ⟨σ, τ, hdom, hσ, hτ⟩ := exists_pair_of_endpoint_bounds μ (a₂ / a₁) (b₂ / b₁)
    (div_nonneg ha₂ ha₁.le) (div_nonneg hb₂ hb₁.le)
    (μ.rowWeight U p 0) (μ.rowWeight U r s)
    (μ.rowWeight_nonneg U hp le_rfl) (μ.rowWeight_nonneg U hr hs) hc
  refine ⟨σ, τ, hdom, ?_, ?_, ?_, ?_⟩
  · change (∑ u, ∑ v, σ.weight u v) = _
    simp_rw [hσ]
    rw [hcross.rowWeight_total, add_zero]
    exact div_mul_cancel₀ _ (ne_of_gt hM)
  · change (∑ u, ∑ v, τ.weight u v) = _
    simp_rw [hτ]
    rw [hcross.rowWeight_total]
    dsimp [r, s]
    field_simp [ne_of_gt hM]
    ring
  · intro u hu
    change (∑ v, σ.weight u v) / (1 + a₂ / a₁) = 0
    simp_rw [hσ]
    rw [μ.rowWeight_sum, if_neg hu, zero_mul, zero_div]
  · intro u hu
    change (∑ v, τ.weight u v) / (1 + b₂ / b₁) = 0
    simp_rw [hτ]
    rw [μ.rowWeight_sum, hruns.load_zero_outside hu, mul_zero, zero_div]

theorem exists_improved_balancing (μ : FractionalMatching G) (U W : Finset V)
    (hdis : Disjoint U W) (hruns : μ.RunsBetween U W) (a₁ a₂ b₁ b₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 ≤ a₂) (hb₁ : 0 < b₁) (hb₂ : 0 ≤ b₂)
    (hsum : a₁ + a₂ + b₁ + b₂ = 2 * μ.total)
    (hbound : max a₁ a₂ + min b₁ b₂ ≤ μ.total) :
    ∃ σ : SkewMatching G (a₂ / a₁), ∃ τ : SkewMatching G (b₂ / b₁),
      PairDominated σ τ μ ∧ σ.total = a₁ + a₂ ∧ τ.total = b₁ + b₂ ∧
      (∀ u ∉ U, σ.outLoad u = 0) ∧ (∀ u ∉ U ∪ W, τ.outLoad u = 0) :=
  exists_improved_balancing_le μ U W hdis hruns a₁ a₂ b₁ b₂ ha₁ ha₂ hb₁ hb₂ hsum.le hbound

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_improved_balancing
