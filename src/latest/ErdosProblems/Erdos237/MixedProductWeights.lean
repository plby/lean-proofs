import ErdosProblems.Erdos237.ProductWeights
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-! Product first-moment estimates with different weights on each coordinate. -/

namespace Erdos237

open Finset
open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

theorem sum_mixed_product_weights (w : ι → α → ℝ) (hw : ∀ i, ∑ a, w i a = 1) :
    ∑ x : ι → α, ∏ i, w i (x i) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [hw]

theorem sum_coordinate_mixed_product_weights (w c : ι → α → ℝ)
    (hw : ∀ i, ∑ a, w i a = 1) (i : ι) :
    ∑ x : ι → α, c i (x i) * ∏ j, w j (x j) = ∑ a, c i a * w i a := by
  classical
  have hprod (x : ι → α) : c i (x i) * ∏ j, w j (x j) =
      ∏ j, (if j = i then c j (x j) else 1) * w j (x j) := by
    rw [prod_mul_distrib]
    simp
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j (a : α) => (if j = i then c j a else 1) * w j a)]
  have hsum (j : ι) : (∑ a : α, (if j = i then c j a else 1) * w j a) =
      if j = i then ∑ a, c i a * w i a else 1 := by
    split_ifs with h
    · subst j
      simp
    · simp [hw]
  simp_rw [hsum]
  simp

theorem sum_cost_mixed_product_weights (w c : ι → α → ℝ)
    (hw : ∀ i, ∑ a, w i a = 1) :
    ∑ x : ι → α, (∑ i, c i (x i)) * ∏ i, w i (x i) =
      ∑ i, ∑ a, c i a * w i a := by
  classical
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [sum_coordinate_mixed_product_weights w c hw]

theorem half_le_mixed_product_mass_below_cutoff (w c : ι → α → ℝ)
    (hw : ∀ i, ∑ a, w i a = 1) (hw0 : ∀ i a, 0 ≤ w i a) (hc0 : ∀ i a, 0 ≤ c i a)
    (t : ℝ) (ht : 0 < t) (hmean : (∑ i, ∑ a, c i a * w i a) ≤ t / 2) :
    1 / 2 ≤ ∑ x : ι → α, if (∑ i, c i (x i)) ≤ t then ∏ i, w i (x i) else 0 := by
  classical
  let mass (x : ι → α) := ∏ i, w i (x i)
  let cost (x : ι → α) := ∑ i, c i (x i)
  have hmass (x : ι → α) : 0 ≤ mass x := prod_nonneg fun i _ => hw0 i (x i)
  have hcost (x : ι → α) : 0 ≤ cost x := sum_nonneg fun i _ => hc0 i (x i)
  have hpoint (x : ι → α) : t * (if cost x ≤ t then 0 else mass x) ≤ cost x * mass x := by
    split_ifs with hx
    · simpa using mul_nonneg (hcost x) (hmass x)
    · exact mul_le_mul_of_nonneg_right (le_of_not_ge hx) (hmass x)
  have hbad : t * (∑ x : ι → α, if cost x ≤ t then 0 else mass x) ≤ t / 2 := by
    calc
      _ = ∑ x : ι → α, t * (if cost x ≤ t then 0 else mass x) := mul_sum _ _ _
      _ ≤ ∑ x : ι → α, cost x * mass x := sum_le_sum fun x _ => hpoint x
      _ = ∑ i, ∑ a, c i a * w i a := sum_cost_mixed_product_weights w c hw
      _ ≤ t / 2 := hmean
  have htotal : (∑ x : ι → α, if cost x ≤ t then mass x else 0) +
      (∑ x : ι → α, if cost x ≤ t then 0 else mass x) = 1 := by
    rw [← sum_add_distrib]
    convert sum_mixed_product_weights w hw using 1
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp [mass]
  change 1 / 2 ≤ ∑ x : ι → α, if cost x ≤ t then mass x else 0
  nlinarith

theorem mixed_product_mass_lower_bound (w c : ι → α → ℝ)
    (hw : ∀ i a, 0 ≤ w i a) (hc : ∀ i a, 0 ≤ c i a)
    (hZ : ∀ i, 0 < ∑ a, w i a)
    (hmean : (∑ i, ∑ a, c i a * (w i a / ∑ b, w i b)) ≤ 1 / 4) :
    (∏ i, ∑ a, w i a) / 2 ≤
      ∑ x : ι → α, if (∑ i, c i (x i)) ≤ 1 / 2 then ∏ i, w i (x i) else 0 := by
  classical
  let Z := ∏ i, ∑ a, w i a
  have hZpos : 0 < Z := prod_pos fun i _ => hZ i
  have hprob (i : ι) : (∑ a, w i a / ∑ b, w i b) = 1 := by
    rw [← sum_div, div_self (hZ i).ne']
  have h := half_le_mixed_product_mass_below_cutoff
    (fun i a => w i a / ∑ b, w i b) c hprob
    (fun i a => div_nonneg (hw i a) (hZ i).le) hc (1 / 2) (by norm_num)
    (by simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using hmean)
  have hmul := mul_le_mul_of_nonneg_left h hZpos.le
  calc
    _ = Z * (1 / 2) := by dsimp [Z]; ring
    _ ≤ _ := hmul
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      split_ifs
      · rw [prod_div_distrib]
        change Z * (_ / Z) = _
        field_simp
      · ring

end Erdos237
