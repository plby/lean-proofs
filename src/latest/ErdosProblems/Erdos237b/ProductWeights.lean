import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Product weights and a first-moment truncation bound

For the qualitative large-dimension variational argument, a first-moment
bound suffices to keep half the product mass inside the simplex. There is no
need for the sharp second-moment estimate used to obtain quantitative bounds.
These finite identities apply to step-function candidates on product boxes.
-/

namespace Erdos237b

open Finset
open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Total mass of an independent product of normalized finite weights. -/
theorem sum_product_weights (w : α → ℝ) (hw : ∑ a, w a = 1) :
    ∑ x : ι → α, ∏ i, w (x i) = 1 := by
  classical
  rw [← Fintype.prod_sum]
  simp [hw]

/-- A single coordinate's first moment is unchanged by taking a product
with normalized weights on the other coordinates. -/
theorem sum_coordinate_product_weights (w c : α → ℝ)
    (hw : ∑ a, w a = 1) (i : ι) :
    ∑ x : ι → α, c (x i) * ∏ j, w (x j) = ∑ a, c a * w a := by
  classical
  have hprod (x : ι → α) :
      c (x i) * ∏ j, w (x j) =
        ∏ j, (if j = i then c (x j) else 1) * w (x j) := by
    rw [prod_mul_distrib]
    simp
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun j (a : α) => (if j = i then c a else 1) * w a)]
  have hsum (j : ι) :
      (∑ a : α, (if j = i then c a else 1) * w a) =
        if j = i then ∑ a, c a * w a else 1 := by
    split_ifs <;> simp_all
  simp_rw [hsum]
  simp

/-- The first moment of a sum of coordinates under product weights. -/
theorem sum_cost_product_weights (w c : α → ℝ) (hw : ∑ a, w a = 1) :
    ∑ x : ι → α, (∑ i, c (x i)) * ∏ i, w (x i) =
      Fintype.card ι * ∑ a, c a * w a := by
  classical
  simp_rw [sum_mul]
  rw [sum_comm]
  simp_rw [sum_coordinate_product_weights w c hw]
  simp

/-- If the expected total cost is at most half a positive cutoff, at least
half the product mass has cost below the cutoff. -/
theorem half_le_product_mass_below_cutoff (w c : α → ℝ)
    (hw : ∑ a, w a = 1) (hw0 : ∀ a, 0 ≤ w a) (hc0 : ∀ a, 0 ≤ c a)
    (t : ℝ) (ht : 0 < t)
    (hmean : (Fintype.card ι : ℝ) * (∑ a, c a * w a) ≤ t / 2) :
    1 / 2 ≤ ∑ x : ι → α, if (∑ i, c (x i)) ≤ t then ∏ i, w (x i) else 0 := by
  classical
  let mass (x : ι → α) : ℝ := ∏ i, w (x i)
  let cost (x : ι → α) : ℝ := ∑ i, c (x i)
  have hmass (x : ι → α) : 0 ≤ mass x := prod_nonneg fun i _ => hw0 (x i)
  have hcost (x : ι → α) : 0 ≤ cost x := sum_nonneg fun i _ => hc0 (x i)
  have hpoint (x : ι → α) :
      t * (if cost x ≤ t then 0 else mass x) ≤ cost x * mass x := by
    split_ifs with hx
    · simpa using mul_nonneg (hcost x) (hmass x)
    · exact mul_le_mul_of_nonneg_right (le_of_not_ge hx) (hmass x)
  have hbad : t * (∑ x : ι → α, if cost x ≤ t then 0 else mass x) ≤ t / 2 := by
    calc
      _ = ∑ x : ι → α, t * (if cost x ≤ t then 0 else mass x) := mul_sum _ _ _
      _ ≤ ∑ x : ι → α, cost x * mass x := sum_le_sum fun x _ => hpoint x
      _ = Fintype.card ι * ∑ a, c a * w a := sum_cost_product_weights w c hw
      _ ≤ t / 2 := hmean
  have htotal :
      (∑ x : ι → α, if cost x ≤ t then mass x else 0) +
        (∑ x : ι → α, if cost x ≤ t then 0 else mass x) = 1 := by
    rw [← sum_add_distrib]
    convert sum_product_weights (ι := ι) w hw using 1
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp [mass]
  change 1 / 2 ≤ ∑ x : ι → α, if cost x ≤ t then mass x else 0
  nlinarith

end Erdos237b
