/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAbsoluteKernel
import Mathlib.Analysis.Complex.Exponential

/-!
# Finite Euler products and logarithmic moments of moved assignments

The number of coordinate choices is retained explicitly. Applying this
with ordered pairs of coordinates gives the `k^2` moved-prime weight.
No infinite-series interchange or dimension-dependent constant occurs.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [Fintype α] [Fintype β]

theorem sum_assignmentScalarWeight (b : α → ℝ) :
    (∑ r : α → Option β, assignmentScalarWeight b r) =
      ∏ q, (1 + (Fintype.card β : ℝ) * b q) := by
  classical
  unfold assignmentScalarWeight
  rw [← Fintype.prod_sum (fun (q : α) (i : Option β) => if i = none then 1 else b q)]
  simp [Fintype.sum_option]

theorem sum_marked_assignment_product (f : α → β → ℝ) (g : β → ℝ) (q : α) :
    (∑ r : α → β, (∏ t, f t (r t)) * g (r q)) =
      (∑ i, f q i * g i) * ∏ t ∈ Finset.univ.erase q, ∑ i, f t i := by
  classical
  calc
    _ = ∑ r : α → β, ∏ t, f t (r t) * (if t = q then g (r t) else 1) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ t, ∑ i, f t i * (if t = q then g i else 1) :=
      (Fintype.prod_sum (fun t i => f t i * (if t = q then g i else 1))).symm
    _ = _ := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun t => ∑ i, f t i * (if t = q then g i else 1)) (Finset.mem_univ q)]
      congr 1
      · simp
      · apply Finset.prod_congr rfl
        intro t ht
        simp only [if_neg (Finset.mem_erase.mp ht).1, mul_one]

omit [DecidableEq α] [Fintype β] in
theorem log_assignmentPrimeProduct {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (r : α → Option β) :
    Real.log (assignmentPrimeProduct p r) =
      ∑ q, if r q = none then 0 else Real.log (p q) := by
  classical
  rw [assignmentPrimeProduct, Nat.cast_prod, Real.log_prod (fun q _hq => by
    split_ifs
    · norm_num
    · exact_mod_cast (hp q).ne')]
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hq : r q = none <;> simp [hq]

theorem sum_assignmentScalarWeight_logProduct {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (b : α → ℝ) :
    (∑ r : α → Option β, assignmentScalarWeight b r * Real.log (assignmentPrimeProduct p r)) =
      ∑ q, ((Fintype.card β : ℝ) * b q * Real.log (p q)) *
        ∏ t ∈ Finset.univ.erase q, (1 + (Fintype.card β : ℝ) * b t) := by
  classical
  simp_rw [log_assignmentPrimeProduct hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  simp only [assignmentScalarWeight]
  rw [sum_marked_assignment_product (fun t (i : Option β) => if i = none then 1 else b t)
      (fun i => if i = none then 0 else Real.log (p q)) q]
  simp [Fintype.sum_option, mul_assoc]

theorem sum_assignmentScalarWeight_logProduct_le {p : α → ℕ} (hp : ∀ q, 0 < p q)
    {b : α → ℝ} (hb : ∀ q, 0 ≤ b q) :
    (∑ r : α → Option β, assignmentScalarWeight b r * Real.log (assignmentPrimeProduct p r)) ≤
      Real.exp (∑ q, (Fintype.card β : ℝ) * b q) *
        ∑ q, (Fintype.card β : ℝ) * b q * Real.log (p q) := by
  classical
  have hB (q : α) : 0 ≤ (Fintype.card β : ℝ) * b q := mul_nonneg (Nat.cast_nonneg _) (hb q)
  have hprod (q : α) :
      (∏ t ∈ Finset.univ.erase q, (1 + (Fintype.card β : ℝ) * b t)) ≤
        Real.exp (∑ t, (Fintype.card β : ℝ) * b t) := by
    calc
      _ ≤ ∏ t, (1 + (Fintype.card β : ℝ) * b t) :=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.erase_subset _ _)
          (fun t _ht => by linarith [hB t]) (fun t _ht _hnot => by linarith [hB t])
      _ ≤ _ := Real.prod_one_add_le_exp_sum _ hB
  rw [sum_assignmentScalarWeight_logProduct hp, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _hq
  calc
    _ ≤ ((Fintype.card β : ℝ) * b q * Real.log (p q)) *
        Real.exp (∑ t, (Fintype.card β : ℝ) * b t) :=
      mul_le_mul_of_nonneg_left (hprod q) (mul_nonneg (hB q) (Real.log_natCast_nonneg _))
    _ = _ := mul_comm _ _

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_assignmentScalarWeight
#print axioms Erdos4b.FGKMT.sum_assignmentScalarWeight_logProduct_le
