/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos851.FiniteCombinatorialSieve
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic bounds for finite sieve products

The beta-sieve boundary estimate needs the elementary comparison between
the sum of local densities and the logarithm of the corresponding inverse
Euler product.  This file keeps that real-analysis bookkeeping independent
of the ordered-chain combinatorics.
-/

namespace Erdos851

open FiniteCombinatorialSieve

/-- For a local density in `[0,1)`, its value is at most the negative
logarithm of the complementary local factor. -/
theorem le_neg_log_one_sub {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.mpr hx1
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

/-- The sum of local densities over a finite ordered list is at most the
logarithm of its inverse Euler product. -/
theorem list_sum_le_log_finiteEulerProduct_inv
    {ι : Type*} (g : ι → ℝ) (P : List ι)
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg1 : ∀ p ∈ P, g p < 1) :
    (P.map g).sum ≤ Real.log (finiteEulerProduct g P)⁻¹ := by
  have hterm : ∀ x ∈ P.map g, x ≤ -Real.log (1 - x) := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact le_neg_log_one_sub (hg0 p hp) (hg1 p hp)
  have hfactor : ∀ x ∈ P.map (fun p => 1 - g p), x ≠ 0 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact (sub_pos.mpr (hg1 p hp)).ne'
  have hneg : ∀ Q : List ι,
      ((Q.map g).map fun x => -Real.log (1 - x)).sum =
        -((Q.map fun p => Real.log (1 - g p)).sum) := by
    intro Q
    induction Q with
    | nil => simp
    | cons p Q ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  have hsum : ∀ Q : List ℝ,
      (∀ x ∈ Q, x ≤ -Real.log (1 - x)) →
      Q.sum ≤ (Q.map fun x => -Real.log (1 - x)).sum := by
    intro Q hQ
    induction Q with
    | nil => simp
    | cons x Q ih =>
        simp only [List.sum_cons, List.map_cons]
        exact add_le_add (hQ x (by simp))
          (ih fun y hy => hQ y (by simp [hy]))
  calc
    (P.map g).sum ≤ ((P.map g).map fun x => -Real.log (1 - x)).sum :=
      hsum (P.map g) hterm
    _ = -((P.map fun p => Real.log (1 - g p)).sum) := hneg P
    _ = -Real.log (finiteEulerProduct g P) := by
      have hmap :
          (P.map fun p => Real.log (1 - g p)).sum =
            ((P.map fun p => 1 - g p).map Real.log).sum := by
        rw [List.map_map]
        apply congrArg List.sum
        exact List.map_congr_left fun _ _ => rfl
      rw [finiteEulerProduct, Real.log_list_prod hfactor]
      rw [hmap]
    _ = Real.log (finiteEulerProduct g P)⁻¹ := by
      rw [Real.log_inv]

/-- A product-ratio upper bound immediately yields the logarithmic mass
bound used in the elementary-symmetric estimate. -/
theorem list_sum_le_log_of_finiteEulerProduct_inv_le
    {ι : Type*} (g : ι → ℝ) (P : List ι) {B : ℝ}
    (hg0 : ∀ p ∈ P, 0 ≤ g p) (hg1 : ∀ p ∈ P, g p < 1)
    (hprodPos : 0 < (finiteEulerProduct g P)⁻¹)
    (hB : (finiteEulerProduct g P)⁻¹ ≤ B) :
    (P.map g).sum ≤ Real.log B := by
  exact (list_sum_le_log_finiteEulerProduct_inv g P hg0 hg1).trans
    (Real.log_le_log hprodPos hB)

end Erdos851
