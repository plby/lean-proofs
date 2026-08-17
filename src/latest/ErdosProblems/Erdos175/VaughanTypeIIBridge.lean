/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.Phase
import ErdosProblems.Erdos175.TypeII
import ErdosProblems.Erdos175.VaughanTypeIIExpansion

/-!
# The Type-II Vaughan terms as reciprocal bilinear sums

The product-restricted kernel in `TypeII` is the analytic form used in
Granville--Ramaré, Proposition 9.4.  This file identifies it exactly with
the two Type-II terms in the four-sum Vaughan decomposition.  It is kept as
a separate bridge so neither the algebraic Vaughan development nor the
generic Type-II estimates acquire a circular dependency.
-/

noncomputable section

namespace Erdos175.VaughanTypeIIBridge

open scoped ArithmeticFunction BigOperators
open Vaughan VaughanFourSums VaughanTypeIIExpansion

private lemma vaughan_reciprocalPhase_eq_e (x : ℝ) (n : ℕ) :
    Vaughan.reciprocalPhase x n = e (x / (n : ℝ)) := by
  unfold Vaughan.reciprocalPhase e
  congr 1

/-- The `Σ₂,₂` term is the reciprocal bilinear sum with outer coefficient
`b_r` and inner coefficient one.  The rectangular inner support `[1,y']`
is cut down to the exact hyperbolic interval by the kernel. -/
theorem sigma22_eq_reciprocalBilinearSum
    (y y' M K : ℕ) (x : ℝ) :
    sigma22 (Finset.Ioc y y') (Vaughan.reciprocalPhase x) M K =
      TypeII.reciprocalBilinearSum
        (Finset.Ioc y y') (Finset.Ioc M (M * K)) (Finset.Icc 1 y') x
        (fun r => (bCoeff M K r : ℂ)) (fun _ => 1) := by
  rw [sigma22_Ioc_eq_outer, TypeII.reciprocalBilinearSum_eq]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrpos : 0 < r := by
    have := (Finset.mem_Ioc.mp hr).1
    omega
  rw [← innerProductInterval_eq_Ioc y y' r hrpos]
  unfold innerProductInterval
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  simp only [Finset.mem_Ioc]
  by_cases hprod : y < r * l ∧ r * l ≤ y'
  · rw [if_pos hprod, if_pos hprod]
    rw [vaughan_reciprocalPhase_eq_e]
    ring
  · rw [if_neg hprod, if_neg hprod]

/-- The `Σ₃` term is the reciprocal bilinear sum with outer coefficient
`a_l` and inner von Mangoldt coefficient.  The support `(K,y']`, together
with the product-restricted kernel, is exactly the interval
`(max K (y/l), y'/l]` in the expanded Vaughan term. -/
theorem sigma3_eq_reciprocalBilinearSum
    (y y' M K : ℕ) (x : ℝ) :
    sigma3 (Finset.Ioc y y') (Vaughan.reciprocalPhase x) M K =
      TypeII.reciprocalBilinearSum
        (Finset.Ioc y y') (Finset.Ioc M y') (Finset.Ioc K y') x
        (fun l => (aCoeff M l : ℂ))
        (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) := by
  rw [sigma3_Ioc_eq_outer, TypeII.reciprocalBilinearSum_eq]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hlpos : 0 < l := by
    have := (Finset.mem_Ioc.mp hl).1
    omega
  have hset :
      (Finset.Ioc K y').filter (fun k => l * k ∈ Finset.Ioc y y') =
        Finset.Ioc (max K (y / l)) (y' / l) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkI, hprodI⟩ := Finset.mem_filter.mp hk
      have hkI' := Finset.mem_Ioc.mp hkI
      have hprodI' := Finset.mem_Ioc.mp hprodI
      apply Finset.mem_Ioc.mpr
      constructor
      · rw [max_lt_iff]
        exact ⟨hkI'.1, (Nat.div_lt_iff_lt_mul hlpos).2
          (by simpa [Nat.mul_comm] using hprodI'.1)⟩
      · exact (Nat.le_div_iff_mul_le hlpos).2
          (by simpa [Nat.mul_comm] using hprodI'.2)
    · intro hk
      have hk' := Finset.mem_Ioc.mp hk
      have hklow := (max_lt_iff.mp hk'.1)
      have hprodLow : y < l * k :=
        by simpa [Nat.mul_comm] using
          (Nat.div_lt_iff_lt_mul hlpos).1 hklow.2
      have hprodHigh : l * k ≤ y' :=
        by simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hlpos).1 hk'.2
      have hky' : k ≤ y' :=
        (Nat.le_mul_of_pos_left k hlpos).trans hprodHigh
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr ⟨hklow.1, hky'⟩,
          Finset.mem_Ioc.mpr ⟨hprodLow, hprodHigh⟩⟩
  rw [← hset, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hprod : l * k ∈ Finset.Ioc y y'
  · rw [if_pos hprod, if_pos hprod]
    rw [vaughan_reciprocalPhase_eq_e]
    simp only [Nat.mul_comm]
  · rw [if_neg hprod, if_neg hprod]

#print axioms sigma22_eq_reciprocalBilinearSum
#print axioms sigma3_eq_reciprocalBilinearSum

end Erdos175.VaughanTypeIIBridge
