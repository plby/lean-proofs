/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceProxyAllocationBounds
import ErdosProblems.Erdos4b.ResidualPrimeFiberTail

/-!
# Total proxy allocation cost

The finite cofactor correction is bounded using the proved reciprocal
totient sum. Both the common slack and ceiling costs remain explicit.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem residualProxyEndpoint_le_totient {U y m : ℕ} (hm : 0 < m) :
    (U / m : ℕ) / residualCofactorLocalProduct y m ≤ 2 * (U : ℝ) / Nat.totient m := by
  rw [div_eq_mul_inv, ← residualCofactorInverseProduct_eq_inv]
  calc
    _ ≤ (U / m : ℕ) * (2 * ((m : ℝ) / Nat.totient m)) :=
      mul_le_mul_of_nonneg_left (residualCofactorInverseProduct_le_two_mul_ratio hm)
        (Nat.cast_nonneg _)
    _ = 2 * ((U / m : ℕ) * (m : ℝ)) / Nat.totient m := by ring
    _ ≤ 2 * (U : ℝ) / Nat.totient m :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (natDiv_cast_mul_le U m) (by norm_num))
        (Nat.cast_nonneg _)

theorem sum_residualProxyEndpoint_le {E : Finset ℕ} {U y B : ℕ}
    (hB : 1 ≤ B) (hE : ∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ B) :
    (∑ m ∈ E, (U / m : ℕ) / residualCofactorLocalProduct y m) ≤
      8 * (U : ℝ) * (1 + Real.log B) := by
  have hsub : E ⊆ Finset.Ioc 1 B := by
    intro m hm
    have hd := hE m hm
    have hm2 : 2 ≤ m := Nat.le_of_dvd hd.1 hd.2.1.two_dvd
    exact Finset.mem_Ioc.mpr ⟨by omega, hd.2.2⟩
  have htot : (∑ m ∈ Finset.Ioc 1 B, (1 : ℝ) / Nat.totient m) ≤
      4 * (1 + Real.log B) := by
    simpa only [Nat.cast_one, div_one, one_div] using
      sum_inv_totient_Ioc_le_four_mul_one_add_log_ratio (by norm_num : 0 < (1 : ℕ)) hB
  calc
    _ ≤ ∑ m ∈ E, 2 * (U : ℝ) / Nat.totient m :=
      Finset.sum_le_sum fun m hm ↦ residualProxyEndpoint_le_totient (hE m hm).1
    _ = 2 * (U : ℝ) * (∑ m ∈ E, (1 : ℝ) / Nat.totient m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ 2 * (U : ℝ) * (∑ m ∈ Finset.Ioc 1 B, (1 : ℝ) / Nat.totient m) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ ↦ by positivity)) (by positivity)
    _ ≤ 2 * (U : ℝ) * (4 * (1 + Real.log B)) :=
      mul_le_mul_of_nonneg_left htot (by positivity)
    _ = _ := by ring

theorem sum_sourceRequestedIntervalLength_residual_le
    {E : Finset ℕ} {U y B : ℕ} {ρ L slack : ℝ}
    (hB : 1 ≤ B) (hE : ∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ B)
    (hρ : 0 ≤ ρ) (hL : 0 ≤ L) (hslack : 0 ≤ slack) :
    (∑ m ∈ E, (sourceRequestedIntervalLength ρ (U / m : ℕ) L
      (residualCofactorLocalProduct y m) slack : ℝ)) ≤
      8 * ρ * U / L * (1 + Real.log B) + E.card * (slack + 1) := by
  have hfirst := sum_sourceRequestedIntervalLength_le E
    (fun m ↦ (U / m : ℕ)) (residualCofactorLocalProduct y) hρ hL hslack
    (fun m _ ↦ Nat.cast_nonneg _) (fun m hm ↦ (residualCofactorLocalProduct_pos (hE m hm).2.1).le)
  have hsum := sum_residualProxyEndpoint_le (U := U) (y := y) hB hE
  calc
    _ ≤ ρ / L * (∑ m ∈ E, (U / m : ℕ) / residualCofactorLocalProduct y m) +
        E.card * (slack + 1) := hfirst
    _ ≤ ρ / L * (8 * (U : ℝ) * (1 + Real.log B)) + E.card * (slack + 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (div_nonneg hρ hL)) le_rfl
    _ = _ := by ring

theorem sum_residualCofactorInverse_le {E : Finset ℕ} {y B : ℕ}
    (hB : 1 ≤ B) (hE : ∀ m ∈ E, 0 < m ∧ Even m ∧ m ≤ B) :
    (∑ m ∈ E, (1 : ℝ) / residualCofactorLocalProduct y m) ≤
      8 * (B : ℝ) * (1 + Real.log B) := by
  apply le_trans _ (sum_residualProxyEndpoint_le (U := B) (y := y) hB hE)
  apply Finset.sum_le_sum
  intro m hm
  have hquot : 1 ≤ B / m := Nat.le_div_iff_mul_le (hE m hm).1 |>.mpr (by
    simpa only [one_mul] using (hE m hm).2.2)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hquot)
    (residualCofactorLocalProduct_pos (hE m hm).2.1).le

theorem sum_residualProxyEndpoint_interval_le {E : Finset ℕ} {U y A B : ℕ}
    (hA : 0 < A) (hAB : A ≤ B) (hE : E ⊆ Finset.Ioc A B) :
    (∑ m ∈ E, (U / m : ℕ) / residualCofactorLocalProduct y m) ≤
      8 * (U : ℝ) * (1 + Real.log ((B : ℝ) / A)) := by
  have htot : (∑ m ∈ Finset.Ioc A B, (1 : ℝ) / Nat.totient m) ≤
      4 * (1 + Real.log ((B : ℝ) / A)) := by
    simpa only [one_div] using sum_inv_totient_Ioc_le_four_mul_one_add_log_ratio hA hAB
  calc
    _ ≤ ∑ m ∈ E, 2 * (U : ℝ) / Nat.totient m :=
      Finset.sum_le_sum fun m hm ↦ residualProxyEndpoint_le_totient
        (hA.trans (Finset.mem_Ioc.mp (hE hm)).1)
    _ = 2 * (U : ℝ) * (∑ m ∈ E, (1 : ℝ) / Nat.totient m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    _ ≤ 2 * (U : ℝ) * (∑ m ∈ Finset.Ioc A B, (1 : ℝ) / Nat.totient m) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hE (fun m _ _ ↦ by positivity)) (by positivity)
    _ ≤ 2 * (U : ℝ) * (4 * (1 + Real.log ((B : ℝ) / A))) :=
      mul_le_mul_of_nonneg_left htot (by positivity)
    _ = _ := by ring

end

end Erdos4b
