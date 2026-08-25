import ErdosProblems.Erdos964.SemiprimeBombieriVinogradov
import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy

/-!
# Divisor-weighted distribution of separated semiprimes

The squarefree divisor multiplicities arising in the sieve are absorbed
by Cauchy--Schwarz, a reciprocal-totient moment, and the unweighted
semiprime distribution theorem.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem finiteResidueCount_le_div_add_one (S : Finset ℕ) (N q a : ℕ)
    (hS : S ⊆ Finset.Icc 1 N) (hq : 0 < q) :
    (finiteResidueCount S q a : ℝ) ≤ (N : ℝ) / q + 1 := by
  have hsub : S.filter (fun n => n ≡ a [MOD q]) ⊆
      (Finset.Ico 1 (N + 1)).filter (fun n => n ≡ a [MOD q]) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnb := Finset.mem_Icc.mp (hS hn'.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hnb.1, by omega⟩, hn'.2⟩
  have hcard : (finiteResidueCount S q a : ℝ) ≤
      (((Finset.Ico 1 (N + 1)).filter (fun n => n ≡ a [MOD q])).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have herr := (abs_le.mp (intervalModEqCardError_abs_le_one 1 (N + 1) q a
    (by omega) hq)).2
  rw [intervalModEq_card_eq_length_div_add_error] at hcard
  push_cast at hcard
  simp only [add_sub_cancel_right] at hcard
  linarith

theorem finiteResidueCount_discrepancy_le_two_mul_div (S : Finset ℕ) (N q a : ℕ)
    (hS : S ⊆ Finset.Icc 1 N) (hq : 0 < q) (hqN : q ≤ N) :
    |(finiteResidueCount S q a : ℝ) - (S.card : ℝ) / q.totient| ≤
      2 * (N : ℝ) / q.totient := by
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hφN : (q.totient : ℝ) ≤ N := by exact_mod_cast (Nat.totient_le q).trans hqN
  have hcard : (S.card : ℝ) ≤ N := by
    have := Finset.card_le_card hS
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hcount := finiteResidueCount_le_div_add_one S N q a hS hq
  have hdiv : (N : ℝ) / q ≤ (N : ℝ) / q.totient :=
    div_le_div₀ (by positivity) le_rfl hφ hφq
  have hone : (1 : ℝ) ≤ (N : ℝ) / q.totient := (one_le_div₀ hφ).mpr hφN
  have htotal := div_le_div_of_nonneg_right hcard hφ.le
  have htotal0 : (0 : ℝ) ≤ (S.card : ℝ) / q.totient := by positivity
  have hcount0 : (0 : ℝ) ≤ finiteResidueCount S q a := by positivity
  rw [mul_div_assoc, abs_sub_le_iff]
  constructor <;> linarith

theorem semiprimesAtScale_subset_Icc (P : Finset ℕ) (L X : ℕ)
    (hP : ∀ p ∈ P, 0 < p) : semiprimesAtScale P L X ⊆ Finset.Icc 1 X := by
  intro n hn
  obtain ⟨⟨p, r⟩, hpr, rfl⟩ := Finset.mem_image.mp hn
  have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hpr).1
  have hr := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmem.2).1).1
  exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (hP p hmem.1) (by omega),
    (Finset.mem_filter.mp hpr).2⟩

theorem semiprimeScaleMaxDiscrepancy_le_two_mul_div
    (P : Finset ℕ) (L q : ℕ) (hP : ∀ p ∈ P, 0 < p)
    (hq : 0 < q) (hqL : q ≤ L ^ 2) :
    semiprimeScaleMaxDiscrepancy P L q ≤ 2 * (L : ℝ) ^ 2 / q.totient := by
  have hL : 0 < L := by nlinarith
  obtain ⟨x, a, hx, _, hmax⟩ := semiprimeScaleMaxDiscrepancy_attained P hL hq
  rw [hmax]
  have hsub : semiprimesAtScale P L x ⊆ Finset.Icc 1 (L ^ 2) :=
    (semiprimesAtScale_subset_Icc P L x hP).trans
      (Finset.Icc_subset_Icc le_rfl (Finset.mem_Icc.mp hx).2)
  simpa only [Nat.cast_pow] using
    finiteResidueCount_discrepancy_le_two_mul_div _ (L ^ 2) q a hsub hq hqL

theorem semiprimeScale_weighted_discrepancy_le
    (P : Finset ℕ) (L d Q : ℕ) (S : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hSQ : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q) (hQL : Q ≤ L ^ 2) :
    (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * semiprimeScaleMaxDiscrepancy P L q) ≤
      Real.sqrt (2 * (L : ℝ) ^ 2 * (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L q) := by
  have hweighted := sum_weight_mul_le_sqrt_of_pointwise_div S
    (fun q => ((d ^ ω q : ℕ) : ℝ)) (semiprimeScaleMaxDiscrepancy P L)
    (fun q => (q.totient : ℝ)) (2 * (L : ℝ) ^ 2)
    (fun q _ => semiprimeScaleMaxDiscrepancy_nonneg P L q)
    (fun q hq => semiprimeScaleMaxDiscrepancy_le_two_mul_div P L q hP
      (by have := (Finset.mem_Icc.mp (hSQ hq)).1; omega)
      ((Finset.mem_Icc.mp (hSQ hq)).2.trans hQL))
  apply hweighted.trans
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left
    (sum_tauPow_sq_div_totient_le_one_add_log d Q S hSQ hsq) (by positivity)

end Erdos964
