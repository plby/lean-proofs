import ErdosProblems.Erdos964.PrimeWeightedMultiples

/-!
# Uniform saving after summing the prime slices

Every endpoint lies above the common scale `L`, and `p * endpoint ≤ L²`.
Summing the available endpoint saving costs only the harmonic sum over `p`.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem sum_inv_subset_Ioc_le_one_add_log (L : ℕ) (P : Finset ℕ)
    (hP : P ⊆ Finset.Ioc 0 L) :
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ 1 + Real.log L := by
  have hIcc : P ⊆ Finset.Icc 1 L := by
    intro p hp
    exact Finset.mem_Icc.mpr (Finset.mem_Ioc.mp (hP hp))
  apply (Finset.sum_le_sum_of_subset_of_nonneg hIcc
    (fun p _ _ => inv_nonneg.mpr (Nat.cast_nonneg p))).trans
  have h := harmonic_le_one_add_log L
  rw [harmonic_eq_sum_Icc] at h
  simpa only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using h

theorem exists_prime_family_weighted_logSaving (a d m : ℕ) (hm : 0 < m)
    (θ : ℝ) (hθ : 0 < θ) (hθhalf : θ < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 4 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L → ∀ P : Finset ℕ, P ⊆ Finset.Ioc 0 L →
      ∀ F : ℕ → ℕ, (∀ p ∈ P, L ≤ F p ∧ p * F p ≤ L ^ 2) →
      ∀ S : ℕ → Finset ℕ,
        (∀ p ∈ P, S p ⊆ Finset.Ioc 0 (modulusCutoff θ (F p))) →
        (∀ p ∈ P, ∀ q ∈ S p, Squarefree q) →
      (∑ p ∈ P, ∑ q ∈ S p,
        ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy (F p) (m * q)) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_prime_weighted_multiples_logSaving (a + 1) d m hm θ hθ hθhalf
  refine ⟨2 * C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP F hF S hS hsq
  have hL4 : 4 ≤ L := hL₀.trans hL
  have hlogone := one_le_log_natCast hL4
  have hlogpos : 0 < Real.log (L : ℝ) := by linarith
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpoint (p : ℕ) (hp : p ∈ P) :
      (∑ q ∈ S p, ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy (F p) (m * q)) ≤
        (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) * (p : ℝ)⁻¹ := by
    have hpp : (0 : ℝ) < p := by exact_mod_cast (Finset.mem_Ioc.mp (hP hp)).1
    have hFp : (0 : ℝ) < F p := hLp.trans_le (by exact_mod_cast (hF p hp).1)
    have hlogs : Real.log (L : ℝ) ≤ Real.log (F p : ℝ) :=
      Real.log_le_log hLp (by exact_mod_cast (hF p hp).1)
    have hvalue : (F p : ℝ) ≤ (L : ℝ) ^ 2 / p := by
      apply (le_div_iff₀ hpp).mpr
      have h := (hF p hp).2
      have hR : (p : ℝ) * F p ≤ (L : ℝ) ^ 2 := by exact_mod_cast h
      simpa only [mul_comm] using hR
    calc
      _ ≤ C * (F p : ℝ) / (Real.log (F p : ℝ)) ^ (a + 1) :=
        hbound (F p) (hL.trans (hF p hp).1) (S p) (hS p hp) (hsq p hp)
      _ ≤ C * (F p : ℝ) / (Real.log (L : ℝ)) ^ (a + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hlogpos.le hlogs (a + 1))
      _ ≤ C * ((L : ℝ) ^ 2 / p) / (Real.log (L : ℝ)) ^ (a + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvalue hC) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ P, (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) * (p : ℝ)⁻¹ :=
      Finset.sum_le_sum hpoint
    _ = (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) * ∑ p ∈ P, (p : ℝ)⁻¹ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) * (1 + Real.log L) :=
      mul_le_mul_of_nonneg_left (sum_inv_subset_Ioc_le_one_add_log L P hP) (by positivity)
    _ ≤ (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (a + 1)) * (2 * Real.log L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by
      rw [pow_add, pow_one]
      field_simp

end Erdos964
