import ErdosProblems.Erdos964.SemiprimeWeightedDistribution

/-!
# Arbitrary logarithmic saving with divisor weights

The distribution estimate remains valid after multiplication by `d^ω(q)`
on any subset of squarefree moduli in the permitted range.
-/

namespace Erdos964

open scoped BigOperators ArithmeticFunction.omega
open BoundedGaps.Maynard

theorem weighted_semiprime_sqrt_envelope_le {C L l t : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hl : 0 < l) (ht : 0 ≤ t) (htl : t ≤ 2 * l)
    (a k : ℕ) :
    Real.sqrt (2 * L ^ 2 * t ^ (2 * k)) *
        Real.sqrt (C * L ^ 2 / l ^ (2 * (a + k))) ≤
      (2 * 2 ^ k * Real.sqrt C) * L ^ 2 / l ^ a := by
  have hpow (x : ℝ) (n : ℕ) : x ^ (2 * n) = (x ^ n) ^ 2 := by
    rw [Nat.mul_comm 2 n, pow_mul]
  have hfirst : Real.sqrt (2 * L ^ 2 * t ^ (2 * k)) ≤
      2 * L * (2 * l) ^ k := by
    rw [hpow]
    have hid : 2 * L ^ 2 * (t ^ k) ^ 2 = 2 * (L * t ^ k) ^ 2 := by ring
    rw [hid, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq (by positivity)]
    have htwo : Real.sqrt 2 ≤ (2 : ℝ) := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
    calc
      _ ≤ 2 * (L * t ^ k) := mul_le_mul_of_nonneg_right htwo (by positivity)
      _ ≤ 2 * L * (2 * l) ^ k := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htl k) (by positivity)
  have hsecond : Real.sqrt (C * L ^ 2 / l ^ (2 * (a + k))) =
      Real.sqrt C * L / l ^ (a + k) := by
    rw [hpow, Real.sqrt_div (by positivity), Real.sqrt_mul hC,
      Real.sqrt_sq hL, Real.sqrt_sq (by positivity)]
  rw [hsecond]
  calc
    _ ≤ (2 * L * (2 * l) ^ k) * (Real.sqrt C * L / l ^ (a + k)) :=
      mul_le_mul_of_nonneg_right hfirst (by positivity)
    _ = _ := by
      rw [mul_pow, pow_add]
      field_simp

theorem exists_semiprimesAtScale_weighted_logSaving (a d : ℕ) (η θ : ℝ)
    (hη : 0 < η) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L₀ : ℕ, 16 ≤ L₀ ∧
      ∀ L : ℕ, L₀ ≤ L →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ≤ L) →
        (∀ p ∈ P, Real.rpow (L : ℝ) η < p) →
      ∀ S : Finset ℕ, S ⊆ Finset.Ioc 0 (modulusCutoff θ L) →
        (∀ q ∈ S, Squarefree q) →
      (∑ q ∈ S, ((d ^ ω q : ℕ) : ℝ) * semiprimeScaleMaxDiscrepancy P L q) ≤
        C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ a := by
  obtain ⟨C, hC, L₀, hL₀, hbound⟩ :=
    exists_semiprimesAtScale_max_logSaving (2 * (a + d ^ 2)) η θ hη hθ hθ1
  refine ⟨2 * 2 ^ (d ^ 2) * Real.sqrt C, by positivity, L₀, hL₀, ?_⟩
  intro L hL P hP hPL hPlower S hS hsq
  have hL16 : 16 ≤ L := hL₀.trans hL
  have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hlogone := one_le_log_natCast (show 4 ≤ L by omega)
  have hlog : 0 < Real.log (L : ℝ) := by linarith
  have hcut : modulusCutoff θ L ≤ L := by
    have hreal : (modulusCutoff θ L : ℝ) ≤ L :=
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg L) θ)).trans
        (Real.rpow_le_self_of_one_le hLone hθ1.le)
    exact_mod_cast hreal
  have hSL : S ⊆ Finset.Icc 1 L := by
    intro q hq
    have hqb := Finset.mem_Ioc.mp (hS hq)
    exact Finset.mem_Icc.mpr ⟨hqb.1, hqb.2.trans hcut⟩
  have hsum : (∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L q) ≤
      C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (2 * (a + d ^ 2)) := by
    apply le_trans _ (hbound L hL P hP hPL hPlower)
    exact Finset.sum_le_sum_of_subset_of_nonneg hS
      (fun q _ _ => semiprimeScaleMaxDiscrepancy_nonneg P L q)
  calc
    _ ≤ Real.sqrt (2 * (L : ℝ) ^ 2 * (1 + Real.log L) ^ (2 * d ^ 2)) *
        Real.sqrt (∑ q ∈ S, semiprimeScaleMaxDiscrepancy P L q) :=
      semiprimeScale_weighted_discrepancy_le P L d L S
        (fun p hp => (hP p hp).pos) hSL hsq (by nlinarith)
    _ ≤ Real.sqrt (2 * (L : ℝ) ^ 2 * (1 + Real.log L) ^ (2 * d ^ 2)) *
        Real.sqrt (C * (L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ (2 * (a + d ^ 2))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)
    _ ≤ _ := weighted_semiprime_sqrt_envelope_le hC (Nat.cast_nonneg L) hlog
      (by linarith) (by linarith) a (d ^ 2)

end Erdos964
