/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierSourceCoefficient

/-!
# Exact physical normalization on the analytic divisor support

The full finite pre-sieved weight sum is the literal interval length
times the physical density and coordinate lcm kernel, plus the CRT
endpoint error. No within-family or cross-family coprimality is added
to the divisor support.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem cutoffDivisorTupleSupport_coordinate_pos
    {ι : Type*} [Fintype ι] {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {d : ι → ℕ} (hd : d ∈ cutoffDivisorTupleSupport ι P) (i : ι) : 0 < d i :=
  Nat.pos_of_dvd_of_pos ((mem_cutoffDivisorTupleSupport P hP d).mp hd i)
    (primeFinsetProduct_pos P hP)

theorem cutoffDoubledGeneralSupport
    (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    DoubledSelbergGeneralSupport H (cutoffDivisorTupleSupport H P)
      (cutoffCompanionDivisorTupleSupport H P m) m := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro d hd d' hd' i
    exact Nat.lcm_pos (cutoffDivisorTupleSupport_coordinate_pos hP hd i)
      (cutoffDivisorTupleSupport_coordinate_pos hP hd' i)
  · intro e he e' he' i
    exact Nat.lcm_pos
      (cutoffDivisorTupleSupport_coordinate_pos hP (Finset.mem_filter.mp he).1 i)
      (cutoffDivisorTupleSupport_coordinate_pos hP (Finset.mem_filter.mp he').1 i)
  · intro e he e' he' i
    exact (coprime_nat_lcm_iff m _ _).mpr
      ⟨(Finset.mem_filter.mp he).2 i, (Finset.mem_filter.mp he').2 i⟩

theorem cutoffDivisorTupleSupport_coordinate_coprime_primorial
    {ι : Type*} [Fintype ι] {P : Finset ℕ} {w : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hrough : ∀ p ∈ P, w < p)
    {d : ι → ℕ} (hd : d ∈ cutoffDivisorTupleSupport ι P) (i : ι) :
    (primorial w).Coprime (d i) := by
  apply Nat.coprime_of_dvd
  intro p hp hpw hpdiv
  have hpP := (prime_dvd_primeFinsetProduct_iff P hP hp).mp
    (hpdiv.trans ((mem_cutoffDivisorTupleSupport P hP d).mp hd i))
  exact (not_lt_of_ge (hp.dvd_primorial_iff.mp hpw)) (hrough p hpP)

theorem doubledSelbergGeneralNormalizationMain_eq_of_preSieve_coprime
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (W m q T : ℕ)
    (hWcop : ∀ d ∈ D, ∀ e ∈ E, ∀ d' ∈ D, ∀ e' ∈ E,
      ∀ i : LargeGapCrtIndex H, W.Coprime (largeGapCrtModulus H d e d' e' i)) :
    doubledSelbergGeneralNormalizationMain H D E lambda W m q T =
      (((allowedPreSieveResidues W m).card : ℝ) * (T : ℝ) / W) *
        doubledSelbergCoordinateLcmKernel H D E lambda m q := by
  classical
  unfold doubledSelbergGeneralNormalizationMain doubledSelbergCoordinateLcmKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d' hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e' he'
  have hcop := hWcop d hd e he d' hd' e' he'
  rw [sum_largeGapGeneralCrtClassMain_eq H W m q T d e d' e' hcop]
  by_cases hc : LargeGapCoordinateCrtCompatible H m q d e d' e'
  · rw [if_pos hc, if_pos hc, largeGapGeneralCrtModulus_eq_mul H W d e d' e' hcop]
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv]
    ring
  · simp only [if_neg hc, mul_zero]

theorem preSievedCutoffDoubledWeightSum_eq_lcmKernel_add_error
    (H P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (w m q T : ℕ)
    (hw : 2 ≤ w) (hm : 0 < m) (hrough : ∀ p ∈ P, w < p)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) :
    (∑ n ∈ Finset.Icc 0 T,
      if largeGapPreSieved w m n then
        doubledSelbergWeight H (cutoffDivisorTupleSupport H P)
          (cutoffCompanionDivisorTupleSupport H P m) lambda m q n else 0) =
      (T : ℝ) * preSieveDensity w m *
        doubledSelbergCoordinateLcmKernel H (cutoffDivisorTupleSupport H P)
          (cutoffCompanionDivisorTupleSupport H P m) lambda m q +
      doubledSelbergGeneralNormalizationError H (cutoffDivisorTupleSupport H P)
        (cutoffCompanionDivisorTupleSupport H P m) lambda (primorial w) m q T := by
  classical
  rw [preSievedDoubledWeightSum_eq_generalMain_add_error H
    (cutoffDivisorTupleSupport H P) (cutoffCompanionDivisorTupleSupport H P m)
    lambda w m q T hw hm (cutoffDoubledGeneralSupport H P hP m)]
  have hcop : ∀ d ∈ cutoffDivisorTupleSupport H P,
      ∀ e ∈ cutoffCompanionDivisorTupleSupport H P m,
      ∀ d' ∈ cutoffDivisorTupleSupport H P,
      ∀ e' ∈ cutoffCompanionDivisorTupleSupport H P m,
      ∀ i : LargeGapCrtIndex H, (primorial w).Coprime (largeGapCrtModulus H d e d' e' i) := by
    intro d hd e he d' hd' e' he' i
    cases i with
    | inl i =>
        exact (coprime_nat_lcm_iff _ _ _).mpr
          ⟨cutoffDivisorTupleSupport_coordinate_coprime_primorial hP hrough hd i,
            cutoffDivisorTupleSupport_coordinate_coprime_primorial hP hrough hd' i⟩
    | inr i =>
        exact (coprime_nat_lcm_iff _ _ _).mpr
          ⟨cutoffDivisorTupleSupport_coordinate_coprime_primorial hP hrough
            (Finset.mem_filter.mp he).1 i,
            cutoffDivisorTupleSupport_coordinate_coprime_primorial hP hrough
              (Finset.mem_filter.mp he').1 i⟩
  rw [doubledSelbergGeneralNormalizationMain_eq_of_preSieve_coprime _ _ _ _ _ _ _ _ hcop]
  rw [mul_div_right_comm, card_allowedPreSieveResidues_div_primorial hw hm]
  ring

end

end Erdos4b
