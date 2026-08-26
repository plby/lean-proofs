/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.LargeGcdPrimeStructure
import ErdosProblems.Erdos822.IntegerResidueBlocks
import ErdosProblems.Erdos822.LargeGcdFreeBasic
import ErdosProblems.Erdos822.HarmonicElementary

/-!
# A direct B4 layer at cutoff N^4

For a structured cofactor k*r*q, a prime above N^4 that divides both the
cofactor and its totient forces r ∣ q-1.  The latter is a single residue
class for q modulo r, so its reciprocal mass is small.
-/

namespace Erdos822

open scoped BigOperators

/-- Cofactors failing B4 at the concrete cutoff N^4. -/
noncomputable def largeCutoffBadOddCofactors (N : ℕ) : Finset ℕ := by
  classical
  exact (oddRawCofactors N).filter fun m =>
    ∃ p : ℕ, p.Prime ∧ N ^ 4 < p ∧
      p ∣ m ∧ p ∣ Nat.totient m

@[simp]
theorem mem_largeCutoffBadOddCofactors_iff
    {N m : ℕ} :
    m ∈ largeCutoffBadOddCofactors N ↔
      m ∈ oddRawCofactors N ∧
        ∃ p : ℕ, p.Prime ∧ N ^ 4 < p ∧
          p ∣ m ∧ p ∣ Nat.totient m := by
  simp [largeCutoffBadOddCofactors]

/-- Structured cofactors for which the middle prime divides q-1. -/
def middlePredLargeCofactors (N : ℕ) : Finset ℕ :=
  ((oddCofactorTriples N).filter fun t => t.2.1 ∣ t.2.2 - 1).image
    cofactorProduct

@[simp]
theorem mem_middlePredLargeCofactors_iff
    {N m : ℕ} :
    m ∈ middlePredLargeCofactors N ↔
      ∃ k r q : ℕ,
        (k, r, q) ∈ oddCofactorTriples N ∧
          r ∣ q - 1 ∧ m = k * r * q := by
  constructor
  · intro hm
    rw [middlePredLargeCofactors, Finset.mem_image] at hm
    obtain ⟨⟨k, r, q⟩, ht, rfl⟩ := hm
    have htData := Finset.mem_filter.mp ht
    exact ⟨k, r, q, htData.1, htData.2, rfl⟩
  · rintro ⟨k, r, q, ht, hrq, rfl⟩
    rw [middlePredLargeCofactors, Finset.mem_image]
    exact ⟨(k, r, q), Finset.mem_filter.mpr ⟨ht, hrq⟩, rfl⟩

/-- Every large-cutoff B4 failure lies in the explicit r ∣ q-1
exceptional family. -/
theorem largeCutoffBadOddCofactors_subset_middlePredLarge
    {N : ℕ} (hN : 2 ≤ N) :
    largeCutoffBadOddCofactors N ⊆ middlePredLargeCofactors N := by
  intro m hm
  have hmData := mem_largeCutoffBadOddCofactors_iff.mp hm
  obtain ⟨p, hp, hpN, hpm, hpφ⟩ := hmData.2
  rw [oddRawCofactors] at hmData
  simp only [Finset.mem_image] at hmData
  obtain ⟨⟨k, r, q⟩, ht, hmeq⟩ := hmData.1
  rw [mem_oddCofactorTriples_iff] at ht
  rw [mem_middlePredLargeCofactors_iff]
  refine ⟨k, r, q, ?_, ?_, hmeq.symm⟩
  · rw [mem_oddCofactorTriples_iff]
    exact ht
  · apply middle_dvd_large_pred_of_large_common_totient
      hN hp hpN ht.1 ht.2.1 ht.2.2
    · rw [← hmeq] at hpm
      simpa [cofactorProduct] using hpm
    · rw [← hmeq] at hpφ
      simpa [cofactorProduct] using hpφ

/-- The good concrete-cutoff B4 layer is the complement of the preceding
bad family inside the odd raw cofactors. -/
noncomputable def largeCutoffGoodOddCofactors (N : ℕ) : Finset ℕ := by
  classical
  exact (oddRawCofactors N).filter fun m =>
    ∀ p : ℕ, p.Prime → N ^ 4 < p →
      ¬ (p ∣ m ∧ p ∣ Nat.totient m)

@[simp]
theorem mem_largeCutoffGoodOddCofactors_iff
    {N m : ℕ} :
    m ∈ largeCutoffGoodOddCofactors N ↔
      m ∈ oddRawCofactors N ∧
        ∀ p : ℕ, p.Prime → N ^ 4 < p →
          ¬ (p ∣ m ∧ p ∣ Nat.totient m) := by
  simp [largeCutoffGoodOddCofactors]

theorem largeCutoffGoodOddCofactors_eq_largeGcdFree
    (N : ℕ) :
    largeCutoffGoodOddCofactors N =
      largeGcdFreeOddCofactors N (N ^ 4) := by
  ext m
  simp [largeCutoffGoodOddCofactors, largeGcdFreeOddCofactors]

/-- Exact triple expansion of the reciprocal mass of the r ∣ q-1
exceptional family. -/
theorem sum_inv_middlePredLargeCofactors_eq_triple
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m =
      ∑ k ∈ oddSmallFactors N,
        ∑ r ∈ middlePrimes N,
          ∑ q ∈ (largePrimes N).filter fun q => r ∣ q - 1,
            (1 : ℝ) / (k * r * q) := by
  unfold middlePredLargeCofactors
  rw [Finset.sum_image
    ((cofactorProduct_injOn_oddCofactorTriples hN).mono
      (Finset.filter_subset _ _))]
  rw [oddCofactorTriples]
  change
    (∑ t ∈ (oddSmallFactors N ×ˢ (middlePrimes N ×ˢ largePrimes N)).filter
        (fun t => t.2.1 ∣ t.2.2 - 1),
      (1 : ℝ) / cofactorProduct t) = _
  rw [Finset.sum_filter]
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_filter]
  simp [cofactorProduct]

/-- The q-fiber cut out by r ∣ q-1 lies in one large-prime residue class
modulo r. -/
theorem largePrimes_filter_middle_dvd_pred_subset_residueClass
    {N r : ℕ} (hN : 2 ≤ N) (hr : r ∈ middlePrimes N) :
    (largePrimes N).filter (fun q => r ∣ q - 1) ⊆
      largePrimeResidueClass N r 1 (N ^ 4) := by
  intro q hq
  have hqData := Finset.mem_filter.mp hq
  rw [mem_largePrimeResidueClass_iff]
  have hqge : N ^ 21 ≤ q := (mem_largePrimes_iff.mp hqData.1).1
  have hN4N21 : N ^ 4 < N ^ 21 :=
    Nat.pow_lt_pow_right (by omega : 1 < N) (by omega)
  have hmod : q ≡ 1 [MOD r] := by
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ q)).2 hqData.2).symm
  exact ⟨hqData.1, hN4N21.trans_le hqge, hmod⟩

/-- The reciprocal q-mass of the r ∣ q-1 fiber has the expected
inverse-r main term. -/
theorem sum_inv_largePrimes_filter_middle_dvd_pred_le
    {N r : ℕ} (hN : 2 ≤ N) (hr : r ∈ middlePrimes N) :
    ∑ q ∈ (largePrimes N).filter (fun q => r ∣ q - 1),
        (1 : ℝ) / q ≤
      ((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) := by
  calc
    (∑ q ∈ (largePrimes N).filter (fun q => r ∣ q - 1),
        (1 : ℝ) / q) ≤
        ∑ q ∈ largePrimeResidueClass N r 1 (N ^ 4),
          (1 : ℝ) / q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (largePrimes_filter_middle_dvd_pred_subset_residueClass hN hr)
      intro q hq hnot
      positivity
    _ ≤ ((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) *
        (harmonic N : ℝ) :=
      sum_inv_largePrimeResidueClass_le_harmonic_of_pos hN
        (mem_middlePrimes_iff.mp hr).2.2.pos

/-- The reciprocal-square mass of middle-layer primes is at most
1/N^4. -/
theorem sum_inv_sq_middlePrimes_le_inv_pow_four
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ r ∈ middlePrimes N, (1 : ℝ) / (r ^ 2 : ℕ) ≤
      (1 : ℝ) / (N ^ 4 : ℕ) := by
  have hsubset : middlePrimes N ⊆ Finset.Ioc (N ^ 4) (N ^ 5) := by
    intro r hr
    have hrData := mem_middlePrimes_iff.mp hr
    rw [Finset.mem_Ioc]
    refine ⟨?_, hrData.2.1⟩
    have hne : r ≠ N ^ 4 := by
      intro heq
      rw [heq] at hrData
      exact (Nat.Prime.not_prime_pow (by omega : 2 ≤ 4)) hrData.2.2
    omega
  calc
    (∑ r ∈ middlePrimes N, (1 : ℝ) / (r ^ 2 : ℕ)) ≤
        ∑ r ∈ Finset.Ioc (N ^ 4) (N ^ 5),
          (1 : ℝ) / (r ^ 2 : ℕ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro r hr hnot
      positivity
    _ ≤ (1 : ℝ) / (N ^ 4 : ℕ) -
        (1 : ℝ) / (N ^ 5 : ℕ) := by
      have hpow : N ^ 4 ≤ N ^ 5 :=
        Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
      have h :=
        (sum_Ioc_inv_sq_le_sub (α := ℝ) (k := N ^ 4)
          (n := N ^ 5) (by positivity) hpow)
      norm_num only [one_div, Nat.cast_pow] at h ⊢
      push_cast at h
      exact h
    _ ≤ (1 : ℝ) / (N ^ 4 : ℕ) := by
      have hnonneg : 0 ≤ (1 : ℝ) / (N ^ 5 : ℕ) := by positivity
      linarith

/-- The full reciprocal mass removed by the concrete N^4 B4 filter is
bounded by a square-reciprocal middle-prime tail plus a negligible block
endpoint term. -/
theorem sum_inv_largeCutoffBadOddCofactors_le
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ largeCutoffBadOddCofactors N, (1 : ℝ) / m ≤
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (((1 : ℝ) / (N ^ 4 : ℕ)) * (harmonic N : ℝ) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (harmonic N : ℝ)) := by
  let K : ℝ := ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k
  let R : ℝ := ∑ r ∈ middlePrimes N, (1 : ℝ) / r
  let H : ℝ := (harmonic N : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun k hk => by positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun r hr => by positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  calc
    (∑ m ∈ largeCutoffBadOddCofactors N, (1 : ℝ) / m) ≤
        ∑ m ∈ middlePredLargeCofactors N, (1 : ℝ) / m := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (largeCutoffBadOddCofactors_subset_middlePredLarge hN)
      intro m hm hnot
      positivity
    _ = ∑ k ∈ oddSmallFactors N,
          ∑ r ∈ middlePrimes N,
            ∑ q ∈ (largePrimes N).filter (fun q => r ∣ q - 1),
              (1 : ℝ) / (k * r * q) :=
      sum_inv_middlePredLargeCofactors_eq_triple hN
    _ ≤ ∑ k ∈ oddSmallFactors N,
          ∑ r ∈ middlePrimes N,
            ((1 : ℝ) / k * ((1 : ℝ) / r)) *
              (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro r hr
      calc
        (∑ q ∈ (largePrimes N).filter (fun q => r ∣ q - 1),
            (1 : ℝ) / (k * r * q)) =
            ((1 : ℝ) / k * ((1 : ℝ) / r)) *
              ∑ q ∈ (largePrimes N).filter (fun q => r ∣ q - 1),
                (1 : ℝ) / q := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          push_cast
          ring
        _ ≤ ((1 : ℝ) / k * ((1 : ℝ) / r)) *
              (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
          apply mul_le_mul_of_nonneg_left
            (by
              dsimp [H]
              exact sum_inv_largePrimes_filter_middle_dvd_pred_le hN hr)
          positivity
    _ = K *
        ∑ r ∈ middlePrimes N,
          ((1 : ℝ) / r) *
            (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
      calc
        (∑ k ∈ oddSmallFactors N,
            ∑ r ∈ middlePrimes N,
              ((1 : ℝ) / k * ((1 : ℝ) / r)) *
                (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H)) =
            ∑ k ∈ oddSmallFactors N,
              ((1 : ℝ) / k) *
                ∑ r ∈ middlePrimes N,
                  ((1 : ℝ) / r) *
                    (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = K *
            ∑ r ∈ middlePrimes N,
              ((1 : ℝ) / r) *
                (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H) := by
          dsimp [K]
          rw [Finset.sum_mul]
    _ = K *
        ((∑ r ∈ middlePrimes N, (1 : ℝ) / (r ^ 2 : ℕ)) * H +
          ((1 : ℝ) / (N ^ 21 : ℕ)) * R * H) := by
      congr 1
      calc
        (∑ r ∈ middlePrimes N,
            ((1 : ℝ) / r) *
              (((1 : ℝ) / r + (1 : ℝ) / (N ^ 21 : ℕ)) * H)) =
            ∑ r ∈ middlePrimes N,
              (((1 : ℝ) / (r ^ 2 : ℕ)) * H +
                ((1 : ℝ) / (N ^ 21 : ℕ)) * ((1 : ℝ) / r) * H) := by
          apply Finset.sum_congr rfl
          intro r hr
          push_cast
          ring
        _ = (∑ r ∈ middlePrimes N, (1 : ℝ) / (r ^ 2 : ℕ)) * H +
            ((1 : ℝ) / (N ^ 21 : ℕ)) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r) * H := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul,
            ← Finset.sum_mul, ← Finset.mul_sum]
        _ = (∑ r ∈ middlePrimes N, (1 : ℝ) / (r ^ 2 : ℕ)) * H +
            ((1 : ℝ) / (N ^ 21 : ℕ)) * R * H := by rfl
    _ ≤ K *
        (((1 : ℝ) / (N ^ 4 : ℕ)) * H +
          ((1 : ℝ) / (N ^ 21 : ℕ)) * R * H) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right
          (sum_inv_sq_middlePrimes_le_inv_pow_four hN) hH) _
    _ =
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
        (((1 : ℝ) / (N ^ 4 : ℕ)) * (harmonic N : ℝ) +
          ((1 : ℝ) / (N ^ 21 : ℕ)) *
            (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
              (harmonic N : ℝ)) := by
      rfl

/-- Middle-layer reciprocal mass is bounded by the harmonic mass up to its
right endpoint. -/
theorem sum_inv_middlePrimes_le_harmonic_pow_five
    (N : ℕ) :
    ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤
      (harmonic (N ^ 5) : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  calc
    (∑ r ∈ middlePrimes N, (1 : ℝ) / r) ≤
        ∑ r ∈ Finset.Icc 1 (N ^ 5), (1 : ℝ) / r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        rw [Finset.mem_Icc]
        have hrData := mem_middlePrimes_iff.mp hr
        exact ⟨hrData.2.2.pos, hrData.2.1⟩
      · intro r hr hnot
        positivity
    _ = ∑ r ∈ Finset.Icc 1 (N ^ 5),
          (((r : ℚ)⁻¹ : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Rat.cast_inv, Rat.cast_natCast]
      ring

/-- A very crude uniform numerical bound is enough to show that the
concrete-cutoff B4 deletion is negligible compared with logarithmic raw
mass. -/
theorem sum_inv_largeCutoffBadOddCofactors_le_two
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ m ∈ largeCutoffBadOddCofactors N, (1 : ℝ) / m ≤ 2 := by
  have hbase := sum_inv_largeCutoffBadOddCofactors_le hN
  have hK :
      ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k ≤ (N : ℝ) := by
    exact (sum_inv_oddSmallFactors_le_harmonic N).trans
      (harmonic_le_natCast N)
  have hR :
      ∑ r ∈ middlePrimes N, (1 : ℝ) / r ≤ ((N ^ 5 : ℕ) : ℝ) := by
    exact (sum_inv_middlePrimes_le_harmonic_pow_five N).trans
      (harmonic_le_natCast (N ^ 5))
  have hH : (harmonic N : ℝ) ≤ (N : ℝ) :=
    harmonic_le_natCast N
  have hK0 : 0 ≤ ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k :=
    Finset.sum_nonneg fun k hk => by positivity
  have hR0 : 0 ≤ ∑ r ∈ middlePrimes N, (1 : ℝ) / r :=
    Finset.sum_nonneg fun r hr => by positivity
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun j hj => by positivity
  have hfirst :
      (N : ℝ) * (((1 : ℝ) / (N ^ 4 : ℕ)) * (N : ℝ)) ≤ 1 := by
    have hpow : N ^ 2 ≤ N ^ 4 :=
      Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
    have hpowR : ((N ^ 2 : ℕ) : ℝ) ≤ ((N ^ 4 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hden : (0 : ℝ) < ((N ^ 4 : ℕ) : ℝ) := by positivity
    calc
      (N : ℝ) * (((1 : ℝ) / (N ^ 4 : ℕ)) * (N : ℝ)) =
          ((N ^ 2 : ℕ) : ℝ) / ((N ^ 4 : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ 1 := by
        apply (div_le_iff₀ hden).2
        simpa only [one_mul] using hpowR
  have hsecond :
      (N : ℝ) *
        (((1 : ℝ) / (N ^ 21 : ℕ)) * ((N ^ 5 : ℕ) : ℝ) *
          (N : ℝ)) ≤ 1 := by
    have hpow : N ^ 7 ≤ N ^ 21 :=
      Nat.pow_le_pow_right (by omega : 1 ≤ N) (by omega)
    have hpowR : ((N ^ 7 : ℕ) : ℝ) ≤ ((N ^ 21 : ℕ) : ℝ) := by
      exact_mod_cast hpow
    have hden : (0 : ℝ) < ((N ^ 21 : ℕ) : ℝ) := by positivity
    calc
      (N : ℝ) *
          (((1 : ℝ) / (N ^ 21 : ℕ)) * ((N ^ 5 : ℕ) : ℝ) *
            (N : ℝ)) =
          ((N ^ 7 : ℕ) : ℝ) / ((N ^ 21 : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ 1 := by
        apply (div_le_iff₀ hden).2
        simpa only [one_mul] using hpowR
  calc
    (∑ m ∈ largeCutoffBadOddCofactors N, (1 : ℝ) / m) ≤
        (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k) *
          (((1 : ℝ) / (N ^ 4 : ℕ)) * (harmonic N : ℝ) +
            ((1 : ℝ) / (N ^ 21 : ℕ)) *
              (∑ r ∈ middlePrimes N, (1 : ℝ) / r) *
                (harmonic N : ℝ)) := hbase
    _ ≤ (N : ℝ) *
          (((1 : ℝ) / (N ^ 4 : ℕ)) * (N : ℝ) +
            ((1 : ℝ) / (N ^ 21 : ℕ)) *
              ((N ^ 5 : ℕ) : ℝ) * (N : ℝ)) := by
      gcongr
    _ ≤ 2 := by
      linarith

/-- Subtracting the concrete-cutoff B4 bad mass gives a retained-mass
lower bound for the good family. -/
theorem sum_inv_largeCutoffGoodOddCofactors_ge
    {N : ℕ} {R D : ℝ}
    (hraw : R ≤ ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m)
    (hbad : ∑ m ∈ largeCutoffBadOddCofactors N,
        (1 : ℝ) / m ≤ D) :
    R - D ≤
      ∑ m ∈ largeCutoffGoodOddCofactors N, (1 : ℝ) / m := by
  classical
  let good := largeCutoffGoodOddCofactors N
  let bad := largeCutoffBadOddCofactors N
  have hpartition : oddRawCofactors N = good ∪ bad := by
    ext m
    simp only [good, bad, largeCutoffGoodOddCofactors,
      largeCutoffBadOddCofactors, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hm
      by_cases hg : ∀ p : ℕ, p.Prime → N ^ 4 < p →
          ¬ (p ∣ m ∧ p ∣ Nat.totient m)
      · exact Or.inl ⟨hm, hg⟩
      · right
        push_neg at hg
        exact ⟨hm, hg⟩
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm
  have hdisj : Disjoint good bad := by
    rw [Finset.disjoint_left]
    intro m hmg hmb
    have hg := (mem_largeCutoffGoodOddCofactors_iff.mp hmg).2
    have hb := (mem_largeCutoffBadOddCofactors_iff.mp hmb).2
    obtain ⟨p, hp, hpN, hpm, hpφ⟩ := hb
    exact hg p hp hpN ⟨hpm, hpφ⟩
  have htotal :
      ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m =
        ∑ m ∈ good, (1 : ℝ) / m +
          ∑ m ∈ bad, (1 : ℝ) / m := by
    rw [hpartition, Finset.sum_union hdisj]
  dsimp [good, bad] at htotal ⊢
  linarith

/-- The genuine B4 family at cutoff N^4 still has logarithmic reciprocal
mass. -/
theorem eventually_largeCutoffGoodOddCofactors_log_mass :
    ∀ᶠ N : ℕ in Filter.atTop,
      (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ largeCutoffGoodOddCofactors N,
          (1 : ℝ) / m := by
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (8000 : ℝ))
  filter_upwards [eventually_log_le_mul_reciprocalOddRawCofactorSum,
      hlog, Filter.eventually_ge_atTop 2] with N hraw hlogN hN
  change (8000 : ℝ) ≤ Real.log (N : ℝ) at hlogN
  have hraw' :
      (1 / 2000 : ℝ) * Real.log (N : ℝ) ≤
        ∑ m ∈ oddRawCofactors N, (1 : ℝ) / m := by
    simpa [reciprocalOddRawCofactorSum] using hraw
  have hret := sum_inv_largeCutoffGoodOddCofactors_ge
    hraw' (sum_inv_largeCutoffBadOddCofactors_le_two hN)
  calc
    (1 / 4000 : ℝ) * Real.log (N : ℝ) ≤
        (1 / 2000 : ℝ) * Real.log (N : ℝ) - 2 := by
      nlinarith
    _ ≤ ∑ m ∈ largeCutoffGoodOddCofactors N,
          (1 : ℝ) / m := hret

end Erdos822
