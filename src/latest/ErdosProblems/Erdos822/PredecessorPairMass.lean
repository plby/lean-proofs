/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.InternalPrimeChannelBound

/-! # A harmonic average for a prime dividing a small factor and a prime predecessor -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem exists_primePacket_tail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N T y : ℕ, 2 ≤ y →
      (∑ p ∈ (Nat.primesLE N).filter (y < ·), packetPrimeMean (b1PrimePacket T p) / p) ≤
        C * (b1DoubleLog T + 2 : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) := by
  obtain ⟨C, hC, hpacket⟩ := exists_packetPrimeMean_prime_modulus_upper
  obtain ⟨D, hD, htail⟩ := exists_sum_inv_sq_primesAbove_le
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro N T y hy
  calc
    (∑ p ∈ (Nat.primesLE N).filter (y < ·), packetPrimeMean (b1PrimePacket T p) / p) ≤
        ∑ p ∈ (Nat.primesLE N).filter (y < ·), (C * (b1DoubleLog T + 2 : ℝ) / p) / p := by
      exact Finset.sum_le_sum fun p hp ↦ div_le_div_of_nonneg_right
        (hpacket T p (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2) (by positivity)
    _ = (C * (b1DoubleLog T + 2 : ℝ)) *
        ∑ p ∈ (Nat.primesLE N).filter (y < ·), (1 : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (C * (b1DoubleLog T + 2 : ℝ)) * (D / ((y : ℝ) * Real.log (y : ℝ))) :=
      mul_le_mul_of_nonneg_left (htail N y hy) (by positivity)
    _ = C * D * (b1DoubleLog T + 2 : ℝ) / ((y : ℝ) * Real.log (y : ℝ)) := by ring

theorem sum_inv_predecessor_common_prime_le_packets
    {N T y : ℕ} {A : Finset ℕ} (hA : A ⊆ Nat.primesLE T) :
    (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
      ∑ q ∈ A.filter (fun q ↦ ∃ p, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ q - 1), (1 : ℝ) / q) ≤
      (harmonic N : ℝ) *
        ∑ p ∈ (Nat.primesLE N).filter (y < ·), packetPrimeMean (b1PrimePacket T p) / p := by
  let P := (Nat.primesLE N).filter (y < ·)
  have hfiber {k : ℕ} (hk : k ∈ oddSmallFactors N) :
      (∑ q ∈ A.filter (fun q ↦ ∃ p, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ q - 1), (1 : ℝ) / q) ≤
        ∑ p ∈ P.filter (· ∣ k), packetPrimeMean (b1PrimePacket T p) := by
    have hsub : A.filter (fun q ↦ ∃ p, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ q - 1) ⊆
        (P.filter (· ∣ k)).biUnion (b1PrimePacket T) := by
      intro q hq
      obtain ⟨hqA, p, hp, hyp, hpk, hpq⟩ := Finset.mem_filter.mp hq
      have hpN := (Nat.le_of_dvd (oddSmallFactors_pos hk) hpk).trans (oddSmallFactors_le hk)
      have hqp := Nat.mem_primesLE.mp (hA hqA)
      exact Finset.mem_biUnion.mpr ⟨p,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpN, hp⟩, hyp⟩, hpk⟩,
        mem_b1PrimePacket_iff.mpr ⟨hqp.1, hqp.2, hpq⟩⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q hq hnot ↦ by positivity)).trans
      (sum_biUnion_le_sum _ _ _ (fun p hp q hq ↦ by positivity))
  calc
    _ ≤ ∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ p ∈ P.filter (· ∣ k), packetPrimeMean (b1PrimePacket T p) := by
      exact Finset.sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_left (hfiber hk) (by positivity)
    _ = ∑ p ∈ P, packetPrimeMean (b1PrimePacket T p) *
        ∑ k ∈ (oddSmallFactors N).filter (p ∣ ·), (1 : ℝ) / k := by
      simp only [Finset.mul_sum, Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      split_ifs <;> ring
    _ ≤ ∑ p ∈ P, packetPrimeMean (b1PrimePacket T p) * ((harmonic N : ℝ) / p) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.pos
      have hmass : (∑ k ∈ (oddSmallFactors N).filter (p ∣ ·), (1 : ℝ) / k) ≤
          (harmonic N : ℝ) / p :=
        (sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div hp0).trans
          (div_le_div_of_nonneg_right (harmonic_cast_mono (Nat.div_le_self N p)) (by positivity))
      exact mul_le_mul_of_nonneg_left hmass (Finset.sum_nonneg fun q hq ↦ by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

theorem exists_predecessor_common_prime_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N T y : ℕ, ∀ A : Finset ℕ,
      A ⊆ Nat.primesLE T → 2 ≤ y →
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ q ∈ A.filter (fun q ↦ ∃ p, p.Prime ∧ y < p ∧ p ∣ k ∧ p ∣ q - 1), (1 : ℝ) / q) ≤
        C * (harmonic N : ℝ) * (b1DoubleLog T + 2 : ℝ) /
          ((y : ℝ) * Real.log (y : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := exists_primePacket_tail_bound
  refine ⟨C, hC, ?_⟩
  intro N T y A hA hy
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun k hk ↦ by positivity
  refine (sum_inv_predecessor_common_prime_le_packets hA).trans ?_
  calc
    _ ≤ (harmonic N : ℝ) *
        (C * (b1DoubleLog T + 2 : ℝ) / ((y : ℝ) * Real.log (y : ℝ))) :=
      mul_le_mul_of_nonneg_left (hbound N T y hy) hH
    _ = _ := by ring

theorem b1DoubleLog_pow_le (N a : ℕ) :
    b1DoubleLog (N ^ a) ≤ b1DoubleLog N + a + 1 := by
  by_cases ha : a = 0
  · subst a
    simp [b1DoubleLog]
  have hNpow : N ^ a < 2 ^ ((Nat.log 2 N + 1) * a) := by
    rw [pow_mul]
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) N) ha
  have hlog : Nat.log 2 (N ^ a) ≤ (Nat.log 2 N + 1) * a := by
    exact (Nat.log_lt_of_lt_pow' (by positivity) hNpow).le
  have ha2 : a ≤ 2 ^ a := Nat.lt_two_pow_self.le
  have hK : Nat.log 2 N + 1 ≤ 2 ^ (b1DoubleLog N + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (Nat.log 2 N)
  have hupper : Nat.log 2 (N ^ a) ≤ 2 ^ (b1DoubleLog N + a + 1) := by
    refine hlog.trans ((Nat.mul_le_mul hK ha2).trans_eq ?_)
    rw [← pow_add]
    congr 1
    omega
  exact (Nat.log_mono_right hupper).trans_eq (Nat.log_pow (by norm_num) _)

theorem eventually_harmonic_doubleLog_pow_div_small
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) (a : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      C * (harmonic N : ℝ) * (b1DoubleLog (N ^ a) + 2 : ℝ) /
        ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) ≤
          ε * Real.log (N : ℝ) := by
  have hlogZ : Tendsto (fun N ↦ Real.log (b1DoubleLog N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_b1DoubleLog_atTop)
  filter_upwards [tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2,
    hlogZ.eventually_ge_atTop (2 * C * (a + 4 : ℝ) / ε), eventually_ge_atTop 4]
      with N hZ hlogZ hN
  have hZpos : (0 : ℝ) < b1DoubleLog N := by exact_mod_cast (show 0 < b1DoubleLog N by omega)
  have hlogZpos : 0 < Real.log (b1DoubleLog N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b1DoubleLog N by omega))
  have hlogN : 1 ≤ Real.log (N : ℝ) := BoundedGaps.Maynard.one_le_log_natCast hN
  have hH : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log N
    linarith only [h, hlogN]
  have hH0 : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun k hk ↦ by positivity
  have hZpow : (b1DoubleLog (N ^ a) + 2 : ℝ) ≤ (a + 4 : ℝ) * b1DoubleLog N := by
    have h := b1DoubleLog_pow_le N a
    have hR : (b1DoubleLog (N ^ a) : ℝ) ≤ b1DoubleLog N + a + 1 := by exact_mod_cast h
    have hZR : (2 : ℝ) ≤ b1DoubleLog N := by exact_mod_cast hZ
    have haR := Nat.cast_nonneg (α := ℝ) a
    nlinarith only [hR, hZR, haR]
  have hcoeff : 2 * C * (a + 4 : ℝ) / Real.log (b1DoubleLog N : ℝ) ≤ ε := by
    apply (div_le_iff₀ hlogZpos).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hlogZ
  calc
    _ ≤ C * (2 * Real.log (N : ℝ)) * ((a + 4 : ℝ) * b1DoubleLog N) /
        ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) := by gcongr
    _ = (2 * C * (a + 4 : ℝ) / Real.log (b1DoubleLog N : ℝ)) * Real.log (N : ℝ) := by
      field_simp
    _ ≤ ε * Real.log (N : ℝ) := mul_le_mul_of_nonneg_right hcoeff (by linarith)

theorem eventually_predecessor_common_prime_mass_small
    {ε : ℝ} (hε : 0 < ε) (a : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Nat.primesLE (N ^ a) →
      (∑ k ∈ oddSmallFactors N, (1 : ℝ) / k *
        ∑ q ∈ A.filter (fun q ↦ ∃ p, p.Prime ∧ b1DoubleLog N < p ∧ p ∣ k ∧ p ∣ q - 1),
          (1 : ℝ) / q) ≤ ε * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_predecessor_common_prime_mass_bound
  filter_upwards [eventually_harmonic_doubleLog_pow_div_small hC.le hε a,
    tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2] with N hsmall hZ
  intro A hA
  exact (hbound N (N ^ a) (b1DoubleLog N) A hA hZ).trans hsmall

#print axioms eventually_predecessor_common_prime_mass_small

end Erdos822
