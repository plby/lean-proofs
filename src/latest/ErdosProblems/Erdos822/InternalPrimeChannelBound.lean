/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.PrimePredecessorReciprocal
import ErdosProblems.Erdos822.InternalShiftedPrimeMass

/-! # The internal totient channel at an iterated-logarithm cutoff -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem internalShiftedPrimeBadSmallFactors_subset_primePackets (N y : ℕ) :
    internalShiftedPrimeBadSmallFactors N y ⊆
      ((Nat.primesLE N).filter (y < ·)).biUnion fun p ↦
        (b1PrimePacket N p).biUnion fun q ↦
          (oddSmallFactors N).filter (p * q ∣ ·) := by
  intro k hk
  obtain ⟨hk, p, hp, hyp, hpk, q, hqk, hpq⟩ := Finset.mem_filter.mp hk
  have hk0 := oddSmallFactors_pos hk
  have hkN := oddSmallFactors_le hk
  have hpN := (Nat.le_of_dvd hk0 hpk).trans hkN
  have hqp := Nat.prime_of_mem_primeFactors hqk
  have hqdiv := Nat.dvd_of_mem_primeFactors hqk
  have hqN := (Nat.le_of_dvd hk0 hqdiv).trans hkN
  have hpqlt : p < q := by
    have := Nat.le_of_dvd (Nat.sub_pos_of_lt hqp.one_lt) hpq
    omega
  exact Finset.mem_biUnion.mpr ⟨p,
    Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpN, hp⟩, hyp⟩,
    Finset.mem_biUnion.mpr ⟨q, mem_b1PrimePacket_iff.mpr ⟨hqN, hqp, hpq⟩,
      Finset.mem_filter.mpr ⟨hk,
        hp.dvd_mul_of_dvd_ne (ne_of_lt hpqlt) hqp hpk hqdiv⟩⟩⟩

theorem sum_inv_internalShiftedPrimeBadSmallFactors_le_primePackets (N y : ℕ) :
    (∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k) ≤
      (harmonic N : ℝ) * ∑ p ∈ (Nat.primesLE N).filter (y < ·),
        packetPrimeMean (b1PrimePacket N p) / p := by
  calc
    (∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k) ≤
        ∑ k ∈ ((Nat.primesLE N).filter (y < ·)).biUnion (fun p ↦
          (b1PrimePacket N p).biUnion fun q ↦ (oddSmallFactors N).filter (p * q ∣ ·)),
          (1 : ℝ) / k :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (internalShiftedPrimeBadSmallFactors_subset_primePackets N y)
        (fun k hk hnot ↦ by positivity)
    _ ≤ ∑ p ∈ (Nat.primesLE N).filter (y < ·),
        ∑ q ∈ b1PrimePacket N p,
          ∑ k ∈ (oddSmallFactors N).filter (p * q ∣ ·), (1 : ℝ) / k := by
      refine (sum_biUnion_le_sum _ _ _ (fun p hp k hk ↦ by positivity)).trans ?_
      exact Finset.sum_le_sum fun p hp ↦
        sum_biUnion_le_sum _ _ _ (fun q hq k hk ↦ by positivity)
    _ ≤ ∑ p ∈ (Nat.primesLE N).filter (y < ·),
        ∑ q ∈ b1PrimePacket N p, (harmonic N : ℝ) / (p * q : ℕ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp0 := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.pos
      apply Finset.sum_le_sum
      intro q hq
      have hq0 := (mem_b1PrimePacket_iff.mp hq).2.1.pos
      exact (sum_inv_oddSmallFactors_filter_dvd_le_harmonic_div
        (Nat.mul_pos hp0 hq0)).trans
          (div_le_div_of_nonneg_right (harmonic_cast_mono (Nat.div_le_self N (p * q)))
            (by positivity))
    _ = (harmonic N : ℝ) * ∑ p ∈ (Nat.primesLE N).filter (y < ·),
        packetPrimeMean (b1PrimePacket N p) / p := by
      simp only [Finset.mul_sum, packetPrimeMean, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      push_cast
      ring

theorem exists_internalShiftedPrimeBadSmallFactors_sharp_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N y : ℕ, 2 ≤ y →
      (∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k) ≤
        C * (harmonic N : ℝ) * (b1DoubleLog N + 2 : ℝ) /
          ((y : ℝ) * Real.log (y : ℝ)) := by
  obtain ⟨C, hC, hpacket⟩ := exists_packetPrimeMean_prime_modulus_upper
  obtain ⟨D, hD, htail⟩ := exists_sum_inv_sq_primesAbove_le
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro N y hy
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum]
    exact Finset.sum_nonneg fun k hk ↦ by positivity
  calc
    (∑ k ∈ internalShiftedPrimeBadSmallFactors N y, (1 : ℝ) / k) ≤
        (harmonic N : ℝ) * ∑ p ∈ (Nat.primesLE N).filter (y < ·),
          packetPrimeMean (b1PrimePacket N p) / p :=
      sum_inv_internalShiftedPrimeBadSmallFactors_le_primePackets N y
    _ ≤ (harmonic N : ℝ) * ∑ p ∈ (Nat.primesLE N).filter (y < ·),
        (C * (b1DoubleLog N + 2 : ℝ) / p) / p := by
      apply mul_le_mul_of_nonneg_left _ hH
      apply Finset.sum_le_sum
      intro p hp
      exact div_le_div_of_nonneg_right
        (hpacket N p (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2) (by positivity)
    _ = (harmonic N : ℝ) * (C * (b1DoubleLog N + 2 : ℝ)) *
        ∑ p ∈ (Nat.primesLE N).filter (y < ·), (1 : ℝ) / (p : ℝ) ^ 2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ (harmonic N : ℝ) * (C * (b1DoubleLog N + 2 : ℝ)) *
        (D / ((y : ℝ) * Real.log (y : ℝ))) :=
      mul_le_mul_of_nonneg_left (htail N y hy) (by positivity)
    _ = C * D * (harmonic N : ℝ) * (b1DoubleLog N + 2 : ℝ) /
        ((y : ℝ) * Real.log (y : ℝ)) := by ring

theorem eventually_internalShiftedPrimeBadSmallFactors_mass_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (∑ k ∈ internalShiftedPrimeBadSmallFactors N (b1DoubleLog N), (1 : ℝ) / k) ≤
        ε * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := exists_internalShiftedPrimeBadSmallFactors_sharp_bound
  have hlogZ : Tendsto (fun N ↦ Real.log (b1DoubleLog N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_b1DoubleLog_atTop)
  filter_upwards [tendsto_b1DoubleLog_atTop.eventually_ge_atTop 2,
    hlogZ.eventually_ge_atTop (4 * C / ε),
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).eventually_ge_atTop
      (Real.exp 1)] with N hZ hlogZ hN
  have hZpos : (0 : ℝ) < b1DoubleLog N := by exact_mod_cast (show 0 < b1DoubleLog N by omega)
  have hlogZpos : 0 < Real.log (b1DoubleLog N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b1DoubleLog N by omega))
  have hlogN : 1 ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 1) hN
    simpa only [Real.log_exp] using h
  have hH : (harmonic N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    have h := harmonic_le_one_add_log N
    linarith only [h, hlogN]
  have hZtwo : (b1DoubleLog N + 2 : ℝ) ≤ 2 * b1DoubleLog N := by
    have : (2 : ℝ) ≤ b1DoubleLog N := by exact_mod_cast hZ
    linarith only [this]
  have hcoeff : 4 * C / Real.log (b1DoubleLog N : ℝ) ≤ ε := by
    apply (div_le_iff₀ hlogZpos).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hlogZ
  calc
    (∑ k ∈ internalShiftedPrimeBadSmallFactors N (b1DoubleLog N), (1 : ℝ) / k) ≤
        C * (harmonic N : ℝ) * (b1DoubleLog N + 2 : ℝ) /
          ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) := hbound N _ hZ
    _ ≤ C * (2 * Real.log (N : ℝ)) * (2 * b1DoubleLog N : ℝ) /
        ((b1DoubleLog N : ℝ) * Real.log (b1DoubleLog N : ℝ)) := by gcongr
    _ = (4 * C / Real.log (b1DoubleLog N : ℝ)) * Real.log (N : ℝ) := by
      field_simp
      <;> ring
    _ ≤ ε * Real.log (N : ℝ) := mul_le_mul_of_nonneg_right hcoeff (by linarith)

#print axioms eventually_internalShiftedPrimeBadSmallFactors_mass_small

end Erdos822
