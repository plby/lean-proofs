/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.B1Packets
import ErdosProblems.Erdos387.UniformAnalyticInputs

/-!
# Reciprocal mass of the B1 packets from uniform prime distribution

The only prime-distribution input is the proved shifted Siegel--Walfisz
lower bound.  We use its unshifted specialization on disjoint dyadic
intervals and keep the integer-floor error explicit.
-/

namespace Erdos822

open scoped BigOperators

def b1DyadicPacket (d j : ℕ) : Finset ℕ :=
  (Finset.Ioc (2 ^ j) (2 ^ (j + 1))).filter
    fun q ↦ q.Prime ∧ d ∣ q - 1

theorem mem_b1DyadicPacket_iff {d j q : ℕ} :
    q ∈ b1DyadicPacket d j ↔
      2 ^ j < q ∧ q ≤ 2 ^ (j + 1) ∧ q.Prime ∧ d ∣ q - 1 := by
  simp [b1DyadicPacket, and_assoc]

theorem b1DyadicPacket_eq_mod_filter (d j : ℕ) :
    b1DyadicPacket d j =
      (Finset.Ioc (2 ^ j) (2 * 2 ^ j)).filter
        (fun q ↦ q.Prime ∧ q % d = 1 % d) := by
  ext q
  simp only [b1DyadicPacket, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hprime, hdiv⟩
    refine ⟨⟨hlo, by simpa [pow_succ, Nat.mul_comm] using hhi⟩, hprime, ?_⟩
    exact ((Nat.modEq_iff_dvd' hprime.one_le).mpr hdiv).symm
  · rintro ⟨⟨hlo, hhi⟩, hprime, hmod⟩
    refine ⟨⟨hlo, by simpa [pow_succ, Nat.mul_comm] using hhi⟩, hprime, ?_⟩
    exact (Nat.modEq_iff_dvd' hprime.one_le).mp (Nat.ModEq.symm hmod)

theorem exists_b1DyadicPacket_card_lower :
    ∃ J₀ : ℕ, ∀ j d : ℕ, J₀ ≤ j → 2 ≤ d → d ≤ j + 1 →
      2 ^ j / (8 * d * (j + 1)) ≤ (b1DyadicPacket d j).card := by
  obtain ⟨X₀, hX₀⟩ := Erdos387.shiftedSiegelWalfiszLower 1
  refine ⟨X₀, ?_⟩
  intro j d hj hd hdj
  have hX : X₀ ≤ 2 ^ j := hj.trans (Nat.lt_two_pow_self.le)
  have h := hX₀ (2 ^ j) d 1 0 hX hd
    (by simpa [Nat.log_pow (by norm_num : 1 < 2)] using hdj)
    (by omega) (Nat.coprime_one_left d)
  simpa [b1DyadicPacket_eq_mod_filter, Nat.log_pow (by norm_num : 1 < 2)] using h

theorem exists_b1DyadicPacket_reciprocal_lower :
    ∃ J₀ : ℕ, ∀ j d : ℕ, J₀ ≤ j → 2 ≤ d → d ≤ j + 1 →
      (1 : ℝ) / (16 * d * (j + 1)) - 1 / (2 : ℝ) ^ (j + 1) ≤
        ∑ q ∈ b1DyadicPacket d j, (1 : ℝ) / q := by
  obtain ⟨J₀, hJ₀⟩ := exists_b1DyadicPacket_card_lower
  refine ⟨J₀, ?_⟩
  intro j d hj hd hdj
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hjpos : (0 : ℝ) < j + 1 := by positivity
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (j + 1) := by positivity
  have hfloor := cast_div_sub_one_le_natCast_div
    (N := 2 ^ j) (p := 8 * d * (j + 1)) (by positivity)
  have hcard : ((2 ^ j / (8 * d * (j + 1)) : ℕ) : ℝ) ≤
      (b1DyadicPacket d j).card := by exact_mod_cast hJ₀ j d hj hd hdj
  have hcount : (2 : ℝ) ^ j / (8 * d * (j + 1)) - 1 ≤
      (b1DyadicPacket d j).card := by
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one] using hfloor.trans hcard
  have hmass : ((b1DyadicPacket d j).card : ℝ) / (2 : ℝ) ^ (j + 1) ≤
      ∑ q ∈ b1DyadicPacket d j, (1 : ℝ) / q := by
    calc
      ((b1DyadicPacket d j).card : ℝ) / (2 : ℝ) ^ (j + 1) =
          ∑ _q ∈ b1DyadicPacket d j, (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ q ∈ b1DyadicPacket d j, (1 : ℝ) / q := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hlo, hhi, hprime, hdiv⟩ := mem_b1DyadicPacket_iff.mp hq
        exact one_div_le_one_div_of_le (by exact_mod_cast hprime.pos)
          (by exact_mod_cast hhi)
  calc
    (1 : ℝ) / (16 * d * (j + 1)) - 1 / (2 : ℝ) ^ (j + 1) =
        ((2 : ℝ) ^ j / (8 * d * (j + 1)) - 1) / (2 : ℝ) ^ (j + 1) := by
      rw [pow_succ]
      field_simp
      ring
    _ ≤ ((b1DyadicPacket d j).card : ℝ) / (2 : ℝ) ^ (j + 1) :=
      div_le_div_of_nonneg_right hcount hpowpos.le
    _ ≤ ∑ q ∈ b1DyadicPacket d j, (1 : ℝ) / q := hmass

theorem b1DyadicPacket_disjoint {d i j : ℕ} (hij : i ≠ j) :
    Disjoint (b1DyadicPacket d i) (b1DyadicPacket d j) := by
  have hlt {a b : ℕ} (hab : a < b) :
      Disjoint (b1DyadicPacket d a) (b1DyadicPacket d b) := by
    rw [Finset.disjoint_left]
    intro q hqa hqb
    have hqa' := mem_b1DyadicPacket_iff.mp hqa
    have hqb' := mem_b1DyadicPacket_iff.mp hqb
    have hpow : 2 ^ (a + 1) ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hlt hij
  · exact (hlt hij).symm

theorem sum_b1DyadicPacket_mass_le_packetMean (d J K : ℕ) :
    (∑ j ∈ Finset.Ico J K, ∑ q ∈ b1DyadicPacket d j, (1 : ℝ) / q) ≤
      packetPrimeMean (b1PrimePacket (2 ^ K) d) := by
  have hdis : (↑(Finset.Ico J K) : Set ℕ).Pairwise
      (fun i j ↦ Disjoint (b1DyadicPacket d i) (b1DyadicPacket d j)) := by
    intro i hi j hj hij
    exact b1DyadicPacket_disjoint hij
  rw [← Finset.sum_biUnion hdis]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨j, hj, hqj⟩ := Finset.mem_biUnion.mp hq
    obtain ⟨hlo, hhi, hprime, hdiv⟩ := mem_b1DyadicPacket_iff.mp hqj
    apply mem_b1PrimePacket_iff.mpr
    refine ⟨hhi.trans ?_, hprime, hdiv⟩
    exact Nat.pow_le_pow_right (by norm_num)
      (by have := (Finset.mem_Ico.mp hj).2; omega)
  · intro q hq hnot
    positivity

theorem sum_Ico_inv_two_pow_succ_le_one (J K : ℕ) :
    ∑ j ∈ Finset.Ico J K, (1 : ℝ) / (2 : ℝ) ^ (j + 1) ≤ 1 := by
  calc
    (∑ j ∈ Finset.Ico J K, (1 : ℝ) / (2 : ℝ) ^ (j + 1)) ≤
        ∑ j ∈ Finset.range K, (1 : ℝ) / (2 : ℝ) ^ (j + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
      · intro j hj hnot
        positivity
    _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [pow_succ, div_pow]
      simp only [one_pow]
      ring
    _ ≤ (1 / 2 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le K) (by norm_num)
    _ = 1 := by norm_num

theorem sum_Ico_inv_add_one_eq_harmonic_sub {J K : ℕ} (hJK : J ≤ K) :
    (∑ j ∈ Finset.Ico J K, (1 : ℝ) / ((j : ℝ) + 1)) =
      (harmonic K : ℝ) - (harmonic J : ℝ) := by
  rw [Finset.sum_Ico_eq_sub _ hJK]
  simp [harmonic, div_eq_mul_inv]

/-- Summing disjoint dyadic packets produces a harmonic lower bound with
an absolute endpoint loss of one. -/
theorem exists_packetPrimeMean_harmonic_lower :
    ∃ J₀ : ℕ, ∀ J K d : ℕ, J₀ ≤ J → J ≤ K → 2 ≤ d → d ≤ J + 1 →
      ((harmonic K : ℝ) - harmonic J) / (16 * d) - 1 ≤
        packetPrimeMean (b1PrimePacket (2 ^ K) d) := by
  obtain ⟨J₀, hJ₀⟩ := exists_b1DyadicPacket_reciprocal_lower
  refine ⟨J₀, ?_⟩
  intro J K d hJ hJK hd hdJ
  have hsum := Finset.sum_le_sum (s := Finset.Ico J K)
    (fun j hj ↦ hJ₀ j d (hJ.trans (Finset.mem_Ico.mp hj).1) hd
      (by have := (Finset.mem_Ico.mp hj).1; omega))
  have hsum' :
      ((harmonic K : ℝ) - harmonic J) / (16 * d) -
        (∑ j ∈ Finset.Ico J K, (1 : ℝ) / (2 : ℝ) ^ (j + 1)) ≤
        ∑ j ∈ Finset.Ico J K, ∑ q ∈ b1DyadicPacket d j, (1 : ℝ) / q := by
    have heq : (∑ j ∈ Finset.Ico J K, (1 : ℝ) / (16 * d * (j + 1))) =
        ((harmonic K : ℝ) - harmonic J) / (16 * d) := by
      rw [← sum_Ico_inv_add_one_eq_harmonic_sub hJK, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      simp [div_eq_mul_inv]
    simpa only [Finset.sum_sub_distrib, heq] using hsum
  have htail := sum_Ico_inv_two_pow_succ_le_one J K
  have hmass := sum_b1DyadicPacket_mass_le_packetMean d J K
  linarith

/-- A convenient logarithmic form, after multiplying by the modulus. -/
theorem exists_packetPrimeMean_log_lower :
    ∃ J₀ : ℕ, ∀ J K d : ℕ, J₀ ≤ J → J ≤ K → 2 ≤ d → d ≤ J + 1 →
      (Real.log ((K : ℝ) + 1) - 1 - Real.log (J : ℝ)) / 16 - d ≤
        (d : ℝ) * packetPrimeMean (b1PrimePacket (2 ^ K) d) := by
  obtain ⟨J₀, hJ₀⟩ := exists_packetPrimeMean_harmonic_lower
  refine ⟨J₀, ?_⟩
  intro J K d hJ hJK hd hdJ
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := hJ₀ J K d hJ hJK hd hdJ
  have hK := log_add_one_le_harmonic K
  have hJharm := harmonic_le_one_add_log J
  have hnum : Real.log ((K : ℝ) + 1) - 1 - Real.log (J : ℝ) ≤
      (harmonic K : ℝ) - harmonic J := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hK
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum (show (0 : ℝ) ≤ 16 * d by positivity)
  have hlow :
      (Real.log ((K : ℝ) + 1) - 1 - Real.log (J : ℝ)) / (16 * d) - 1 ≤
        packetPrimeMean (b1PrimePacket (2 ^ K) d) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlow hdpos.le
  calc
    (Real.log ((K : ℝ) + 1) - 1 - Real.log (J : ℝ)) / 16 - d =
        (d : ℝ) * ((Real.log ((K : ℝ) + 1) - 1 - Real.log (J : ℝ)) /
          (16 * d) - 1) := by field_simp
    _ ≤ (d : ℝ) * packetPrimeMean (b1PrimePacket (2 ^ K) d) := hmul

end Erdos822
