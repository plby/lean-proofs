/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.PrimeResidueIntervals
import ErdosProblems.Erdos822.B1Asymptotic
import ErdosProblems.Erdos822.PrimeReciprocalSquareTail

/-!
# Reciprocal primes with a prescribed prime divisor of their predecessor

Use blocks `(p*4^j,p*4^(j+1)]`.  Their lengths divided by the modulus are
exactly `3*4^j`, independently of `p`.  A fixed beta-sieve depth therefore
gives the required uniform harmonic bound after summing the blocks.
-/

namespace Erdos822

open scoped BigOperators Classical

theorem card_primeResidueInterval_le_width_div_add_one
    {p a L U y : ℕ} (hp : p.Prime) :
    (primeResidueInterval p a L U y).card ≤ (U - L) / p + 1 := by
  by_cases hne : (primeResidueInterval p a L U y).Nonempty
  · have h := card_primeResidueInterval_le_duplicateCandidates_of_nonempty hp hne
    dsimp only at h
    exact h.trans (by
      calc
        (twoAffinePrimeCandidates p _ p _ ((U - L) / p + 1) y).card ≤
            (Finset.range ((U - L) / p + 1)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = (U - L) / p + 1 := Finset.card_range _)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem exists_fixed_depth_primeResidueInterval_bound :
    ∃ S : ℕ, ∃ D : ℝ, 101 ≤ S ∧ 0 < D ∧
      ∀ p a L U y : ℕ, p.Prime → 2 ≤ y →
        ((primeResidueInterval p a L U y).card : ℝ) ≤
          (((U - L) / p + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, C, hA, hC, hbound⟩ := exists_primeResidueInterval_card_upper_bound
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (99 * Real.log A / 4)
  let S := max 101 (T + 100)
  have hS : 101 ≤ S := le_max_left _ _
  have hTS : T ≤ S - 100 := by dsimp [S]; omega
  have hlog : Real.log A ≤ 4 * (S - 100 : ℕ) / 99 := by
    have hTSR : (T : ℝ) ≤ (S - 100 : ℕ) := by exact_mod_cast hTS
    linarith only [hT, hTSR]
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℝ := (1 + eta) * C * Real.log 2 * Real.exp 3
  have hApos : 0 < A := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨S, D, hS, hD, ?_⟩
  intro p a L U y hp hy
  have h := hbound p a L U y S hp hy hS hlog
  dsimp only at h
  calc
    ((primeResidueInterval p a L U y).card : ℝ) ≤
        (((U - L) / p + 1 : ℕ) : ℝ) *
          ((1 + eta) * (C * (Real.log 2 / Real.log (y : ℝ)) * Real.exp 3)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := h
    _ = (((U - L) / p + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) +
        ((y ^ S : ℕ) : ℝ) ^ 2 := by dsimp [D]; ring

def primePredecessorBlock (p j : ℕ) : Finset ℕ :=
  primeResidueInterval p 1 (p * 4 ^ j) (p * 4 ^ (j + 1)) 0

theorem primePredecessorBlock_eq_at_cutoff {p j y : ℕ}
    (hp : 0 < p) (hy : y ≤ p * 4 ^ j) :
    primePredecessorBlock p j = primeResidueInterval p 1 (p * 4 ^ j) (p * 4 ^ (j + 1)) y := by
  ext q
  rw [primePredecessorBlock, mem_primeResidueInterval_iff, mem_primeResidueInterval_iff]
  have hL : 0 < p * 4 ^ j := by positivity
  constructor
  · rintro ⟨hlo, hhi, hprime, hzero, hmod⟩
    exact ⟨hlo, hhi, hprime, hy.trans_lt hlo, hmod⟩
  · rintro ⟨hlo, hhi, hprime, hcut, hmod⟩
    exact ⟨hlo, hhi, hprime, hL.trans hlo, hmod⟩

theorem predecessorBlock_width_div {p j : ℕ} (hp : 0 < p) :
    (p * 4 ^ (j + 1) - p * 4 ^ j) / p + 1 = 3 * 4 ^ j + 1 := by
  have hwidth : p * 4 ^ (j + 1) = p * 4 ^ j + p * (3 * 4 ^ j) := by
    rw [pow_succ]
    ring
  rw [hwidth, Nat.add_sub_cancel_left]
  simp [hp.ne']

theorem sum_inv_primePredecessorBlock_le_card_div {p j : ℕ} (hp : 0 < p) :
    ∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q ≤
      ((primePredecessorBlock p j).card : ℝ) / ((p : ℝ) * (4 : ℝ) ^ j) := by
  have h := sum_inv_primeResidueInterval_le_card_div p 1 (p * 4 ^ j) (p * 4 ^ (j + 1)) 0
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hL : (0 : ℝ) < (p : ℝ) * (4 : ℝ) ^ j := by positivity
  refine h.trans ?_
  change ((primePredecessorBlock p j).card : ℝ) / ((p : ℝ) * (4 : ℝ) ^ j + 1) ≤ _
  exact div_le_div_of_nonneg_left (by positivity) hL (by linarith)

theorem sum_inv_primePredecessorBlock_le_four_div {p j : ℕ} (hp : p.Prime) :
    ∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q ≤ (4 : ℝ) / p := by
  have hcard := card_primeResidueInterval_le_width_div_add_one
    (p := p) (a := 1) (L := p * 4 ^ j) (U := p * 4 ^ (j + 1)) (y := 0) hp
  rw [predecessorBlock_width_div hp.pos] at hcard
  have hpow1 : 1 ≤ 4 ^ j := by
    have hpos : 0 < 4 ^ j := by positivity
    omega
  have hcard' : (primePredecessorBlock p j).card ≤ 4 * 4 ^ j := by
    change (primePredecessorBlock p j).card ≤ 3 * 4 ^ j + 1 at hcard
    omega
  calc
    (∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q) ≤
        ((primePredecessorBlock p j).card : ℝ) / ((p : ℝ) * (4 : ℝ) ^ j) :=
      sum_inv_primePredecessorBlock_le_card_div hp.pos
    _ ≤ (4 * (4 : ℝ) ^ j) / ((p : ℝ) * (4 : ℝ) ^ j) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard') (by positivity)
    _ = (4 : ℝ) / p := by field_simp

/-- Beyond a fixed block index, the beta-sieve remainder is geometric and
the main term is harmonic in the block index. -/
theorem exists_primePredecessorBlock_harmonic_bound :
    ∃ S : ℕ, ∃ B : ℝ, 101 ≤ S ∧ 0 < B ∧
      ∀ p j : ℕ, p.Prime → 4 * S ≤ j →
        (∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q) ≤
          (B / (j : ℝ) + 1 / (2 : ℝ) ^ j) / p := by
  obtain ⟨S, D, hS, hD, hbound⟩ := exists_fixed_depth_primeResidueInterval_bound
  let B : ℝ := 16 * S * D / Real.log 2
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hSpos : 0 < S := by omega
  refine ⟨S, B, hS, by dsimp [B]; positivity, ?_⟩
  intro p j hp hj
  let a := j / (2 * S)
  let y := 2 ^ a
  have ha1 : 1 ≤ a := by dsimp [a]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hay : 2 ≤ y := by
    exact (by norm_num : 2 ≤ 2 ^ 1).trans (Nat.pow_le_pow_right (by norm_num) ha1)
  have haj : a ≤ j := Nat.div_le_self _ _
  have hyL : y ≤ p * 4 ^ j := by
    calc
      y ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) haj
      _ ≤ 4 ^ j := Nat.pow_le_pow_left (by norm_num) j
      _ ≤ p * 4 ^ j := by simpa using Nat.mul_le_mul_right (4 ^ j) hp.one_le
  have hset := primePredecessorBlock_eq_at_cutoff hp.pos hyL
  have hcard := hbound p 1 (p * 4 ^ j) (p * 4 ^ (j + 1)) y hp hay
  rw [← hset, predecessorBlock_width_div hp.pos] at hcard
  have hlogyEq : Real.log (y : ℝ) = (a : ℝ) * Real.log 2 := by
    simp [y, Nat.cast_pow, Real.log_pow]
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hja : j ≤ 4 * S * a := by
    have hmod := Nat.mod_lt j (show 0 < 2 * S by omega)
    have hdiv : j % (2 * S) + 2 * S * a = j := Nat.mod_add_div j (2 * S)
    have hSa : S ≤ S * a := by simpa using Nat.mul_le_mul_left S ha1
    nlinarith only [hmod, hdiv, hSa]
  have hjaR : (j : ℝ) ≤ 4 * S * a := by exact_mod_cast hja
  have hratio : D / Real.log (y : ℝ) ≤ (4 * S * D) / ((j : ℝ) * Real.log 2) := by
    apply (div_le_div_iff₀ hlogy (mul_pos hjpos hlog2)).mpr
    rw [hlogyEq]
    have hscaled := mul_le_mul_of_nonneg_right hjaR (show 0 ≤ D * Real.log 2 by positivity)
    nlinarith only [hscaled]
  have hExp : 2 * S * a ≤ j := Nat.mul_div_le j (2 * S)
  have hErrorNat : (y ^ S) ^ 2 ≤ 2 ^ j := by
    dsimp [y]
    rw [← pow_mul, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    nlinarith only [hExp]
  have hError : ((y ^ S : ℕ) : ℝ) ^ 2 ≤ (2 : ℝ) ^ j := by exact_mod_cast hErrorNat
  have hX : ((3 * 4 ^ j + 1 : ℕ) : ℝ) ≤ 4 * (4 : ℝ) ^ j := by
    have hpow1 : 1 ≤ 4 ^ j := by
      have hpos : 0 < 4 ^ j := by positivity
      omega
    exact_mod_cast (show 3 * 4 ^ j + 1 ≤ 4 * 4 ^ j by omega)
  have hcard' : ((primePredecessorBlock p j).card : ℝ) ≤
      (4 * (4 : ℝ) ^ j) * (D / Real.log (y : ℝ)) + (2 : ℝ) ^ j := by
    exact hcard.trans (add_le_add
      (mul_le_mul_of_nonneg_right hX (by positivity)) hError)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  calc
    (∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q) ≤
        ((primePredecessorBlock p j).card : ℝ) / ((p : ℝ) * (4 : ℝ) ^ j) :=
      sum_inv_primePredecessorBlock_le_card_div hp.pos
    _ ≤ ((4 * (4 : ℝ) ^ j) * (D / Real.log (y : ℝ)) + (2 : ℝ) ^ j) /
        ((p : ℝ) * (4 : ℝ) ^ j) := div_le_div_of_nonneg_right hcard' (by positivity)
    _ = (4 * (D / Real.log (y : ℝ)) + 1 / (2 : ℝ) ^ j) / p := by
      rw [show (4 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ 2 by
        rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
        norm_num]
      field_simp
    _ ≤ (4 * ((4 * S * D) / ((j : ℝ) * Real.log 2)) + 1 / (2 : ℝ) ^ j) / p := by
      gcongr
    _ = (B / (j : ℝ) + 1 / (2 : ℝ) ^ j) / p := by dsimp [B]; ring

theorem b1PrimePacket_subset_predecessorBlocks {N p : ℕ} (hp : p.Prime) :
    b1PrimePacket N p ⊆ (Finset.range (Nat.log 2 N + 1)).biUnion (primePredecessorBlock p) := by
  intro q hq
  obtain ⟨hqN, hqp, hpdiv⟩ := mem_b1PrimePacket_iff.mp hq
  let a := (q - 1) / p
  let j := Nat.log 4 a
  have hq2 : 2 ≤ q := hqp.two_le
  have hpq : p ≤ q - 1 := Nat.le_of_dvd (by omega) hpdiv
  have ha : 0 < a := Nat.div_pos hpq hp.pos
  have hpa : p * a = q - 1 := Nat.mul_div_cancel' hpdiv
  have hlow : 4 ^ j ≤ a := Nat.pow_log_le_self 4 ha.ne'
  have hhigh : a < 4 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) a
  have hL : p * 4 ^ j < q := by
    have h := Nat.mul_le_mul_left p hlow
    omega
  have hU : q ≤ p * 4 ^ (j + 1) := by
    have h := Nat.mul_le_mul_left p (show a + 1 ≤ 4 ^ (j + 1) by omega)
    have hp1 := hp.one_le
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hqp.one_le
    nlinarith only [h, hpa, hsub, hp1]
  have haN : a ≤ N := (Nat.div_le_self (q - 1) p).trans ((Nat.sub_le q 1).trans hqN)
  have hjN : j ≤ Nat.log 2 N := Nat.log_mono (by norm_num) (by norm_num) haN
  have hmod : q % p = 1 % p := ((Nat.modEq_iff_dvd' hqp.one_le).mpr hpdiv).symm
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega),
    mem_primeResidueInterval_iff.mpr ⟨hL, hU, hqp, hqp.pos, hmod⟩⟩

theorem packetPrimeMean_le_sum_predecessorBlocks {N p : ℕ} (hp : p.Prime) :
    packetPrimeMean (b1PrimePacket N p) ≤
      ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        ∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q := by
  calc
    packetPrimeMean (b1PrimePacket N p) ≤
        ∑ q ∈ (Finset.range (Nat.log 2 N + 1)).biUnion (primePredecessorBlock p),
          (1 : ℝ) / q :=
      Finset.sum_le_sum_of_subset_of_nonneg (b1PrimePacket_subset_predecessorBlocks hp)
        (fun q hq hnot ↦ by positivity)
    _ ≤ ∑ j ∈ Finset.range (Nat.log 2 N + 1),
        ∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q :=
      sum_biUnion_le_sum _ _ _ (fun j hj q hq ↦ by positivity)

theorem sum_range_succ_inv_natCast (K : ℕ) :
    (∑ j ∈ Finset.range (K + 1), (1 : ℝ) / j) = (harmonic K : ℝ) := by
  rw [Finset.sum_range_succ']
  simp [harmonic]

/-- Uniform reciprocal Brun--Titchmarsh consequence, proved here from the
finite beta sieve: the cost is one inverse modulus and a double logarithm. -/
theorem exists_packetPrimeMean_prime_modulus_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ N p : ℕ, p.Prime →
      packetPrimeMean (b1PrimePacket N p) ≤
        C * (b1DoubleLog N + 2 : ℝ) / p := by
  obtain ⟨S, B, hS, hB, hbound⟩ := exists_primePredecessorBlock_harmonic_bound
  let C : ℝ := 16 * S + 2 + B
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N p hp
  let K := Nat.log 2 N
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpoint (j : ℕ) :
      (∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q) ≤
        ((if j < 4 * S then (4 : ℝ) else 0) + B / (j : ℝ) + 1 / (2 : ℝ) ^ j) / p := by
    by_cases hj : j < 4 * S
    · refine (sum_inv_primePredecessorBlock_le_four_div hp).trans ?_
      apply div_le_div_of_nonneg_right _ hpR.le
      simp only [hj, ite_true]
      have hBj : 0 ≤ B / (j : ℝ) := by positivity
      have hgeo : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
      linarith only [hBj, hgeo]
    · simpa only [hj, ite_false, zero_add] using hbound p j hp (by omega)
  have hsmall :
      (∑ j ∈ Finset.range (K + 1), if j < 4 * S then (4 : ℝ) else 0) ≤ 16 * S := by
    have hcard : ((Finset.range (K + 1)).filter (fun j ↦ j < 4 * S)).card ≤ 4 * S := by
      calc
        ((Finset.range (K + 1)).filter (fun j ↦ j < 4 * S)).card ≤
            (Finset.range (4 * S)).card := by
          apply Finset.card_le_card
          intro j hj
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
        _ = 4 * S := Finset.card_range _
    have hcardR : (((Finset.range (K + 1)).filter (fun j ↦ j < 4 * S)).card : ℝ) ≤
        4 * S := by exact_mod_cast hcard
    have hsum : (∑ j ∈ Finset.range (K + 1), if j < 4 * S then (4 : ℝ) else 0) =
        (((Finset.range (K + 1)).filter (fun j ↦ j < 4 * S)).card : ℝ) * 4 := by
      rw [← Finset.sum_filter]
      simp
    rw [hsum]
    linarith only [hcardR]
  have hharm : (∑ j ∈ Finset.range (K + 1), B / (j : ℝ)) = B * (harmonic K : ℝ) := by
    rw [← sum_range_succ_inv_natCast K, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hgeo : (∑ j ∈ Finset.range (K + 1), (1 : ℝ) / (2 : ℝ) ^ j) ≤ 2 := by
    simpa only [div_pow, one_pow] using sum_geometric_two_le (K + 1)
  have hH : (harmonic K : ℝ) ≤ b1DoubleLog N + 2 :=
    Erdos387.PrimeReciprocal.harmonic_le_two_add_log_two K
  calc
    packetPrimeMean (b1PrimePacket N p) ≤
        ∑ j ∈ Finset.range (K + 1), ∑ q ∈ primePredecessorBlock p j, (1 : ℝ) / q :=
      packetPrimeMean_le_sum_predecessorBlocks hp
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        ((if j < 4 * S then (4 : ℝ) else 0) + B / (j : ℝ) + 1 / (2 : ℝ) ^ j) / p :=
      Finset.sum_le_sum fun j hj ↦ hpoint j
    _ = ((∑ j ∈ Finset.range (K + 1), if j < 4 * S then (4 : ℝ) else 0) +
        B * (harmonic K : ℝ) +
          (∑ j ∈ Finset.range (K + 1), (1 : ℝ) / (2 : ℝ) ^ j)) / p := by
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib, hharm]
    _ ≤ (16 * S + B * (b1DoubleLog N + 2 : ℝ) + 2) / p := by gcongr
    _ ≤ C * (b1DoubleLog N + 2 : ℝ) / p := by
      apply div_le_div_of_nonneg_right _ hpR.le
      have hZ : (1 : ℝ) ≤ b1DoubleLog N + 2 := by
        have := Nat.cast_nonneg (α := ℝ) (b1DoubleLog N)
        linarith only [this]
      have hmul := mul_le_mul_of_nonneg_left hZ (show (0 : ℝ) ≤ 16 * S + 2 by positivity)
      dsimp [C]
      nlinarith only [hmul]

#print axioms exists_packetPrimeMean_prime_modulus_upper

end Erdos822
