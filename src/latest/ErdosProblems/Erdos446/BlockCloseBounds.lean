/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.BlockMassBounds

/-!
# Erdős Problem 446: sharp close-pair bounds for capped block classes

This module relates the prefix exponent in the largest-differing-prime
estimate to `compositionPenalty`.  It then controls the repeated reciprocal
block masses by their geometrically summable relative errors.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

theorem prefixProductMass_eq_sum_take_succ (l : List ℝ) :
    prefixProductMass l =
      ∑ r ∈ Finset.range l.length, (l.take (r + 1)).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
      rw [prefixProductMass_cons, List.length_cons,
        Finset.sum_range_succ']
      simp only [List.take_succ_cons, List.take_zero, List.prod_cons,
        List.prod_nil, ih]
      rw [mul_add, Finset.mul_sum]
      ring

theorem sum_two_pow_range_le (n : ℕ) :
    (∑ t ∈ Finset.range n, (2 : ℝ) ^ t) ≤ (2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      linarith

noncomputable def compositionPrefixTerm {K : ℕ} (b : Fin K → ℕ)
    (i : Fin K) : ℝ :=
  (2 : ℝ) ^ (∑ q ∈ Finset.Iic i, b q) /
    (2 : ℝ) ^ (i.val + 1)

theorem compositionFactor_take_prod {K : ℕ} (b : Fin K → ℕ)
    (i : Fin K) :
    ((List.ofFn (compositionFactor b)).take (i.val + 1)).prod =
      compositionPrefixTerm b i := by
  rw [List.prod_take_ofFn]
  have hfilter :
      (Finset.univ.filter (fun j : Fin K ↦ j.val < i.val + 1)) =
        Finset.Iic i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iic]
    omega
  rw [hfilter]
  dsimp [compositionPrefixTerm]
  simp only [compositionFactor]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_const, Fin.card_Iic]

theorem compositionPenalty_eq_sum_prefixTerm {K : ℕ} (b : Fin K → ℕ) :
    compositionPenalty b = ∑ i : Fin K, compositionPrefixTerm b i := by
  rw [compositionPenalty, prefixProductMass_eq_sum_take_succ]
  simp only [List.length_ofFn]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  exact compositionFactor_take_prod b i

/-- The bit-mask exponent sum is at most `4 / 2^M` times Ford's cyclic
prefix penalty. -/
theorem closeExponentSum_le_penalty {M K : ℕ} (b : Fin K → ℕ) :
    (∑ s : BlockSlot K (extendComposition b),
        (2 : ℝ) ^
          ((∑ q ∈ Finset.Iio s.1, b q) +
            s.2.val + 1) /
          (2 : ℝ) ^ (M + s.1.val)) ≤
      (4 / (2 : ℝ) ^ M) * compositionPenalty b := by
  rw [Fintype.sum_sigma]
  have hblock : ∀ i : Fin K,
      (∑ t : Fin (extendComposition b i),
          (2 : ℝ) ^
            ((∑ q ∈ Finset.Iio i, b q) +
              t.val + 1) /
            (2 : ℝ) ^ (M + i.val)) ≤
        (4 / (2 : ℝ) ^ M) * compositionPrefixTerm b i := by
    intro i
    rw [extendComposition_fin]
    let P : ℕ := ∑ q ∈ Finset.Iio i, b q
    calc
      (∑ t : Fin (b i),
          (2 : ℝ) ^ (P + t.val + 1) /
            (2 : ℝ) ^ (M + i.val)) =
          ((2 : ℝ) ^ (P + 1) / (2 : ℝ) ^ (M + i.val)) *
            ∑ t ∈ Finset.range (b i), (2 : ℝ) ^ t := by
        rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro t ht
        rw [pow_add, pow_add]
        field_simp
        rw [pow_succ]
      _ ≤ ((2 : ℝ) ^ (P + 1) / (2 : ℝ) ^ (M + i.val)) *
            (2 : ℝ) ^ (b i) := by
        apply mul_le_mul_of_nonneg_left (sum_two_pow_range_le (b i))
        positivity
      _ = (4 / (2 : ℝ) ^ M) * compositionPrefixTerm b i := by
        dsimp [compositionPrefixTerm, P]
        rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons]
        field_simp
        rw [pow_add, pow_add]
        ring
  calc
    (∑ i : Fin K, ∑ t : Fin (extendComposition b i),
          (2 : ℝ) ^
          ((∑ q ∈ Finset.Iio i, b q) +
            t.val + 1) /
          (2 : ℝ) ^ (M + i.val)) ≤
        ∑ i : Fin K,
          (4 / (2 : ℝ) ^ M) * compositionPrefixTerm b i :=
      Finset.sum_le_sum fun i hi ↦ hblock i
    _ = (4 / (2 : ℝ) ^ M) * compositionPenalty b := by
      rw [← Finset.mul_sum, ← compositionPenalty_eq_sum_prefixTerm]

theorem sum_range_extendComposition_eq_sum_Iio {K : ℕ}
    (b : Fin K → ℕ) (i : Fin K) :
    (∑ q ∈ Finset.range i.val, extendComposition b q) =
      ∑ q ∈ Finset.Iio i, b q := by
  rw [← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro q hq
  exact extendComposition_fin b q

theorem half_le_compositionPenalty {K : ℕ} (hK : 0 < K)
    (b : Fin K → ℕ) : (1 / 2 : ℝ) ≤ compositionPenalty b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hK.ne'
  rw [compositionPenalty, List.ofFn_succ, prefixProductMass_cons]
  have hfirst : (1 / 2 : ℝ) ≤ compositionFactor b 0 := by
    dsimp [compositionFactor]
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ b 0 := one_le_pow₀ (by norm_num)
    linarith
  have htail : 0 ≤ prefixProductMass
      (List.ofFn fun i : Fin k ↦ compositionFactor b i.succ) := by
    apply prefixProductMass_nonneg
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (compositionFactor_pos b i.succ).le
  calc
    (1 / 2 : ℝ) ≤ compositionFactor b 0 := hfirst
    _ ≤ compositionFactor b 0 *
        (1 + prefixProductMass
          (List.ofFn fun i : Fin k ↦ compositionFactor b i.succ)) := by
      nlinarith [compositionFactor_pos b 0]

/-- Relative Mertens error attached to one repeated prime slot. -/
noncomputable def blockMassRelativeError {K : ℕ} (C : ℝ) (M : ℕ)
    (b : Fin K → ℕ) (s : BlockSlot K (extendComposition b)) : ℝ :=
  (C / Real.log 2) / (2 : ℝ) ^ (M + s.1.val)

theorem blockMassRelativeError_nonneg {K : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (M : ℕ) (b : Fin K → ℕ)
    (s : BlockSlot K (extendComposition b)) :
    0 ≤ blockMassRelativeError C M b s := by
  dsimp [blockMassRelativeError]
  positivity

theorem blockMassRelativeError_sum_le {M K : ℕ} {C : ℝ} (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hcap : ∀ i : Fin K,
      extendComposition b i ≤ (M * M) * (i.val + 1)) :
    (∑ s : BlockSlot K (extendComposition b),
        blockMassRelativeError C M b s) ≤
      4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M := by
  simpa only [blockMassRelativeError, Nat.cast_mul] using
    (slot_geometric_error_sum_le
      (M := M) (k := K) (K := M * M) (b := extendComposition b)
      (C := C / Real.log 2) (by positivity) hcap)

theorem primeBlockMass_upper_relative
    {M K : ℕ} {C : ℝ} {b : Fin K → ℕ}
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (s : BlockSlot K (extendComposition b)) :
    primeBlockMass (M + s.1) ≤
      Real.log 2 * (1 + blockMassRelativeError C M b s) := by
  have hu := le_of_abs_le (hmass s.1)
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  dsimp [blockMassRelativeError]
  calc
    primeBlockMass (M + s.1) ≤
        Real.log 2 + C / (2 : ℝ) ^ (M + s.1.val) := by linarith
    _ = Real.log 2 *
        (1 + (C / Real.log 2) /
          (2 : ℝ) ^ (M + s.1.val)) := by
      field_simp [hlog]

/-- Product of all repeated block masses, with only an absolute exponential
of the total geometric error. -/
theorem slotMassProduct_upper
    {M K : ℕ} {C E : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E) :
    (∏ s : BlockSlot K (extendComposition b),
        primeBlockMass (M + s.1)) ≤
      Real.log 2 ^ K * Real.exp E := by
  let z : BlockSlot K (extendComposition b) → ℝ :=
    blockMassRelativeError C M b
  have hcap := cappedComposition_linear_cap (M := M) hM hb
  have hz0 : ∀ s, 0 ≤ z s :=
    fun s ↦ blockMassRelativeError_nonneg hC M b s
  have hp := prod_upper_of_relative_error
    (Real.log 2) (Real.log_pos one_lt_two).le
    (fun s : BlockSlot K (extendComposition b) ↦
      primeBlockMass (M + s.1)) z
    (fun s ↦ primeBlockMass_nonneg _) hz0
    (primeBlockMass_upper_relative hmass)
  rw [card_blockSlot_extendComposition_of_mem hb] at hp
  have hsum : (∑ s, z s) ≤ E :=
    (blockMassRelativeError_sum_le hC hcap).trans hE
  exact hp.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr hsum) (by positivity))

theorem slotMassProductAway_upper
    {M K : ℕ} {C E : ℝ} (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (s : BlockSlot K (extendComposition b)) :
    (∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
        primeBlockMass (M + t.1.1)) ≤
      2 * Real.log 2 ^ (K - 1) * Real.exp E := by
  let f : BlockSlot K (extendComposition b) → ℝ :=
    fun t ↦ primeBlockMass (M + t.1)
  let P : ℝ := ∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
    f t.1
  have hP0 : 0 ≤ P := by
    dsimp [P, f]
    exact Finset.prod_nonneg fun t ht ↦ primeBlockMass_nonneg _
  have hfull := slotMassProduct_upper hM hC hb hmass hE
  have hsplit := Fintype.prod_eq_mul_prod_subtype_ne f s
  have hmul : (Real.log 2 / 2) * P ≤
      Real.log 2 ^ K * Real.exp E := by
    calc
      (Real.log 2 / 2) * P ≤ f s * P :=
        mul_le_mul_of_nonneg_right (hhalf s.1) hP0
      _ = ∏ t : BlockSlot K (extendComposition b), f t := hsplit.symm
      _ ≤ Real.log 2 ^ K * Real.exp E := by simpa [f] using hfull
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hpow : Real.log 2 ^ K =
      Real.log 2 * Real.log 2 ^ (K - 1) := by
    calc
      Real.log 2 ^ K = Real.log 2 ^ ((K - 1) + 1) := by congr 1 <;> omega
      _ = Real.log 2 ^ (K - 1) * Real.log 2 := by rw [pow_succ]
      _ = Real.log 2 * Real.log 2 ^ (K - 1) := by ring
  change P ≤ _
  apply (le_of_mul_le_mul_left _ (show 0 < Real.log 2 / 2 by positivity))
  calc
    (Real.log 2 / 2) * P ≤ Real.log 2 ^ K * Real.exp E := hmul
    _ = (Real.log 2 / 2) *
        (2 * Real.log 2 ^ (K - 1) * Real.exp E) := by
      rw [hpow]
      field_simp [hlog.ne']

/-- The sharp close-pair estimate for one capped vector.  All dependence on
the vector is confined to `compositionPenalty`; the remaining factor is a
constant multiple of `(2 * log 2)^K`. -/
theorem compositionBlockFamily_closeWeight_upper
    {N M K : ℕ} {C E : ℝ}
    (hM : 1 ≤ M) (hK : 0 < K) (hC : 0 ≤ C)
    {b : Fin K → ℕ} (hb : b ∈ cappedCompositions M K)
    (hmass : ∀ i : Fin K,
      |primeBlockMass (M + i) - Real.log 2| ≤
        C / (2 : ℝ) ^ (M + i.val))
    (hhalf : ∀ i : Fin K,
      Real.log 2 / 2 ≤ primeBlockMass (M + i))
    (hE : 4 * (M * M) * (C / Real.log 2) / (2 : ℝ) ^ M ≤ E)
    (hN : 3 ≤ N) (hendpoint : ∀ i : Fin K, N ≤ blockEndpoint (M + i))
    (hprime : ∀ t : ℕ, N ≤ t →
      dyadicPrimeMass t ≤ 3 / Real.log (t : ℝ)) :
    compositionFactorial b *
        (∑ a ∈ compositionBlockFamily M b,
          (closePairCount a : ℝ) / a) ≤
      ((2 * Real.log 2 : ℝ) ^ K * Real.exp E *
        (2 + 56 /
          (Real.log 2 ^ 2 * (2 : ℝ) ^ M))) *
        compositionPenalty b := by
  let Base : ℝ := (2 * Real.log 2 : ℝ) ^ K * Real.exp E
  let Q : ℝ := 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M)
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hBase0 : 0 ≤ Base := by dsimp [Base]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hfull := slotMassProduct_upper hM hC hb hmass hE
  have haway := slotMassProductAway_upper hM hK hC hb hmass hhalf hE
  have hexact := blockFamily_closeWeight_upper_exact
    (N := N) (M := M) (k := K) (b := extendComposition b)
    hN hendpoint hprime
  rw [slotCount_extendComposition_of_mem hb] at hexact
  have hdiag :
      (2 : ℝ) ^ K *
          (∏ s : BlockSlot K (extendComposition b),
            primeBlockMass (M + s.1)) ≤ Base := by
    calc
      (2 : ℝ) ^ K *
          (∏ s : BlockSlot K (extendComposition b),
            primeBlockMass (M + s.1)) ≤
          (2 : ℝ) ^ K * (Real.log 2 ^ K * Real.exp E) :=
        mul_le_mul_of_nonneg_left hfull (by positivity)
      _ = Base := by
        dsimp [Base]
        rw [mul_pow]
        ring
  have hterm : ∀ s : BlockSlot K (extendComposition b),
      (2 : ℝ) ^
          (K +
            ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
              s.2.val) + 1) *
          ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) ≤
        (Base * (14 / Real.log 2 ^ 2)) *
          ((2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
            (2 : ℝ) ^ (M + s.1.val)) := by
    intro s
    have hpref := sum_range_extendComposition_eq_sum_Iio b s.1
    have ha := haway s
    have hlogEndpoint := log_blockEndpoint (M + s.1.val)
    have hpowers :
        (2 : ℝ) ^
            (K +
              ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
                s.2.val) + 1) =
          (2 : ℝ) ^ K *
            (2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) := by
      rw [hpref]
      rw [show K + ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val) + 1 =
        K + ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) by omega,
        pow_add]
    rw [hpowers, hlogEndpoint]
    have hpow0 : 0 ≤ (2 : ℝ) ^ K *
        (2 : ℝ) ^ ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) := by
      positivity
    calc
      ((2 : ℝ) ^ K *
            (2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1)) *
          ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / ((2 : ℝ) ^ (M + s.1.val) * Real.log 2))) ≤
        ((2 : ℝ) ^ K *
            (2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1)) *
          ((2 * Real.log 2 ^ (K - 1) * Real.exp E) *
            (7 / ((2 : ℝ) ^ (M + s.1.val) * Real.log 2))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_right ha
          positivity
        · exact hpow0
      _ = (Base * (14 / Real.log 2 ^ 2)) *
          ((2 : ℝ) ^
              ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
            (2 : ℝ) ^ (M + s.1.val)) := by
        dsimp [Base]
        have hpowK : Real.log 2 ^ K =
            Real.log 2 * Real.log 2 ^ (K - 1) := by
          calc
            Real.log 2 ^ K = Real.log 2 ^ ((K - 1) + 1) := by
              congr 1 <;> omega
            _ = Real.log 2 ^ (K - 1) * Real.log 2 := by rw [pow_succ]
            _ = _ := by ring
        rw [mul_pow, hpowK]
        field_simp [hlog.ne']
        ring
  have hnondiag :
      (∑ s : BlockSlot K (extendComposition b),
        (2 : ℝ) ^
          (K +
            ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
              s.2.val) + 1) *
          ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
              primeBlockMass (M + t.1.1)) *
            (7 / Real.log (blockEndpoint (M + s.1) : ℝ)))) ≤
        Base * Q * compositionPenalty b := by
    calc
      _ ≤ ∑ s : BlockSlot K (extendComposition b),
          (Base * (14 / Real.log 2 ^ 2)) *
            ((2 : ℝ) ^
                ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
              (2 : ℝ) ^ (M + s.1.val)) :=
        Finset.sum_le_sum fun s hs ↦ hterm s
      _ = (Base * (14 / Real.log 2 ^ 2)) *
          (∑ s : BlockSlot K (extendComposition b),
            (2 : ℝ) ^
                ((∑ q ∈ Finset.Iio s.1, b q) + s.2.val + 1) /
              (2 : ℝ) ^ (M + s.1.val)) := by rw [Finset.mul_sum]
      _ ≤ (Base * (14 / Real.log 2 ^ 2)) *
          ((4 / (2 : ℝ) ^ M) * compositionPenalty b) := by
        apply mul_le_mul_of_nonneg_left (closeExponentSum_le_penalty b)
        positivity
      _ = Base * Q * compositionPenalty b := by
        dsimp [Q]
        field_simp [hlog.ne']
        ring
  have hpen := half_le_compositionPenalty hK b
  have hdiagPen : Base ≤ Base * 2 * compositionPenalty b := by
    calc
      Base = Base * 1 := by ring
      _ ≤ Base * (2 * compositionPenalty b) := by
        apply mul_le_mul_of_nonneg_left
        · linarith
        · exact hBase0
      _ = _ := by ring
  change compositionFactorial b *
      (∑ a ∈ blockFamily M K (extendComposition b),
        (closePairCount a : ℝ) / a) ≤ _
  calc
    compositionFactorial b *
        (∑ a ∈ blockFamily M K (extendComposition b),
          (closePairCount a : ℝ) / a) ≤
      (2 : ℝ) ^ K *
          (∏ s : BlockSlot K (extendComposition b),
            primeBlockMass (M + s.1)) +
        ∑ s : BlockSlot K (extendComposition b),
          (2 : ℝ) ^
            (K +
              ((∑ i ∈ Finset.range s.1.val, extendComposition b i) +
                s.2.val) + 1) *
            ((∏ t : {t : BlockSlot K (extendComposition b) // t ≠ s},
                primeBlockMass (M + t.1.1)) *
              (7 / Real.log (blockEndpoint (M + s.1) : ℝ))) := by
      simpa only [compositionFactorial, extendComposition_fin] using hexact
    _ ≤ Base + Base * Q * compositionPenalty b := add_le_add hdiag hnondiag
    _ ≤ Base * 2 * compositionPenalty b +
        Base * Q * compositionPenalty b := add_le_add hdiagPen le_rfl
    _ = (Base * (2 + Q)) * compositionPenalty b := by ring
    _ = (((2 * Real.log 2 : ℝ) ^ K * Real.exp E *
          (2 + 56 / (Real.log 2 ^ 2 * (2 : ℝ) ^ M))) *
        compositionPenalty b) := by rfl

end Erdos446
