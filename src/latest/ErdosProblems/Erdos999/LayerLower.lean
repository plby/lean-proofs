/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.NumberTheory.WellApproximable
import ErdosProblems.Erdos220

/-!
# A lower bound for one reduced approximation layer

This file develops the one-denominator geometric estimate used in the
Pollington--Vaughan large-values argument for Erdős Problem 999.
-/

open Filter Metric Set MeasureTheory
open scoped BigOperators ENNReal MeasureTheory Topology

namespace Erdos999

noncomputable section

private lemma weighted_gap_sum_lower
    {iota : Type*} [Fintype iota] (L : ℝ) (d : iota → ℝ)
    (hL : 0 < L) (hd : ∀ i, 0 < d i) :
    L * (∑ i, d i) ^ 2 /
        (∑ i, ((d i) ^ 2 + L ^ 2)) ≤
      ∑ i, min L (d i) := by
  have hg : ∀ i ∈ (Finset.univ : Finset iota),
      0 < (d i) ^ 2 + L ^ 2 := by
    intro i hi
    positivity
  have htitu := Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ : Finset iota) d hg
  have hpoint : ∀ i : iota,
      L * ((d i) ^ 2 / ((d i) ^ 2 + L ^ 2)) ≤ min L (d i) := by
    intro i
    rw [le_min_iff]
    constructor
    · rw [← mul_div_assoc, div_le_iff₀ (hg i (Finset.mem_univ i))]
      nlinarith [sq_nonneg (d i), sq_nonneg L]
    · rw [← mul_div_assoc, div_le_iff₀ (hg i (Finset.mem_univ i))]
      nlinarith [sq_nonneg (d i - L), hd i]
  calc
    L * (∑ i, d i) ^ 2 / (∑ i, ((d i) ^ 2 + L ^ 2)) =
        L * ((∑ i, d i) ^ 2 / ∑ i, ((d i) ^ 2 + L ^ 2)) :=
      mul_div_assoc _ _ _
    _ ≤ L * ∑ i, (d i) ^ 2 / ((d i) ^ 2 + L ^ 2) :=
      mul_le_mul_of_nonneg_left htitu hL.le
    _ = ∑ i, L * ((d i) ^ 2 / ((d i) ^ 2 + L ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i, min L (d i) := Finset.sum_le_sum fun i _ ↦ hpoint i

private lemma reducedResidue_zero_eq_one {q : ℕ} (hq : 1 < q) :
    Erdos220.reducedResidue q
      ⟨0, Nat.totient_pos.mpr (by omega : 0 < q)⟩ = 1 := by
  let i0 : Fin q.totient := ⟨0, Nat.totient_pos.mpr (by omega : 0 < q)⟩
  have hpos : 0 < Erdos220.reducedResidue q i0 :=
    Erdos220.reducedResidue_pos hq i0
  have hone : 1 ∈ Erdos220.reducedResidueFinset q :=
    Erdos220.one_mem_reducedResidueFinset hq
  rw [← Erdos220.image_reducedResidue_univ] at hone
  rcases Finset.mem_image.mp hone with ⟨i, hi, hri⟩
  have hle : Erdos220.reducedResidue q i0 ≤
      Erdos220.reducedResidue q i :=
    (Erdos220.reducedResidue q).monotone
      (Fin.le_iff_val_le_val.mpr (Nat.zero_le _))
  change Erdos220.reducedResidue q i0 = 1
  omega

private lemma reducedResidue_last_eq_sub_one {q : ℕ} (hq : 1 < q) :
    Erdos220.reducedResidue q
      ⟨q.totient - 1,
        Nat.sub_lt (Nat.totient_pos.mpr (by omega : 0 < q)) (by omega)⟩ = q - 1 := by
  have hqpos : 0 < q := by omega
  have hphi : 0 < q.totient := Nat.totient_pos.mpr hqpos
  let ilast : Fin q.totient := ⟨q.totient - 1, Nat.sub_lt hphi (by omega)⟩
  have hcop : q.Coprime (q - 1) := by
    have hleft : (q - (q - 1)).Coprime (q - 1) := by
      have heq : q - (q - 1) = 1 := by omega
      rw [heq]
      exact Nat.coprime_one_left _
    exact (Nat.coprime_sub_self_left (m := q - 1) (n := q) (by omega)).mp hleft
  have hlastmem : q - 1 ∈ Erdos220.reducedResidueFinset q := by
    rw [Erdos220.mem_reducedResidueFinset]
    exact ⟨by omega, hcop⟩
  rw [← Erdos220.image_reducedResidue_univ] at hlastmem
  rcases Finset.mem_image.mp hlastmem with ⟨i, hi, hri⟩
  have hilast : i ≤ ilast := by
    apply Fin.le_iff_val_le_val.mpr
    dsimp [ilast]
    omega
  have hle : Erdos220.reducedResidue q i ≤
      Erdos220.reducedResidue q ilast :=
    (Erdos220.reducedResidue q).monotone hilast
  have hlt : Erdos220.reducedResidue q ilast < q :=
    Erdos220.reducedResidue_lt q ilast
  change Erdos220.reducedResidue q ilast = q - 1
  omega

private lemma sum_internalGap_cast_eq {q : ℕ} (hq : 1 < q) :
    ∑ k : Fin (q.totient - 1), (Erdos220.internalGap q k : ℝ) = q - 2 := by
  have hphi : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  let a : ℕ → ℝ := fun i ↦
    if hi : i < q.totient then
      ((Erdos220.reducedResidue q ⟨i, hi⟩ : ℕ) : ℝ) else 0
  let b : ℕ → ℝ := fun i ↦
    if hi : i < q.totient - 1 then
      (Erdos220.internalGap q ⟨i, hi⟩ : ℝ) else 0
  have heq :
      (∑ k : Fin (q.totient - 1), (Erdos220.internalGap q k : ℝ)) =
        ∑ k ∈ Finset.range (q.totient - 1), (a (k + 1) - a k) := by
    calc
      (∑ k : Fin (q.totient - 1), (Erdos220.internalGap q k : ℝ)) =
          ∑ k : Fin (q.totient - 1), b k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [b, k.isLt]
      _ = ∑ k ∈ Finset.range (q.totient - 1), b k := by
        rw [Fin.sum_univ_eq_sum_range]
      _ = ∑ k ∈ Finset.range (q.totient - 1), (a (k + 1) - a k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < q.totient - 1 := Finset.mem_range.mp hk
        have hk0 : k < q.totient := by omega
        have hk1 : k + 1 < q.totient := by omega
        simp only [b, dif_pos hklt, Erdos220.internalGap,
          Erdos220.gapRightIndex, Erdos220.gapLeftIndex]
        have hgap : Erdos220.reducedResidue q ⟨k, hk0⟩ ≤
            Erdos220.reducedResidue q ⟨k + 1, hk1⟩ := by
          apply Nat.le_of_lt
          apply (Erdos220.reducedResidue q).strictMono
          exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self k)
        rw [Nat.cast_sub hgap]
        simp [a, hk0, hk1]
  rw [heq]
  have htel := Finset.sum_range_sub' a (q.totient - 1)
  have hlast : q.totient - 1 < q.totient := Nat.sub_lt hphi (by omega)
  have hzero : 0 < q.totient := hphi
  calc
    (∑ k ∈ Finset.range (q.totient - 1), (a (k + 1) - a k)) =
        a (q.totient - 1) - a 0 := by
      calc
        (∑ k ∈ Finset.range (q.totient - 1), (a (k + 1) - a k)) =
            - ∑ k ∈ Finset.range (q.totient - 1), (a k - a (k + 1)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = a (q.totient - 1) - a 0 := by rw [htel]; ring
    _ = q - 2 := by
      simp only [a, dif_pos hlast, dif_pos hzero]
      rw [reducedResidue_last_eq_sub_one hq, reducedResidue_zero_eq_one hq]
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      push_cast
      ring

/-- A quantitative lower bound for the sum of truncated internal reduced-residue gaps. -/
theorem exists_internalGap_min_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (L : ℝ), 4 ≤ q → 0 < L →
      L ≤ (q : ℝ) / (2 * q.totient) →
      c * (q.totient : ℝ) * L ≤
        ∑ k : Fin (q.totient - 1),
          min L (Erdos220.internalGap q k : ℝ) := by
  obtain ⟨C, hC, hgap⟩ := Erdos220.erdos_220
  let K : ℝ := C + 1
  have hK : 0 < K := by dsimp [K]; linarith
  let c : ℝ := 1 / (4 * K)
  refine ⟨c, by dsimp [c]; positivity, ?_⟩
  intro q L hq hL hcap
  have hqpos : 0 < q := by omega
  have hphiNat : 0 < q.totient := Nat.totient_pos.mpr hqpos
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast hphiNat
  have hphiTwo : 2 ≤ q.totient := by
    rcases Nat.totient_even (by omega : 2 < q) with ⟨t, ht⟩
    omega
  let d : Fin (q.totient - 1) → ℝ := fun k ↦
    (Erdos220.internalGap q k : ℝ)
  let D : ℝ := ∑ k, d k
  let G : ℝ := ∑ k, d k ^ 2
  let H : ℝ := ∑ k, (d k ^ 2 + L ^ 2)
  have hd : ∀ k, 0 < d k := fun k ↦ by
    dsimp [d]
    exact_mod_cast Erdos220.internalGap_pos q k
  have hD : D = (q : ℝ) - 2 := by
    simpa [D, d] using sum_internalGap_cast_eq (by omega : 1 < q)
  have hG : G ≤ C * (q : ℝ) ^ 2 / q.totient := by
    have hg := hgap q (by omega : 1 ≤ q)
    rw [Erdos220.cast_sumSquaredGaps_sortedTotatives (by omega : 2 ≤ q)] at hg
    simpa [G, d, Erdos220.gapSquareSum_eq_sum_internalGap] using hg
  have hH : H = G + ((q.totient - 1 : ℕ) : ℝ) * L ^ 2 := by
    simp only [H, G, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcap' : 2 * (q.totient : ℝ) * L ≤ q := by
    have := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hphi)).mp hcap
    nlinarith
  have hLsq : ((q.totient - 1 : ℕ) : ℝ) * L ^ 2 ≤
      (q : ℝ) ^ 2 / q.totient := by
    have hcard : (((q.totient - 1 : ℕ) : ℝ)) ≤ q.totient := by
      exact_mod_cast Nat.sub_le q.totient 1
    have hfirst : (((q.totient - 1 : ℕ) : ℝ)) * L ^ 2 ≤
        (q.totient : ℝ) * L ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sq_nonneg L)
    apply hfirst.trans
    apply (le_div_iff₀ hphi).2
    have hsquare : (2 * (q.totient : ℝ) * L) ^ 2 ≤ (q : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcap' 2
    nlinarith
  have hHupper : H ≤ K * (q : ℝ) ^ 2 / q.totient := by
    rw [hH]
    calc
      G + (((q.totient - 1 : ℕ) : ℝ)) * L ^ 2 ≤
          C * (q : ℝ) ^ 2 / q.totient +
            (q : ℝ) ^ 2 / q.totient := add_le_add hG hLsq
      _ = K * (q : ℝ) ^ 2 / q.totient := by
        dsimp [K]
        ring
  have hHpos : 0 < H := by
    let k0 : Fin (q.totient - 1) := ⟨0, by omega⟩
    apply Finset.sum_pos'
    · intro k hk
      exact add_nonneg (sq_nonneg _) (sq_nonneg _)
    · refine ⟨k0, Finset.mem_univ _, ?_⟩
      nlinarith [sq_pos_of_pos (hd k0), sq_nonneg L]
  have hDsq : (q : ℝ) ^ 2 / 4 ≤ D ^ 2 := by
    rw [hD]
    have hhalf : (q : ℝ) / 2 ≤ (q : ℝ) - 2 := by
      have hqR : (4 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    calc
      (q : ℝ) ^ 2 / 4 = ((q : ℝ) / 2) ^ 2 := by ring
      _ ≤ ((q : ℝ) - 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hhalf 2
  have hfrac : c * (q.totient : ℝ) * L ≤ L * D ^ 2 / H := by
    apply (le_div_iff₀ hHpos).2
    calc
      c * (q.totient : ℝ) * L * H ≤
          c * (q.totient : ℝ) * L *
            (K * (q : ℝ) ^ 2 / q.totient) := by
        exact mul_le_mul_of_nonneg_left hHupper
          (mul_nonneg (mul_nonneg (by positivity) hphi.le) hL.le)
      _ = L * ((q : ℝ) ^ 2 / 4) := by
        dsimp [c]
        field_simp [hK.ne', hphi.ne']
      _ ≤ L * D ^ 2 := mul_le_mul_of_nonneg_left hDsq hL.le
  exact hfrac.trans (weighted_gap_sum_lower L d hL hd)

private def internalGapInterval (q : ℕ) (L : ℝ)
    (k : Fin (q.totient - 1)) : Set ℝ :=
  Ioc
    ((Erdos220.reducedResidue q (Erdos220.gapLeftIndex q k) : ℕ) / (q : ℝ))
    (((Erdos220.reducedResidue q (Erdos220.gapLeftIndex q k) : ℕ) / (q : ℝ)) +
      min L (Erdos220.internalGap q k : ℝ) / (2 * q))

private lemma measurableSet_internalGapInterval (q : ℕ) (L : ℝ)
    (k : Fin (q.totient - 1)) :
    MeasurableSet (internalGapInterval q L k) := by
  exact measurableSet_Ioc

private lemma volumeReal_internalGapInterval {q : ℕ} (hq : 0 < q)
    {L : ℝ} (hL : 0 ≤ L) (k : Fin (q.totient - 1)) :
    volume.real (internalGapInterval q L k) =
      min L (Erdos220.internalGap q k : ℝ) / (2 * q) := by
  have hgap : (0 : ℝ) ≤ Erdos220.internalGap q k := by positivity
  have hmin : 0 ≤ min L (Erdos220.internalGap q k : ℝ) := le_min hL hgap
  have hdiff : 0 ≤
      (((Erdos220.reducedResidue q (Erdos220.gapLeftIndex q k) : ℕ) /
          (q : ℝ)) + min L (Erdos220.internalGap q k : ℝ) / (2 * q)) -
        ((Erdos220.reducedResidue q (Erdos220.gapLeftIndex q k) : ℕ) /
          (q : ℝ)) := by
    exact sub_nonneg.mpr (le_add_of_nonneg_right (by positivity))
  rw [measureReal_def, internalGapInterval, Real.volume_Ioc]
  rw [ENNReal.toReal_ofReal hdiff]
  ring

private lemma internalGapInterval_upper_le_left_of_lt
    {q : ℕ} (hq : 0 < q) {L : ℝ}
    {i j : Fin (q.totient - 1)} (hij : i < j) :
    ((Erdos220.reducedResidue q (Erdos220.gapLeftIndex q i) : ℕ) / (q : ℝ)) +
        min L (Erdos220.internalGap q i : ℝ) / (2 * q) ≤
      (Erdos220.reducedResidue q (Erdos220.gapLeftIndex q j) : ℕ) / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hgap : Erdos220.reducedResidue q (Erdos220.gapLeftIndex q i) +
      Erdos220.internalGap q i =
      Erdos220.reducedResidue q (Erdos220.gapRightIndex q i) :=
    Erdos220.reducedResidue_add_internalGap q i
  have hidx : Erdos220.gapRightIndex q i ≤ Erdos220.gapLeftIndex q j := by
    apply Fin.le_iff_val_le_val.mpr
    simpa [Erdos220.gapRightIndex, Erdos220.gapLeftIndex] using hij
  have hres : Erdos220.reducedResidue q (Erdos220.gapRightIndex q i) ≤
      Erdos220.reducedResidue q (Erdos220.gapLeftIndex q j) :=
    (Erdos220.reducedResidue q).monotone hidx
  have hgapR :
      (Erdos220.reducedResidue q (Erdos220.gapLeftIndex q i) : ℝ) +
          (Erdos220.internalGap q i : ℝ) =
        (Erdos220.reducedResidue q (Erdos220.gapRightIndex q i) : ℝ) := by
    exact_mod_cast hgap
  have hresR :
      (Erdos220.reducedResidue q (Erdos220.gapRightIndex q i) : ℝ) ≤
        (Erdos220.reducedResidue q (Erdos220.gapLeftIndex q j) : ℝ) := by
    exact_mod_cast hres
  have hhalf : min L (Erdos220.internalGap q i : ℝ) / 2 ≤
      Erdos220.internalGap q i := by
    have hgap0 : (0 : ℝ) ≤ Erdos220.internalGap q i := by positivity
    nlinarith [min_le_right L (Erdos220.internalGap q i : ℝ)]
  rw [show min L (Erdos220.internalGap q i : ℝ) / (2 * q) =
      (min L (Erdos220.internalGap q i : ℝ) / 2) / q by ring,
    ← add_div, div_le_div_iff_of_pos_right hqR]
  nlinarith

private lemma pairwise_disjoint_internalGapInterval {q : ℕ} (hq : 0 < q)
    {L : ℝ} :
    Pairwise (fun i j ↦
      Disjoint (internalGapInterval q L i) (internalGapInterval q L j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hsep := internalGapInterval_upper_le_left_of_lt (L := L) hq hijlt
    exact (not_lt_of_ge (hxi.2.trans hsep)) hxj.1
  · have hsep := internalGapInterval_upper_le_left_of_lt (L := L) hq hjilt
    exact (not_lt_of_ge (hxj.2.trans hsep)) hxi.1

private lemma internalGapInterval_subset_preimage_layer
    {q : ℕ} (hq : 4 ≤ q) {L : ℝ} (hL : 0 < L)
    (hcap : L ≤ (q : ℝ) / (2 * q.totient))
    (k : Fin (q.totient - 1)) :
    internalGapInterval q L k ⊆
      ((↑) : ℝ → UnitAddCircle) ⁻¹'
        approxAddOrderOf UnitAddCircle q (L / q) ∩ Ioc 0 1 := by
  intro x hx
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hphi : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr hqpos
  let a : ℕ := Erdos220.reducedResidue q (Erdos220.gapLeftIndex q k)
  have haPos : 0 < a := Erdos220.reducedResidue_pos (by omega) _
  have haLt : a < q := Erdos220.reducedResidue_lt q _
  have haCop : q.Coprime a := Erdos220.reducedResidue_coprime q _
  have hgap0 : (0 : ℝ) ≤ Erdos220.internalGap q k := by positivity
  have hmin0 : 0 ≤ min L (Erdos220.internalGap q k : ℝ) :=
    le_min hL.le hgap0
  have hxlower : (a : ℝ) / q < x := by simpa [internalGapInterval, a] using hx.1
  have hxupper : x ≤ (a : ℝ) / q +
      min L (Erdos220.internalGap q k : ℝ) / (2 * q) := by
    simpa [internalGapInterval, a] using hx.2
  have hxdiff0 : 0 < x - (a : ℝ) / q := sub_pos.mpr hxlower
  have hxdiff : x - (a : ℝ) / q < L / q := by
    have hminle : min L (Erdos220.internalGap q k : ℝ) ≤ L := min_le_left _ _
    have hhalf : min L (Erdos220.internalGap q k : ℝ) / (2 * q) < L / q := by
      calc
        min L (Erdos220.internalGap q k : ℝ) / (2 * q) ≤
            L / (2 * q) :=
          div_le_div_of_nonneg_right hminle (by positivity)
        _ < L / q := by
          rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * q) hqR]
          nlinarith
    linarith
  have hxdiffhalf : |x - (a : ℝ) / q| ≤ (1 : ℝ) / 2 := by
    rw [abs_of_pos hxdiff0]
    have htotient_one : (1 : ℝ) ≤ q.totient := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt
        (Nat.totient_pos.mpr hqpos))
    have hLhalf : L / q ≤ (1 : ℝ) / 2 := by
      apply (div_le_iff₀ hqR).2
      have := hcap
      have hden : 0 < 2 * (q.totient : ℝ) := by positivity
      have hLq : L * (2 * q.totient) ≤ q := (le_div_iff₀ hden).mp hcap
      nlinarith
    exact hxdiff.le.trans hLhalf
  constructor
  · change (x : UnitAddCircle) ∈ approxAddOrderOf UnitAddCircle q (L / q)
    rw [UnitAddCircle.mem_approxAddOrderOf_iff hqpos]
    refine ⟨a, haLt, haCop.symm.gcd_eq_one, ?_⟩
    rw [← QuotientAddGroup.mk_sub]
    rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2
      (by simpa using hxdiffhalf)]
    simpa [abs_of_pos hxdiff0] using hxdiff
  · constructor
    · have : (0 : ℝ) < (a : ℝ) / q := div_pos (by exact_mod_cast haPos) hqR
      linarith
    · have hgap_le_q : Erdos220.internalGap q k ≤ q :=
        Erdos220.internalGap_le_n q k
      have hmin_le_q : min L (Erdos220.internalGap q k : ℝ) ≤ q := by
        exact (min_le_right _ _).trans (by exact_mod_cast hgap_le_q)
      have ha_le_nat : a ≤ q - 1 := by omega
      have ha_le : (a : ℝ) ≤ (q : ℝ) - 1 := by
        rw [← Nat.cast_one, ← Nat.cast_sub (by omega : 1 ≤ q)]
        exact_mod_cast ha_le_nat
      have hgap_eq : a + Erdos220.internalGap q k =
          Erdos220.reducedResidue q (Erdos220.gapRightIndex q k) :=
        Erdos220.reducedResidue_add_internalGap q k
      have hright_lt :
          Erdos220.reducedResidue q (Erdos220.gapRightIndex q k) < q :=
        Erdos220.reducedResidue_lt q _
      have hgap_eqR : (a : ℝ) + (Erdos220.internalGap q k : ℝ) =
          (Erdos220.reducedResidue q (Erdos220.gapRightIndex q k) : ℝ) := by
        exact_mod_cast hgap_eq
      have hright_leR :
          (Erdos220.reducedResidue q (Erdos220.gapRightIndex q k) : ℝ) ≤ q := by
        exact_mod_cast (Nat.le_of_lt hright_lt)
      have hadd_le : (a : ℝ) / q +
          min L (Erdos220.internalGap q k : ℝ) / (2 * q) ≤ 1 := by
        rw [show min L (Erdos220.internalGap q k : ℝ) / (2 * q) =
            (min L (Erdos220.internalGap q k : ℝ) / 2) / q by ring,
          ← add_div, div_le_iff₀ hqR]
        nlinarith [min_le_right L (Erdos220.internalGap q k : ℝ), hmin0]
      exact hxupper.trans hadd_le

/-- For all denominators at least four, one approximation layer has measure
bounded below by an absolute constant times its normalized weight. -/
theorem exists_largeValueLayer_lower_of_four_le :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (L : ℝ), 4 ≤ q → 0 < L →
      L ≤ (q : ℝ) / (2 * q.totient) →
      c * ((q.totient : ℝ) * L / q) ≤
        volume.real (approxAddOrderOf UnitAddCircle q (L / q)) := by
  obtain ⟨c, hc, hgap⟩ := exists_internalGap_min_lower
  refine ⟨c / 2, by positivity, ?_⟩
  intro q L hq hL hcap
  have hqpos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  let V : Set ℝ := ⋃ k : Fin (q.totient - 1), internalGapInterval q L k
  have hVmeas : MeasurableSet V :=
    MeasurableSet.iUnion fun k ↦ measurableSet_internalGapInterval q L k
  have hVvolume : volume.real V =
      ∑ k : Fin (q.totient - 1),
        min L (Erdos220.internalGap q k : ℝ) / (2 * q) := by
    rw [measureReal_iUnion_fintype
      (pairwise_disjoint_internalGapInterval hqpos)
      (fun k ↦ measurableSet_internalGapInterval q L k)
      (h' := fun k ↦ by simp [internalGapInterval, Real.volume_Ioc])]
    apply Finset.sum_congr rfl
    intro k hk
    exact volumeReal_internalGapInterval hqpos hL.le k
  have hVsubset : V ⊆
      ((↑) : ℝ → UnitAddCircle) ⁻¹'
        approxAddOrderOf UnitAddCircle q (L / q) ∩ Ioc 0 1 := by
    intro x hx
    rcases mem_iUnion.mp hx with ⟨k, hk⟩
    exact internalGapInterval_subset_preimage_layer hq hL hcap k hk
  have hprojection := AddCircle.add_projection_respects_measure (1 : ℝ) 0
    (isOpen_thickening.measurableSet :
      MeasurableSet (approxAddOrderOf UnitAddCircle q (L / q)))
  have htargetfinite :
      volume (((↑) : ℝ → UnitAddCircle) ⁻¹'
        approxAddOrderOf UnitAddCircle q (L / q) ∩ Ioc 0 1) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_right (by simp [Real.volume_Ioc])
  have hmeasureMono : volume.real V ≤
      volume.real (((↑) : ℝ → UnitAddCircle) ⁻¹'
        approxAddOrderOf UnitAddCircle q (L / q) ∩ Ioc 0 1) :=
    measureReal_mono hVsubset htargetfinite
  simp only [zero_add] at hprojection
  have hprojectionReal :
      volume.real (approxAddOrderOf UnitAddCircle q (L / q)) =
        volume.real (((↑) : ℝ → UnitAddCircle) ⁻¹'
          approxAddOrderOf UnitAddCircle q (L / q) ∩ Ioc 0 1) := by
    exact congrArg ENNReal.toReal
      (by simpa only [approxAddOrderOf] using hprojection)
  rw [← hprojectionReal] at hmeasureMono
  calc
    (c / 2) * ((q.totient : ℝ) * L / q) =
        (c * (q.totient : ℝ) * L) / (2 * q) := by ring
    _ ≤ (∑ k : Fin (q.totient - 1),
        min L (Erdos220.internalGap q k : ℝ)) / (2 * q) := by
      exact div_le_div_of_nonneg_right (hgap q L hq hL hcap) (by positivity)
    _ = volume.real V := by
      rw [hVvolume, Finset.sum_div]
    _ ≤ volume.real (approxAddOrderOf UnitAddCircle q (L / q)) := hmeasureMono

end

end Erdos999
