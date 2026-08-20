/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedLowerVolumeCore
import ErdosProblems.Erdos446.SmirnovSplitMass
import ErdosProblems.Erdos446.ShiftedAbelConvolution
import ErdosProblems.Erdos446.UpperBlockOccupancy
import ErdosProblems.Erdos446.SmirnovQuantitative

/-!
# Erdős Problem 446: splitting the fixed-lower prefix energy

This file isolates the finite first-moment calculation used in Ford's
fixed-multiplicity lower bound.  Every result below is a statement about
finite occupancy vectors.  The main decomposition splits a good occupancy
at a marked prefix and records both residual Smirnov barriers.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Every summand of the prefix energy is at most one on the one-slack
Smirnov region. -/
theorem compositionPrefixTerm_le_one_of_mem_smirnov
    {k : ℕ} {c : Fin k → ℕ} (hc : c ∈ smirnovOccupancies k 1 k)
    (i : Fin k) : compositionPrefixTerm c i ≤ 1 := by
  have hpref := (mem_smirnovOccupancies.mp hc).2
    (i.val + 1) (by omega) (by omega)
  have hsum : (∑ q ∈ Finset.Iic i, c q) ≤ i.val + 1 := by
    have hid : occupancyPrefix c (i.val + 1) =
        ∑ q ∈ Finset.Iic i, c q := by
      rw [occupancyPrefix]
      congr 1
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_Iic]
      omega
    rw [← hid]
    omega
  dsimp [compositionPrefixTerm]
  have hpow : (2 : ℝ) ^ (∑ q ∈ Finset.Iic i, c q) ≤
      (2 : ℝ) ^ (i.val + 1) := by
    exact pow_le_pow_right₀ (by norm_num) hsum
  exact (div_le_one (by positivity)).2 hpow

/-- The complete prefix energy is at most the number of coordinates. -/
theorem fixedLowerPrefixEnergy_le_card
    {k : ℕ} {c : Fin k → ℕ} (hc : c ∈ smirnovOccupancies k 1 k) :
    fixedLowerPrefixEnergy c ≤ (k : ℝ) := by
  rw [fixedLowerPrefixEnergy, compositionPenalty_eq_sum_prefixTerm]
  calc
    (∑ i : Fin k, compositionPrefixTerm c i) ≤ ∑ _i : Fin k, (1 : ℝ) :=
      Finset.sum_le_sum fun i _hi ↦
        compositionPrefixTerm_le_one_of_mem_smirnov hc i
    _ = (k : ℝ) := by simp

/-- A coarse bound, useful for the finitely many small parameters before
the uniform Smirnov estimate is invoked. -/
theorem fixedLowerPrefixEnergyMoment_le_card_mul_mass (k : ℕ) :
    fixedLowerPrefixEnergyMoment k ≤
      (k : ℝ) * smirnovOccupancyMass k 1 k := by
  rw [fixedLowerPrefixEnergyMoment, smirnovOccupancyMass,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  rw [div_eq_mul_inv, one_div]
  exact mul_le_mul_of_nonneg_right
    (fixedLowerPrefixEnergy_le_card hc)
    (inv_nonneg.mpr (by
      dsimp [compositionFactorial]
      positivity))

/-! ## Exact splitting of a marked prefix -/

/-- Prefixes of length at most the splitting point are unaffected by
reassembling the two pieces. -/
theorem occupancyPrefix_splitAt_le
    (v h : ℕ) (hh : h ≤ v)
    (a : Fin h → ℕ) (b : Fin (v - h) → ℕ)
    {t : ℕ} (ht : t ≤ h) :
    occupancyPrefix (splitAtCompositionEquiv v h hh (a, b)) t =
      occupancyPrefix a t := by
  rw [occupancyPrefix_eq_sum_take_ofFn,
    ofFn_splitAtCompositionEquiv, List.take_append_of_le_length]
  · rw [occupancyPrefix_eq_sum_take_ofFn]
  · simpa using ht

private theorem sum_le_length_of_smirnov_one
    {s h : ℕ} {a : Fin h → ℕ}
    (ha : a ∈ smirnovOccupancies s 1 h) : s ≤ h := by
  have haData := mem_smirnovOccupancies.mp ha
  by_cases hh : h = 0
  · subst h
    simpa using haData.1.symm
  · have hbarrier := haData.2 h (by omega) le_rfl
    rw [occupancyPrefix_at_length, haData.1] at hbarrier
    omega

/-- Exact residual-barrier description after splitting a one-slack
occupancy.  If the prefix has mass `s`, the tail has offset `h + 1 - s`.
-/
theorem splitAtCompositionEquiv_mem_smirnovOccupancies_iff_exists
    {k h : ℕ} (hh : h ≤ k)
    (a : Fin h → ℕ) (b : Fin (k - h) → ℕ) :
    splitAtCompositionEquiv k h hh (a, b) ∈
        smirnovOccupancies k 1 k ↔
      ∃ s : ℕ,
        (∑ i, a i) = s ∧
        (∑ i, b i) = k - s ∧
        a ∈ smirnovOccupancies s 1 h ∧
        b ∈ smirnovOccupancies (k - s) (h + 1 - s) (k - h) := by
  constructor
  · intro hc
    have hcData := mem_smirnovOccupancies.mp hc
    let s := ∑ i, a i
    have hsum := sum_splitAtCompositionEquiv k h hh a b
    have hbSum : (∑ i, b i) = k - s := by
      rw [hcData.1] at hsum
      dsimp [s]
      omega
    have haMem : a ∈ smirnovOccupancies s 1 h := by
      rw [mem_smirnovOccupancies]
      refine ⟨rfl, ?_⟩
      intro t ht hth
      have hglobal := hcData.2 t ht (hth.trans hh)
      rw [occupancyPrefix_splitAt_le k h hh a b hth] at hglobal
      exact hglobal
    have hsle : s ≤ h := sum_le_length_of_smirnov_one haMem
    have hbMem : b ∈ smirnovOccupancies (k - s) (h + 1 - s) (k - h) := by
      rw [mem_smirnovOccupancies]
      refine ⟨hbSum, ?_⟩
      intro q hq hqkh
      have hglobal := hcData.2 (h + q) (by omega) (by omega)
      rw [occupancyPrefix_splitAt_add k h hh a b hqkh] at hglobal
      dsimp [s] at hglobal ⊢
      omega
    exact ⟨s, rfl, hbSum, haMem, hbMem⟩
  · rintro ⟨s, haSum, hbSum, haMem, hbMem⟩
    have hsle : s ≤ h := sum_le_length_of_smirnov_one haMem
    rw [mem_smirnovOccupancies]
    constructor
    · rw [sum_splitAtCompositionEquiv, haSum, hbSum]
      omega
    · intro t ht htk
      by_cases hth : t ≤ h
      · have hleft := (mem_smirnovOccupancies.mp haMem).2 t ht hth
        rw [occupancyPrefix_splitAt_le k h hh a b hth]
        exact hleft
      · have hle : h ≤ t := by omega
        have hqpos : 1 ≤ t - h := by omega
        have hqle : t - h ≤ k - h := by omega
        have htail := (mem_smirnovOccupancies.mp hbMem).2
          (t - h) hqpos hqle
        have hadd := occupancyPrefix_splitAt_add k h hh a b hqle
        rw [haSum] at hadd
        have hht : h + (t - h) = t := by omega
        rw [hht] at hadd
        rw [hadd]
        omega

/-- Fixed-prefix-mass form of
`splitAtCompositionEquiv_mem_smirnovOccupancies_iff_exists`. -/
theorem splitAtCompositionEquiv_mem_smirnovOccupancies_iff
    {k h s : ℕ} (hh : h ≤ k)
    (a : Fin h → ℕ) (b : Fin (k - h) → ℕ)
    (haSum : (∑ i, a i) = s) :
    splitAtCompositionEquiv k h hh (a, b) ∈
        smirnovOccupancies k 1 k ↔
      (∑ i, b i) = k - s ∧
      a ∈ smirnovOccupancies s 1 h ∧
      b ∈ smirnovOccupancies (k - s) (h + 1 - s) (k - h) := by
  rw [splitAtCompositionEquiv_mem_smirnovOccupancies_iff_exists hh a b]
  constructor
  · rintro ⟨t, hat, hb, ha, hbt⟩
    have hts : t = s := hat.symm.trans haSum
    simpa [hts] using And.intro hb (And.intro ha hbt)
  · rintro ⟨hb, ha, hbt⟩
    exact ⟨s, haSum, hb, ha, hbt⟩

/-- The fiber with marked prefix mass `s` is exactly the product of the
two residual Smirnov regions. -/
theorem fixedLowerPrefixFiber_eq_map_product
    {k h s : ℕ} (hh : h ≤ k) (hs : s ≤ h) :
    (smirnovOccupancies k 1 k).filter
        (fun c ↦ occupancyPrefix c h = s) =
      ((smirnovOccupancies s 1 h) ×ˢ
        smirnovOccupancies (k - s) (h + 1 - s) (k - h)).map
          (splitAtCompositionEquiv k h hh).toEmbedding := by
  classical
  ext c
  constructor
  · intro hc
    have hcData := Finset.mem_filter.mp hc
    let ab := (splitAtCompositionEquiv k h hh).symm c
    have hab : splitAtCompositionEquiv k h hh ab = c :=
      (splitAtCompositionEquiv k h hh).apply_symm_apply c
    have haSum : (∑ i, ab.1 i) = s := by
      rw [← occupancyPrefix_splitAt_left k h hh ab.1 ab.2,
        hab, hcData.2]
    have hsplit :=
      (splitAtCompositionEquiv_mem_smirnovOccupancies_iff
        hh ab.1 ab.2 haSum).mp (hab ▸ hcData.1)
    apply Finset.mem_map.mpr
    exact ⟨ab, Finset.mem_product.mpr ⟨hsplit.2.1, hsplit.2.2⟩, hab⟩
  · intro hc
    obtain ⟨ab, habMem, hab⟩ := Finset.mem_map.mp hc
    have habData := Finset.mem_product.mp habMem
    have haSum : (∑ i, ab.1 i) = s :=
      (mem_smirnovOccupancies.mp habData.1).1
    have hgood : splitAtCompositionEquiv k h hh ab ∈
        smirnovOccupancies k 1 k :=
      (splitAtCompositionEquiv_mem_smirnovOccupancies_iff
        hh ab.1 ab.2 haSum).mpr ⟨
          (mem_smirnovOccupancies.mp habData.2).1,
          habData.1, habData.2⟩
    apply Finset.mem_filter.mpr
    refine ⟨hab ▸ hgood, ?_⟩
    rw [← hab]
    change occupancyPrefix (splitAtCompositionEquiv k h hh ab) h = s
    rw [occupancyPrefix_splitAt_left, haSum]

/-- On the fiber with prefix mass `s`, the marked energy term is the
constant `2^s / 2^h`. -/
theorem compositionPrefixTerm_eq_of_occupancyPrefix
    {k : ℕ} (c : Fin k → ℕ) (i : Fin k)
    {s : ℕ} (hs : occupancyPrefix c (i.val + 1) = s) :
    compositionPrefixTerm c i = (2 : ℝ) ^ s / (2 : ℝ) ^ (i.val + 1) := by
  dsimp [compositionPrefixTerm]
  have hid : occupancyPrefix c (i.val + 1) =
      ∑ q ∈ Finset.Iic i, c q := by
    rw [occupancyPrefix]
    congr 1
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_Iic]
    omega
  rw [hid] at hs
  rw [hs]

/-- Exact scalar split of one marked prefix-energy summand. -/
theorem fixedLowerMarkedEnergyMass_eq_split
    {k : ℕ} (i : Fin k) :
    (∑ c ∈ smirnovOccupancies k 1 k,
        compositionPrefixTerm c i / compositionFactorial c) =
      ∑ s ∈ Finset.range (i.val + 2),
        ((2 : ℝ) ^ s / (2 : ℝ) ^ (i.val + 1)) *
          smirnovOccupancyMass s 1 (i.val + 1) *
          smirnovOccupancyMass (k - s) (i.val + 2 - s)
            (k - (i.val + 1)) := by
  classical
  let h := i.val + 1
  have hh : h ≤ k := by dsimp [h]; omega
  have hmaps : ∀ c ∈ smirnovOccupancies k 1 k,
      occupancyPrefix c h ∈ Finset.range (h + 1) := by
    intro c hc
    have hbarrier := (mem_smirnovOccupancies.mp hc).2 h (by omega) hh
    rw [Finset.mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun c ↦ compositionPrefixTerm c i / compositionFactorial c)]
  dsimp only [h]
  apply Finset.sum_congr rfl
  intro s hsRange
  have hs : s ≤ i.val + 1 := by
    rw [Finset.mem_range] at hsRange
    omega
  rw [fixedLowerPrefixFiber_eq_map_product (by omega) hs,
    Finset.sum_map, Finset.sum_product]
  calc
    (∑ a ∈ smirnovOccupancies s 1 (i.val + 1),
        ∑ b ∈ smirnovOccupancies (k - s) (i.val + 2 - s)
            (k - (i.val + 1)),
          compositionPrefixTerm
              (splitAtCompositionEquiv k (i.val + 1) (by omega) (a, b)) i /
            compositionFactorial
              (splitAtCompositionEquiv k (i.val + 1) (by omega) (a, b))) =
      ∑ a ∈ smirnovOccupancies s 1 (i.val + 1),
        ((2 : ℝ) ^ s / (2 : ℝ) ^ (i.val + 1)) *
          (1 / compositionFactorial a) *
          (∑ b ∈ smirnovOccupancies (k - s) (i.val + 2 - s)
              (k - (i.val + 1)), 1 / compositionFactorial b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      have haSum : (∑ q, a q) = s :=
        (mem_smirnovOccupancies.mp ha).1
      have hpref : occupancyPrefix
          (splitAtCompositionEquiv k (i.val + 1) (by omega) (a, b))
            (i.val + 1) = s := by
        rw [occupancyPrefix_splitAt_left, haSum]
      rw [compositionPrefixTerm_eq_of_occupancyPrefix _ i hpref,
        compositionFactorial_splitAtCompositionEquiv]
      field_simp
    _ = ((2 : ℝ) ^ s / (2 : ℝ) ^ (i.val + 1)) *
          (∑ a ∈ smirnovOccupancies s 1 (i.val + 1),
            1 / compositionFactorial a) *
          (∑ b ∈ smirnovOccupancies (k - s) (i.val + 2 - s)
              (k - (i.val + 1)), 1 / compositionFactorial b) := by
      rw [← Finset.sum_mul]
      congr 1
      rw [Finset.mul_sum]
    _ = ((2 : ℝ) ^ s / (2 : ℝ) ^ (i.val + 1)) *
          smirnovOccupancyMass s 1 (i.val + 1) *
          smirnovOccupancyMass (k - s) (i.val + 2 - s)
            (k - (i.val + 1)) := by rfl

/-- Exact finite split of the entire energy moment.  This is the scalar
double sum to which the uniform Smirnov estimate and shifted Abel
convolution are applied. -/
theorem fixedLowerPrefixEnergyMoment_eq_split (k : ℕ) :
    fixedLowerPrefixEnergyMoment k =
      ∑ i : Fin k, ∑ s ∈ Finset.range (i.val + 2),
        ((2 : ℝ) ^ s / (2 : ℝ) ^ (i.val + 1)) *
          smirnovOccupancyMass s 1 (i.val + 1) *
          smirnovOccupancyMass (k - s) (i.val + 2 - s)
            (k - (i.val + 1)) := by
  rw [fixedLowerPrefixEnergyMoment]
  calc
    (∑ c ∈ smirnovOccupancies k 1 k,
        fixedLowerPrefixEnergy c / compositionFactorial c) =
      ∑ c ∈ smirnovOccupancies k 1 k,
        ∑ i : Fin k,
          compositionPrefixTerm c i / compositionFactorial c := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [fixedLowerPrefixEnergy, compositionPenalty_eq_sum_prefixTerm,
        Finset.sum_div]
    _ = ∑ i : Fin k, ∑ c ∈ smirnovOccupancies k 1 k,
          compositionPrefixTerm c i / compositionFactorial c := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact fixedLowerMarkedEnergyMass_eq_split i

/-- The same scalar moment indexed by the deficit `d = h - s` and by the
number `p = k - s` of points left after the marked prefix.  The filter
removes the spurious zero-length prefix `(d,p) = (0,k)`. -/
noncomputable def fixedLowerDeficitEnergySum (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.range (k + 1),
    ∑ p ∈ (Finset.Icc d k).filter (fun p ↦ 1 ≤ k - p + d),
      (1 / (2 : ℝ) ^ d) *
        smirnovOccupancyMass (k - p) 1 (k - p + d) *
        smirnovOccupancyMass p (d + 1) (p - d)

/-- Reindex the exact marked-prefix split by the deficit and tail mass. -/
theorem fixedLowerPrefixEnergyMoment_eq_deficitSum (k : ℕ) :
    fixedLowerPrefixEnergyMoment k = fixedLowerDeficitEnergySum k := by
  rw [fixedLowerPrefixEnergyMoment_eq_split, fixedLowerDeficitEnergySum]
  let F : ℕ → ℝ := fun i ↦
    ∑ s ∈ Finset.range (i + 2),
      ((2 : ℝ) ^ s / (2 : ℝ) ^ (i + 1)) *
        smirnovOccupancyMass s 1 (i + 1) *
        smirnovOccupancyMass (k - s) (i + 2 - s) (k - (i + 1))
  change (∑ i : Fin k, F i.val) = _
  rw [Fin.sum_univ_eq_sum_range F k]
  dsimp only [F]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
      (fun x _hx ↦ ⟨x.1 + 1 - x.2, k - x.2⟩)
  · intro x hx
    rw [Finset.mem_sigma] at hx ⊢
    rcases hx with ⟨hi, hs⟩
    simp only [Finset.mem_range] at hi hs ⊢
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  · intro x₁ hx₁ x₂ hx₂ heq
    rw [Finset.mem_sigma] at hx₁ hx₂
    simp only [Finset.mem_range] at hx₁ hx₂
    have hs₁k : x₁.2 ≤ k := by omega
    have hs₂k : x₂.2 ≤ k := by omega
    have hpEq : k - x₁.2 = k - x₂.2 :=
      congrArg Sigma.snd heq
    have hsEq : x₁.2 = x₂.2 := by omega
    have hdEq : x₁.1 + 1 - x₁.2 = x₂.1 + 1 - x₂.2 :=
      congrArg Sigma.fst heq
    have hiEq : x₁.1 = x₂.1 := by omega
    apply Sigma.ext hiEq
    simpa [hsEq]
  · intro y hy
    rw [Finset.mem_sigma] at hy
    rcases hy with ⟨hd, hp⟩
    simp only [Finset.mem_range] at hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp
    rcases hp with ⟨⟨hdp, hpk⟩, hpos⟩
    let i := k - y.2 + y.1 - 1
    let s := k - y.2
    have hi : i < k := by dsimp [i]; omega
    have hs : s < i + 2 := by dsimp [i, s]; omega
    refine ⟨⟨i, s⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      simp only [Finset.mem_range]
      exact ⟨hi, hs⟩
    · apply Sigma.ext
      · dsimp [i, s]
        omega
      · have hkp : k - (k - y.2) = y.2 := by omega
        simpa [s, hkp]
  · intro x hx
    rw [Finset.mem_sigma] at hx
    rcases hx with ⟨hi, hs⟩
    simp only [Finset.mem_range] at hi hs
    have hsi : x.2 ≤ x.1 + 1 := by omega
    have hsk : x.2 ≤ k := by omega
    have hkp : k - (k - x.2) = x.2 := by omega
    have hpow :
        (2 : ℝ) ^ x.2 / (2 : ℝ) ^ (x.1 + 1) =
          1 / (2 : ℝ) ^ (x.1 + 1 - x.2) := by
      rw [show x.1 + 1 = x.2 + (x.1 + 1 - x.2) by omega, pow_add]
      field_simp
      rw [Nat.add_sub_cancel_left]
    rw [hpow]
    have hoff : x.1 + 1 - x.2 + 1 = x.1 + 2 - x.2 := by omega
    have htail : k - x.2 - (x.1 + 1 - x.2) = k - (x.1 + 1) := by
      omega
    dsimp only
    rw [hkp, Nat.add_sub_of_le hsi, hoff, htail]

/-! ## Endpoint evaluations used in the deficit sum -/

/-- With no points, every all-zero occupancy satisfies every positive
Smirnov barrier. -/
theorem smirnovOccupancyMass_zero_eq_one (u v : ℕ) :
    smirnovOccupancyMass 0 (u + 1) v = 1 := by
  have hset : smirnovOccupancies 0 (u + 1) v = compositionsOf v 0 := by
    ext c
    rw [mem_smirnovOccupancies, mem_compositionsOf]
    constructor
    · exact fun hc ↦ hc.1
    · intro hc
      refine ⟨hc, ?_⟩
      intro h hh hvh
      have hzero : ∀ i, c i = 0 := by
        intro i
        have hle : c i ≤ ∑ j, c j :=
          Finset.single_le_sum (fun j _hj ↦ Nat.zero_le (c j))
            (Finset.mem_univ i)
        rw [hc] at hle
        omega
      simp [occupancyPrefix, hzero]
  rw [smirnovOccupancyMass, hset,
    sum_inv_compositionFactorial_compositionsOf]
  simp

/-- Exact reciprocal-factorial mass for offset one and arbitrary terminal
slack `d+1`. -/
theorem smirnovOccupancyMass_one_general_eq
    {q d : ℕ} (hq : 1 ≤ q) :
    smirnovOccupancyMass q 1 (q + d) =
      ((d + 1 : ℕ) : ℝ) * ((q + d + 1 : ℕ) : ℝ) ^ (q - 1) /
        (q.factorial : ℝ) := by
  have hv : 0 < q + d := by omega
  have hprob := smirnovProbability_one_eq
    (k := q) (v := q + d) (w := d + 1) hq (by omega) (by omega)
  rw [smirnovOccupancyMass_eq_probability_mul hv, hprob]
  have hpow : (0 : ℝ) < ((q + d : ℕ) : ℝ) ^ q := by positivity
  field_simp
  congr 2
  norm_cast
  omega

/-- Uniform prefix estimate which also covers the zero-point endpoint. -/
theorem smirnovOccupancyMass_one_general_le
    (q d : ℕ) :
    smirnovOccupancyMass q 1 (q + d) ≤
      ((d + 1 : ℕ) : ℝ) * ((q + d + 1 : ℕ) : ℝ) ^ (q - 1) /
        (q.factorial : ℝ) := by
  by_cases hq : q = 0
  · subst q
    rw [smirnovOccupancyMass_zero_eq_one]
    simp
  · exact (smirnovOccupancyMass_one_general_eq (Nat.one_le_iff_ne_zero.mpr hq)).le

/-- A positive amount of mass cannot be placed into an empty occupancy
alphabet. -/
theorem smirnovOccupancyMass_zero_length_eq_zero
    {p u : ℕ} (hp : 0 < p) :
    smirnovOccupancyMass p u 0 = 0 := by
  rw [smirnovOccupancyMass]
  have hset : smirnovOccupancies p u 0 = ∅ := by
    by_contra hne
    obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hsum := (mem_smirnovOccupancies.mp hc).1
    have : (∑ i : Fin 0, c i) = 0 := by simp
    omega
  rw [hset]
  simp

/-! ## The uniform `w = 1` suffix bound -/

/-- For terminal slack one, the quantitative estimate can be written with
a single universal constant for every positive tail length.  The small
parameter cases follow from probability at most one. -/
theorem smirnovProbability_w_one_le
    {p d : ℕ} (hdp : d < p) :
    smirnovProbability p (d + 1) (p - d) ≤
      96 * ((d + 2 : ℕ) : ℝ) / (p : ℝ) := by
  have hp : 0 < p := by omega
  have hv : 0 < p - d := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  by_cases hpLarge : 100 ≤ p
  · by_cases huLarge : 10 * (d + 1) ≤ p
    · have h := smirnovProbability_le_twentyfour
        (k := p) (u := d + 1) (v := p - d) (w := 1)
        hpLarge huLarge (by omega) (by omega) (by omega)
      norm_num at h ⊢
      convert h using 1 <;> ring
    · have hone := smirnovProbability_le_one
        (k := p) (u := d + 1) (v := p - d) hv
      refine hone.trans ?_
      apply (le_div_iff₀ hpR).2
      norm_num
      have hnat : p ≤ 96 * (d + 2) := by omega
      exact_mod_cast hnat
  · have hone := smirnovProbability_le_one
      (k := p) (u := d + 1) (v := p - d) hv
    refine hone.trans ?_
    apply (le_div_iff₀ hpR).2
    norm_num
    have hnat : p ≤ 96 * (d + 2) := by omega
    exact_mod_cast hnat

/-- Reciprocal-factorial form of the preceding probability estimate. -/
theorem smirnovOccupancyMass_w_one_le
    {p d : ℕ} (hdp : d < p) :
    smirnovOccupancyMass p (d + 1) (p - d) ≤
      (96 * ((d + 2 : ℕ) : ℝ) / (p : ℝ)) *
        ((p - d : ℕ) : ℝ) ^ p / (p.factorial : ℝ) := by
  have hv : 0 < p - d := by omega
  rw [smirnovOccupancyMass_eq_probability_mul hv]
  have hpow : 0 ≤ ((p - d : ℕ) : ℝ) ^ p := by positivity
  have hfac : (0 : ℝ) < p.factorial := by positivity
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (smirnovProbability_w_one_le hdp) hpow)
    hfac.le

/-! ## The geometric coefficient in the deficit sum -/

/-- Exact finite form of
`sum_{d ≥ 0} (d+1)(d+2)/2^d = 16`. -/
theorem sum_weighted_deficit_div_two_pow_eq (n : ℕ) :
    (∑ d ∈ Finset.range n,
        (((d + 1 : ℕ) : ℝ) * (d + 2 : ℕ)) / (2 : ℝ) ^ d) =
      16 -
        (2 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 16) / (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring

/-- Every finite partial sum of the deficit coefficients is at most `16`.
-/
theorem sum_weighted_deficit_div_two_pow_le (n : ℕ) :
    (∑ d ∈ Finset.range n,
        (((d + 1 : ℕ) : ℝ) * (d + 2 : ℕ)) / (2 : ℝ) ^ d) ≤ 16 := by
  rw [sum_weighted_deficit_div_two_pow_eq]
  have hnonneg : 0 ≤
      (2 * (n : ℝ) ^ 2 + 10 * (n : ℝ) + 16) / (2 : ℝ) ^ n := by
    positivity
  linarith

/-! ## Shifted Abel bound for the strict interior -/

/-- The strict interior contribution at one fixed positive deficit. -/
noncomputable def fixedEnergyDeficitInterior (k d : ℕ) : ℝ :=
  ∑ p ∈ Finset.Ico (d + 1) k,
    (1 / (2 : ℝ) ^ d) *
      smirnovOccupancyMass (k - p) 1 (k - p + d) *
      smirnovOccupancyMass p (d + 1) (p - d)

theorem pow_div_index_le_pred_pow {p d : ℕ}
    (hp : 1 ≤ p) (hdp : d ≤ p) :
    (((p - d : ℕ) : ℝ) ^ p) / (p : ℝ) ≤
      ((p - d : ℕ) : ℝ) ^ (p - 1) := by
  have hpR : (0 : ℝ) < p := by positivity
  have hratio : (((p - d : ℕ) : ℝ) / (p : ℝ)) ≤ 1 := by
    apply (div_le_one hpR).2
    exact_mod_cast Nat.sub_le p d
  have hnonneg : 0 ≤ ((p - d : ℕ) : ℝ) ^ (p - 1) := by positivity
  have hpow : ((p - d : ℕ) : ℝ) ^ p =
      ((p - d : ℕ) : ℝ) ^ (p - 1) * ((p - d : ℕ) : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    (((p - d : ℕ) : ℝ) ^ p) / (p : ℝ) =
        ((p - d : ℕ) : ℝ) ^ (p - 1) *
          (((p - d : ℕ) : ℝ) / (p : ℝ)) := by
      rw [hpow]
      ring
    _ ≤ ((p - d : ℕ) : ℝ) ^ (p - 1) * 1 :=
      mul_le_mul_of_nonneg_left hratio hnonneg
    _ = _ := by ring

theorem inv_factorial_mul_inv_factorial_eq_choose_div
    {k p : ℕ} (hpk : p ≤ k) :
    (1 / (((k - p).factorial : ℕ) : ℝ)) *
        (1 / (p.factorial : ℝ)) =
      (k.choose p : ℝ) / (k.factorial : ℝ) := by
  have hkpFac : (((k - p).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have hpFac : (p.factorial : ℝ) ≠ 0 := by positivity
  have hkFac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hpk
  have hchoose :
      (k.choose p : ℝ) * (p.factorial : ℝ) *
          (((k - p).factorial : ℕ) : ℝ) =
        (k.factorial : ℝ) := by exact_mod_cast hchooseNat
  field_simp
  nlinarith

theorem fixedEnergyDeficitInterior_le_abel
    {k d : ℕ} (hd : 1 ≤ d) (hdk : d < k)
    (hsuffix : ∀ p ∈ Finset.Ico (d + 1) k,
      smirnovOccupancyMass p (d + 1) (p - d) ≤
        96 * ((d + 2 : ℕ) : ℝ) / (p : ℝ) *
          ((p - d : ℕ) : ℝ) ^ p / (p.factorial : ℝ)) :
    fixedEnergyDeficitInterior k d ≤
      (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d / (k.factorial : ℝ)) *
        fordAbelIntegerNegativePositiveSum k d (d + 1 : ℕ) := by
  rw [fixedEnergyDeficitInterior, fordAbelIntegerNegativePositiveSum]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hpMem
  have hpData := Finset.mem_Ico.mp hpMem
  have hpk : p ≤ k := hpData.2.le
  have hkp : 1 ≤ k - p := by omega
  have hp : 1 ≤ p := by omega
  have hdp : d ≤ p := by omega
  have hprefix := smirnovOccupancyMass_one_general_eq
    (q := k - p) (d := d) hkp
  have hsuf := hsuffix p hpMem
  have hprefixNonneg :
      0 ≤ (1 / (2 : ℝ) ^ d) *
        smirnovOccupancyMass (k - p) 1 (k - p + d) := by
    exact mul_nonneg (by positivity)
      (smirnovOccupancyMass_nonneg (k - p) 1 (k - p + d))
  have hratio := pow_div_index_le_pred_pow hp hdp
  have hfac := inv_factorial_mul_inv_factorial_eq_choose_div hpk
  calc
    (1 / (2 : ℝ) ^ d) *
          smirnovOccupancyMass (k - p) 1 (k - p + d) *
          smirnovOccupancyMass p (d + 1) (p - d) ≤
        ((1 / (2 : ℝ) ^ d) *
          smirnovOccupancyMass (k - p) 1 (k - p + d)) *
          (96 * ((d + 2 : ℕ) : ℝ) / (p : ℝ) *
            ((p - d : ℕ) : ℝ) ^ p / (p.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hsuf hprefixNonneg
    _ = (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) *
          (((k - p + d + 1 : ℕ) : ℝ) ^ (k - p - 1)) *
          ((((p - d : ℕ) : ℝ) ^ p) / (p : ℝ)) *
          ((1 / (((k - p).factorial : ℕ) : ℝ)) *
            (1 / (p.factorial : ℝ))) := by
      rw [hprefix]
      ring
    _ = (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) *
          (((k - p + d + 1 : ℕ) : ℝ) ^ (k - p - 1)) *
          ((((p - d : ℕ) : ℝ) ^ p) / (p : ℝ)) *
          ((k.choose p : ℝ) / (k.factorial : ℝ)) := by rw [hfac]
    _ ≤ (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) *
          (((k - p + d + 1 : ℕ) : ℝ) ^ (k - p - 1)) *
          (((p - d : ℕ) : ℝ) ^ (p - 1)) *
          ((k.choose p : ℝ) / (k.factorial : ℝ)) := by
      gcongr
    _ = (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d / (k.factorial : ℝ)) *
        ((k.choose p : ℝ) *
          ((p : ℝ) - (d : ℝ)) ^ (p - 1) *
          (((d + 1 : ℕ) : ℝ) + ((k - p : ℕ) : ℝ)) ^
            (k - p - 1)) := by
      rw [Nat.cast_sub hdp]
      push_cast
      ring

theorem fixedEnergyDeficitInterior_le
    {k d : ℕ} (hd : 1 ≤ d) (hdk : d < k)
    (hsuffix : ∀ p ∈ Finset.Ico (d + 1) k,
      smirnovOccupancyMass p (d + 1) (p - d) ≤
        96 * ((d + 2 : ℕ) : ℝ) / (p : ℝ) *
          ((p - d : ℕ) : ℝ) ^ p / (p.factorial : ℝ)) :
    fixedEnergyDeficitInterior k d ≤
      96 * Real.exp 4 *
        ((((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d) *
        (((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
  calc
    fixedEnergyDeficitInterior k d ≤
        (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d / (k.factorial : ℝ)) *
          fordAbelIntegerNegativePositiveSum k d (d + 1 : ℕ) :=
      fixedEnergyDeficitInterior_le_abel hd hdk hsuffix
    _ ≤ (96 * (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d / (k.factorial : ℝ)) *
          (Real.exp 4 * (((k + 1 : ℕ) : ℝ) ^ (k - 1))) := by
      apply mul_le_mul_of_nonneg_left
      · have habel := fordAbelIntegerNegativePositiveSum_le
          (t := k) (d := d) (B := ((d + 1 : ℕ) : ℝ)) hd hdk
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le d))
        have hbase :
            (k : ℝ) - (d : ℝ) + ((d + 1 : ℕ) : ℝ) =
              ((k + 1 : ℕ) : ℝ) := by
          push_cast
          ring
        rw [hbase] at habel
        exact habel
      · positivity
    _ = 96 * Real.exp 4 *
        ((((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d) *
        (((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by ring

theorem succ_pow_pred_div_factorial_le_three_scale
    {k : ℕ} (hk : 1 ≤ k) :
    (((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)) ≤
      3 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hfac : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have hbase :
      ((k : ℝ) + 1) = (k : ℝ) * (1 + (k : ℝ)⁻¹) := by
    field_simp
  have hpow : (((k + 1 : ℕ) : ℝ) ^ k) ≤ 3 * (k : ℝ) ^ k := by
    calc
      (((k + 1 : ℕ) : ℝ) ^ k) =
          (k : ℝ) ^ k * (1 + (k : ℝ)⁻¹) ^ k := by
        push_cast
        rw [hbase, mul_pow]
      _ ≤ (k : ℝ) ^ k * Real.exp 1 :=
        mul_le_mul_of_nonneg_left Real.one_add_inv_pow_le_exp (by positivity)
      _ ≤ (k : ℝ) ^ k * 3 :=
        mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (by positivity)
      _ = 3 * (k : ℝ) ^ k := by ring
  have hleft :
      (((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)) =
        (((k + 1 : ℕ) : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
    have hexp : (((k : ℝ) + 1) ^ k) =
        (((k : ℝ) + 1) ^ (k - 1)) * ((k : ℝ) + 1) := by
      rw [← pow_succ]
      congr 1
      omega
    rw [Nat.factorial_succ]
    push_cast
    rw [hexp]
    field_simp
  rw [hleft]
  have hdiv := div_le_div_of_nonneg_right hpow hfac.le
  calc
    (((k + 1 : ℕ) : ℝ) ^ k / ((k + 1).factorial : ℝ)) ≤
        (3 * (k : ℝ) ^ k) / ((k + 1).factorial : ℝ) := hdiv
    _ = 3 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by ring

noncomputable def fixedEnergyPositiveDeficitInteriorSum (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 k, fixedEnergyDeficitInterior k d

theorem fixedEnergyPositiveDeficitInteriorSum_le
    {k : ℕ} (hk : 2 ≤ k)
    (hsuffix : ∀ d ∈ Finset.Ico 1 k, ∀ p ∈ Finset.Ico (d + 1) k,
      smirnovOccupancyMass p (d + 1) (p - d) ≤
        96 * ((d + 2 : ℕ) : ℝ) / (p : ℝ) *
          ((p - d : ℕ) : ℝ) ^ p / (p.factorial : ℝ)) :
    fixedEnergyPositiveDeficitInteriorSum k ≤
      4608 * Real.exp 4 * (k : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
  let B : ℝ := ((k + 1 : ℕ) : ℝ) ^ (k - 1) / (k.factorial : ℝ)
  let S : ℝ := (k : ℝ) ^ k / ((k + 1).factorial : ℝ)
  have hB : B ≤ 3 * S := by
    exact succ_pow_pred_div_factorial_le_three_scale (by omega)
  have hweight :
      (∑ d ∈ Finset.Ico 1 k,
        (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d) ≤ 16 := by
    calc
      (∑ d ∈ Finset.Ico 1 k,
          (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) ≤
          ∑ d ∈ Finset.range k,
            (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
              (2 : ℝ) ^ d := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hdMem
          rw [Finset.mem_range]
          exact (Finset.mem_Ico.mp hdMem).2
        · intro d _hd _hnot
          positivity
      _ ≤ 16 := sum_weighted_deficit_div_two_pow_le k
  calc
    fixedEnergyPositiveDeficitInteriorSum k ≤
        ∑ d ∈ Finset.Ico 1 k,
          96 * Real.exp 4 *
            ((((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
              (2 : ℝ) ^ d) * B := by
      rw [fixedEnergyPositiveDeficitInteriorSum]
      apply Finset.sum_le_sum
      intro d hdMem
      have hdData := Finset.mem_Ico.mp hdMem
      exact fixedEnergyDeficitInterior_le hdData.1 hdData.2
        (hsuffix d hdMem)
    _ = (96 * Real.exp 4 * B) *
        (∑ d ∈ Finset.Ico 1 k,
          (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hdMem
      ring
    _ ≤ (96 * Real.exp 4 * B) * 16 :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ ≤ (96 * Real.exp 4 * (3 * S)) * 16 := by
      gcongr
    _ = 4608 * Real.exp 4 * S := by ring
    _ = 4608 * Real.exp 4 * (k : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
      dsimp [S]
      ring

/-! ## The zero-prefix boundary -/

/-- Boundary terms with zero points in the marked prefix (`p = k`). -/
noncomputable def fixedEnergyZeroPrefixEdge (k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Ico 1 k,
    (1 / (2 : ℝ) ^ d) * smirnovOccupancyMass 0 1 d *
      smirnovOccupancyMass k (d + 1) (k - d)

theorem fixedEnergyZeroPrefixEdge_le
    {k : ℕ} (hk : 1 ≤ k) :
    fixedEnergyZeroPrefixEdge k ≤
      1536 * ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
  have hpoint : ∀ d ∈ Finset.Ico 1 k,
      (1 / (2 : ℝ) ^ d) * smirnovOccupancyMass 0 1 d *
          smirnovOccupancyMass k (d + 1) (k - d) ≤
        96 * ((((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d) *
          ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
    intro d hdMem
    have hd := Finset.mem_Ico.mp hdMem
    have htail := smirnovOccupancyMass_w_one_le (p := k) (d := d) hd.2
    have hratio := pow_div_index_le_pred_pow (p := k) (d := d) hk hd.2.le
    have hpow : (((k - d : ℕ) : ℝ) ^ (k - 1)) ≤
        (k : ℝ) ^ (k - 1) := by
      gcongr
      exact_mod_cast Nat.sub_le k d
    rw [show smirnovOccupancyMass 0 1 d = 1 by
      simpa using smirnovOccupancyMass_zero_eq_one 0 d]
    have hleftNonneg : 0 ≤ (1 / (2 : ℝ) ^ d) := by positivity
    calc
      (1 / (2 : ℝ) ^ d) * 1 *
          smirnovOccupancyMass k (d + 1) (k - d) ≤
        (1 / (2 : ℝ) ^ d) *
          ((96 * ((d + 2 : ℕ) : ℝ) / (k : ℝ)) *
            ((k - d : ℕ) : ℝ) ^ k / (k.factorial : ℝ)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left htail hleftNonneg
      _ = (96 * ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d) *
          ((((k - d : ℕ) : ℝ) ^ k / (k : ℝ)) /
            (k.factorial : ℝ)) := by ring
      _ ≤ (96 * ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d) *
          (((k - d : ℕ) : ℝ) ^ (k - 1) /
            (k.factorial : ℝ)) := by
        gcongr
      _ ≤ (96 * ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d) *
          ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
        gcongr
      _ ≤ 96 * ((((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
          (2 : ℝ) ^ d) *
          ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
        have hdOne : (1 : ℝ) ≤ (d + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le d)
        have hnonneg : 0 ≤ ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d := by
          positivity
        have hins : ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d ≤
            ((d + 1 : ℕ) : ℝ) *
              (((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d) :=
          (le_mul_of_one_le_left hnonneg hdOne)
        calc
          (96 * ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d) *
              ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) ≤
            (96 * (((d + 1 : ℕ) : ℝ) *
              (((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d))) *
              ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
                have hcoeff :
                    96 * ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d ≤
                      96 * (((d + 1 : ℕ) : ℝ) *
                        (((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d)) := by
                  calc
                    96 * ((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d =
                        96 * (((d + 2 : ℕ) : ℝ) / (2 : ℝ) ^ d) := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_left hins (by norm_num)
                exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
          _ = _ := by ring
  calc
    fixedEnergyZeroPrefixEdge k ≤
        ∑ d ∈ Finset.Ico 1 k,
          96 * ((((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) *
            ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by
      rw [fixedEnergyZeroPrefixEdge]
      exact Finset.sum_le_sum hpoint
    _ = (96 * ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ))) *
        (∑ d ∈ Finset.Ico 1 k,
          (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
            (2 : ℝ) ^ d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ (96 * ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ))) * 16 := by
      apply mul_le_mul_of_nonneg_left
      · calc
          (∑ d ∈ Finset.Ico 1 k,
              (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
                (2 : ℝ) ^ d) ≤
              ∑ d ∈ Finset.range k,
                (((d + 1 : ℕ) : ℝ) * ((d + 2 : ℕ) : ℝ)) /
                  (2 : ℝ) ^ d := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro d hd
              exact Finset.mem_range.mpr (Finset.mem_Ico.mp hd).2
            · intro d hd hnot
              positivity
          _ ≤ 16 := sum_weighted_deficit_div_two_pow_le k
      · positivity
    _ = 1536 * ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) := by ring

theorem pred_pow_div_factorial_le_two_scale
    {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) ^ (k - 1) / (k.factorial : ℝ) ≤
      2 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hkR : (0 : ℝ) < k := by positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hfacSucc : (0 : ℝ) < (k + 1).factorial := by positivity
  have hpow : (k : ℝ) ^ k = (k : ℝ) ^ (k - 1) * k := by
    rw [← pow_succ]
    congr 1
    omega
  have hratio : (1 : ℝ) ≤ 2 * (k : ℝ) / ((k : ℝ) + 1) := by
    apply (le_div_iff₀ (by positivity)).2
    norm_num
    exact_mod_cast (show k + 1 ≤ 2 * k by omega)
  calc
    (k : ℝ) ^ (k - 1) / (k.factorial : ℝ) ≤
        (2 * (k : ℝ) / ((k : ℝ) + 1)) *
          ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) :=
      le_mul_of_one_le_left (by positivity) hratio
    _ = 2 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
      rw [Nat.factorial_succ, hpow]
      push_cast
      field_simp

/-- Unconditional positive-deficit interior estimate. -/
theorem fixedEnergyPositiveDeficitInteriorSum_le_scale
    {k : ℕ} (hk : 2 ≤ k) :
    fixedEnergyPositiveDeficitInteriorSum k ≤
      4608 * Real.exp 4 *
        ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have h := fixedEnergyPositiveDeficitInteriorSum_le hk
    (fun d hd p hp ↦ smirnovOccupancyMass_w_one_le (by
      have hdData := Finset.mem_Ico.mp hd
      have hpData := Finset.mem_Ico.mp hp
      omega))
  simpa [mul_div_assoc] using h

/-- The zero-prefix edge costs at most `3072` natural scales. -/
theorem fixedEnergyZeroPrefixEdge_le_scale
    {k : ℕ} (hk : 1 ≤ k) :
    fixedEnergyZeroPrefixEdge k ≤
      3072 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  calc
    fixedEnergyZeroPrefixEdge k ≤
        1536 * ((k : ℝ) ^ (k - 1) / (k.factorial : ℝ)) :=
      fixedEnergyZeroPrefixEdge_le hk
    _ ≤ 1536 *
        (2 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (pred_pow_div_factorial_le_two_scale hk) (by norm_num)
    _ = 3072 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by ring

/-- The surviving `(d,p)=(0,0)` endpoint costs at most three natural
scales. -/
theorem fixedEnergyEndpoint_le_scale
    {k : ℕ} (hk : 1 ≤ k) :
    smirnovOccupancyMass k 1 k ≤
      3 * ((k : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  rw [smirnovOccupancyMass_one_eq hk]
  exact succ_pow_pred_div_factorial_le_three_scale hk

end Erdos446
