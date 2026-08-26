/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import Util.Density

/-!
# Positive lower density is strictly weaker than `Set.HasPosDensity`

This file gives an explicit, fully checked witness for the specification
audit in Erdős Problem 822.  Its set contains every even natural and all
integers in each interval `[4^k, 2 * 4^k)`.  The lower density is positive,
but endpoint identities on successive multiplicative blocks force any
hypothetical natural-density limit to equal both `1` and `1 / 2`.
-/

namespace Erdos822

section StrictnessWitness

open Filter

lemma even_filter_range_card (N : ℕ) :
    ((Finset.range N).filter fun n : ℕ => Even n).card = (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hN : Even N
      · rw [if_pos hN, Finset.card_insert_of_notMem]
        · rw [ih]
          obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp hN
          omega
        · simp
      · rw [if_neg hN, ih]
        obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hN
        omega

lemma even_prefix_card (N : ℕ) :
    (({n : ℕ | Even n} ∩ Set.Iio N).ncard) = (N + 1) / 2 := by
  have hset : ({n : ℕ | Even n} ∩ Set.Iio N) =
      ↑((Finset.range N).filter fun n : ℕ => Even n) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio,
      Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    tauto
  calc
    (({n : ℕ | Even n} ∩ Set.Iio N).ncard) =
        (↑((Finset.range N).filter fun n : ℕ => Even n) : Set ℕ).ncard :=
      congrArg Set.ncard hset
    _ = ((Finset.range N).filter fun n : ℕ => Even n).card :=
      Set.ncard_coe_finset _
    _ = (N + 1) / 2 := even_filter_range_card N

private theorem hasDensity_of_counting_error
    (S : Set ℕ) (c C : ℝ)
    (h : ∀ n, |((S ∩ Set.Iio n).ncard : ℝ) - c * n| ≤ C) :
    S.HasDensity c := by
  rw [Set.HasDensity]
  have hzero : Tendsto
      (fun n : ℕ => (((S ∩ Set.Iio n).ncard : ℝ) - c * n) / n)
      atTop (nhds 0) := by
    exact squeeze_zero_norm
      (fun n => by
        simpa [abs_div] using
          div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg n))
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop)
  simpa only [zero_add] using (hzero.add_const c).congr' (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
    have hIio : (Set.Iio n).ncard = n := by simp
    rw [hIio]
    field_simp
    ring)

lemma even_hasDensity_half :
    ({n : ℕ | Even n} : Set ℕ).HasDensity (1 / 2 : ℝ) := by
  apply hasDensity_of_counting_error _ _ 1
  intro N
  rw [even_prefix_card]
  by_cases hN : Even N
  · obtain ⟨k, rfl⟩ := even_iff_two_dvd.mp hN
    have hdiv : (2 * k + 1) / 2 = k := by omega
    rw [hdiv]
    push_cast
    have hz : (k : ℝ) - 1 / 2 * (2 * (k : ℝ)) = 0 := by ring
    rw [hz, abs_zero]
    norm_num
  · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hN
    have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [hdiv]
    push_cast
    rw [abs_le]
    constructor <;> norm_num <;> linarith

def oscillatingSet : Set ℕ :=
  {n | Even n ∨ ∃ k : ℕ, 4 ^ k ≤ n ∧ n < 2 * 4 ^ k}

lemma oscillatingSet_mem_onBlock (k n : ℕ)
    (hlo : 4 ^ k ≤ n) (hhi : n < 2 * 4 ^ k) :
    n ∈ oscillatingSet := by
  exact Or.inr ⟨k, hlo, hhi⟩

lemma oscillatingSet_mem_offBlock_iff (k n : ℕ)
    (hlo : 2 * 4 ^ k ≤ n) (hhi : n < 4 ^ (k + 1)) :
    n ∈ oscillatingSet ↔ Even n := by
  constructor
  · rintro (heven | ⟨j, hjlo, hjhi⟩)
    · exact heven
    · rcases le_or_gt j k with hjk | hkj
      · have hp : 4 ^ j ≤ 4 ^ k :=
          pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 4) hjk
        have : 2 * 4 ^ j ≤ n :=
          (Nat.mul_le_mul_left 2 hp).trans hlo
        omega
      · have hsucc : k + 1 ≤ j := by omega
        have hp : 4 ^ (k + 1) ≤ 4 ^ j :=
          pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 4) hsucc
        omega
  · exact fun heven => Or.inl heven

noncomputable def prefixCard (S : Set ℕ) (N : ℕ) : ℕ :=
  (S ∩ Set.Iio N).ncard

lemma prefixCard_add_interval (S : Set ℕ) {a b : ℕ} (hab : a ≤ b) :
    prefixCard S b = prefixCard S a + (S ∩ Set.Ico a b).ncard := by
  have hdisj : Disjoint (S ∩ Set.Iio a) (S ∩ Set.Ico a b) := by
    rw [Set.disjoint_left]
    intro n hn1 hn2
    exact (not_lt_of_ge hn2.2.1) hn1.2
  rw [prefixCard, prefixCard, ← Set.ncard_union_eq hdisj]
  congr 1
  ext n
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ico]
  constructor
  · rintro ⟨hnS, hnb⟩
    by_cases hna : n < a
    · exact Or.inl ⟨hnS, hna⟩
    · exact Or.inr ⟨hnS, by omega, hnb⟩
  · rintro (⟨hnS, hna⟩ | ⟨hnS, hna, hnb⟩)
    · exact ⟨hnS, hna.trans_le hab⟩
    · exact ⟨hnS, hnb⟩

lemma prefixCard_onBlock (k : ℕ) :
    prefixCard oscillatingSet (2 * 4 ^ k) =
      prefixCard oscillatingSet (4 ^ k) + 4 ^ k := by
  rw [prefixCard_add_interval oscillatingSet (by
    exact Nat.mul_le_mul_right (4 ^ k) (by norm_num : 1 ≤ 2))]
  simp only [one_mul]
  have hset : oscillatingSet ∩ Set.Ico (4 ^ k) (2 * 4 ^ k) =
      Set.Ico (4 ^ k) (2 * 4 ^ k) := by
    apply Set.inter_eq_right.mpr
    intro n hn
    exact oscillatingSet_mem_onBlock k n hn.1 hn.2
  rw [hset]
  simp
  omega

lemma prefixCard_offBlock_relation (k : ℕ) :
    prefixCard oscillatingSet (4 * 4 ^ k) +
        prefixCard {n : ℕ | Even n} (2 * 4 ^ k) =
      prefixCard oscillatingSet (2 * 4 ^ k) +
        prefixCard {n : ℕ | Even n} (4 * 4 ^ k) := by
  have hpow : 4 ^ (k + 1) = 4 * 4 ^ k := by ring
  have hset : oscillatingSet ∩ Set.Ico (2 * 4 ^ k) (4 * 4 ^ k) =
      {n : ℕ | Even n} ∩ Set.Ico (2 * 4 ^ k) (4 * 4 ^ k) := by
    ext n
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hnS, hlo, hhi⟩
      exact ⟨(oscillatingSet_mem_offBlock_iff k n hlo (hpow ▸ hhi)).mp hnS,
        hlo, hhi⟩
    · rintro ⟨heven, hlo, hhi⟩
      exact ⟨(oscillatingSet_mem_offBlock_iff k n hlo (hpow ▸ hhi)).mpr heven,
        hlo, hhi⟩
  have hS := prefixCard_add_interval oscillatingSet
    (a := 2 * 4 ^ k) (b := 4 * 4 ^ k) (by omega)
  have hE := prefixCard_add_interval {n : ℕ | Even n}
    (a := 2 * 4 ^ k) (b := 4 * 4 ^ k) (by omega)
  rw [hset] at hS
  omega

lemma partialDensity_mono_of_subset {S T : Set ℕ} (hST : S ⊆ T) (N : ℕ) :
    S.partialDensity Set.univ N ≤ T.partialDensity Set.univ N := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Set.ncard_le_ncard
    (Set.inter_subset_inter_left (Set.Iio N) hST)
    ((Set.finite_Iio N).subset Set.inter_subset_right)

lemma oscillatingSet_lowerDensity_pos :
    0 < oscillatingSet.lowerDensity := by
  have hEvenSubset : ({n : ℕ | Even n} : Set ℕ) ⊆ oscillatingSet := by
    intro n hn
    exact Or.inl hn
  have hEvenTendsto := even_hasDensity_half
  rw [Set.HasDensity] at hEvenTendsto
  have hEvenEventually :
      ∀ᶠ N : ℕ in atTop,
        (1 / 4 : ℝ) ≤ ({n : ℕ | Even n} : Set ℕ).partialDensity Set.univ N := by
    filter_upwards [hEvenTendsto.eventually
      (Ioi_mem_nhds (by norm_num : (1 / 4 : ℝ) < 1 / 2))] with N hN
    exact hN.le
  have hOscEventually :
      ∀ᶠ N : ℕ in atTop,
        (1 / 4 : ℝ) ≤ oscillatingSet.partialDensity Set.univ N := by
    filter_upwards [hEvenEventually] with N hN
    exact hN.trans (partialDensity_mono_of_subset hEvenSubset N)
  have hle : (1 / 4 : ℝ) ≤ oscillatingSet.lowerDensity := by
    exact le_liminf_of_le
      (isCoboundedUnder_ge_of_le atTop fun N ↦
        Set.partialDensity_le_one oscillatingSet Set.univ N)
      hOscEventually
  linarith

lemma nat_le_four_pow (k : ℕ) : k ≤ 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ]
      have hp : 0 < 4 ^ k := pow_pos (by norm_num) _
      omega

lemma fourPow_tendsto_atTop : Tendsto (fun k : ℕ => 4 ^ k) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  exact ⟨b, fun k hk => hk.trans (nat_le_four_pow k)⟩

lemma two_mul_fourPow_tendsto_atTop :
    Tendsto (fun k : ℕ => 2 * 4 ^ k) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.1 fourPow_tendsto_atTop) b
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  omega

lemma four_mul_fourPow_tendsto_atTop :
    Tendsto (fun k : ℕ => 4 * 4 ^ k) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨K, hK⟩ := (Filter.tendsto_atTop_atTop.1 fourPow_tendsto_atTop) b
  refine ⟨K, fun k hk => (hK k hk).trans ?_⟩
  omega

lemma cast_prefixCard_eq_mul_partialDensity (S : Set ℕ) {N : ℕ} (hN : 0 < N) :
    (prefixCard S N : ℝ) =
      (N : ℝ) * S.partialDensity Set.univ N := by
  simp only [prefixCard, Set.partialDensity, Set.inter_univ, Set.univ_inter,
    Set.ncard_Iio_nat]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

lemma onBlock_partialDensity_eq (k : ℕ) :
    2 * oscillatingSet.partialDensity Set.univ (2 * 4 ^ k) -
        oscillatingSet.partialDensity Set.univ (4 ^ k) = 1 := by
  have hq : 0 < 4 ^ k := pow_pos (by norm_num) _
  have hR :
      (prefixCard oscillatingSet (2 * 4 ^ k) : ℝ) =
        prefixCard oscillatingSet (4 ^ k) + 4 ^ k := by
    exact_mod_cast prefixCard_onBlock k
  rw [cast_prefixCard_eq_mul_partialDensity oscillatingSet
      (Nat.mul_pos (by norm_num) hq),
    cast_prefixCard_eq_mul_partialDensity oscillatingSet hq] at hR
  push_cast at hR
  have hqR : (0 : ℝ) < 4 ^ k := by exact_mod_cast hq
  nlinarith

lemma offBlock_partialDensity_relation (k : ℕ) :
    4 * oscillatingSet.partialDensity Set.univ (4 * 4 ^ k) -
        2 * oscillatingSet.partialDensity Set.univ (2 * 4 ^ k) =
      4 * ({n : ℕ | Even n} : Set ℕ).partialDensity Set.univ (4 * 4 ^ k) -
        2 * ({n : ℕ | Even n} : Set ℕ).partialDensity Set.univ (2 * 4 ^ k) := by
  have hq : 0 < 4 ^ k := pow_pos (by norm_num) _
  have hR :
      (prefixCard oscillatingSet (4 * 4 ^ k) : ℝ) +
          prefixCard {n : ℕ | Even n} (2 * 4 ^ k) =
        prefixCard oscillatingSet (2 * 4 ^ k) +
          prefixCard {n : ℕ | Even n} (4 * 4 ^ k) := by
    exact_mod_cast prefixCard_offBlock_relation k
  rw [cast_prefixCard_eq_mul_partialDensity oscillatingSet
      (Nat.mul_pos (by norm_num) hq),
    cast_prefixCard_eq_mul_partialDensity ({n : ℕ | Even n} : Set ℕ)
      (Nat.mul_pos (by norm_num) hq),
    cast_prefixCard_eq_mul_partialDensity oscillatingSet
      (Nat.mul_pos (by norm_num) hq),
    cast_prefixCard_eq_mul_partialDensity ({n : ℕ | Even n} : Set ℕ)
      (Nat.mul_pos (by norm_num) hq)] at hR
  push_cast at hR
  have hqR : (0 : ℝ) < 4 ^ k := by exact_mod_cast hq
  nlinarith

lemma oscillatingSet_density_eq_one {d : ℝ}
    (h : oscillatingSet.HasDensity d) : d = 1 := by
  rw [Set.HasDensity] at h
  have hPow := h.comp fourPow_tendsto_atTop
  have hTwoPow := h.comp two_mul_fourPow_tendsto_atTop
  have hlim : Tendsto
      (fun k : ℕ =>
        2 * oscillatingSet.partialDensity Set.univ (2 * 4 ^ k) -
          oscillatingSet.partialDensity Set.univ (4 ^ k))
      atTop (nhds (2 * d - d)) :=
    (tendsto_const_nhds.mul hTwoPow).sub hPow
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (2 * d - d)) :=
    hlim.congr' (Filter.Eventually.of_forall onBlock_partialDensity_eq)
  have hvalue : 2 * d - d = 1 :=
    tendsto_nhds_unique hconst tendsto_const_nhds
  linarith

lemma oscillatingSet_density_eq_half {d : ℝ}
    (h : oscillatingSet.HasDensity d) : d = 1 / 2 := by
  rw [Set.HasDensity] at h
  have hEven := even_hasDensity_half
  rw [Set.HasDensity] at hEven
  have hOscTwo := h.comp two_mul_fourPow_tendsto_atTop
  have hOscFour := h.comp four_mul_fourPow_tendsto_atTop
  have hEvenTwo := hEven.comp two_mul_fourPow_tendsto_atTop
  have hEvenFour := hEven.comp four_mul_fourPow_tendsto_atTop
  let lhs : ℕ → ℝ := fun k =>
    4 * oscillatingSet.partialDensity Set.univ (4 * 4 ^ k) -
      2 * oscillatingSet.partialDensity Set.univ (2 * 4 ^ k)
  let rhs : ℕ → ℝ := fun k =>
    4 * ({n : ℕ | Even n} : Set ℕ).partialDensity Set.univ (4 * 4 ^ k) -
      2 * ({n : ℕ | Even n} : Set ℕ).partialDensity Set.univ (2 * 4 ^ k)
  have hlimL : Tendsto lhs atTop (nhds (4 * d - 2 * d)) := by
    dsimp [lhs]
    exact (tendsto_const_nhds.mul hOscFour).sub
      (tendsto_const_nhds.mul hOscTwo)
  have hlimR : Tendsto rhs atTop (nhds (4 * (1 / 2 : ℝ) - 2 * (1 / 2 : ℝ))) := by
    dsimp [rhs]
    exact (tendsto_const_nhds.mul hEvenFour).sub
      (tendsto_const_nhds.mul hEvenTwo)
  have hlimR' : Tendsto rhs atTop (nhds (4 * d - 2 * d)) :=
    hlimL.congr' (Filter.Eventually.of_forall offBlock_partialDensity_relation)
  have hvalue : 4 * d - 2 * d = 4 * (1 / 2 : ℝ) - 2 * (1 / 2 : ℝ) :=
    tendsto_nhds_unique hlimR' hlimR
  linarith

theorem oscillatingSet_not_hasDensity (d : ℝ) :
    ¬ oscillatingSet.HasDensity d := by
  intro h
  have h1 := oscillatingSet_density_eq_one h
  have h2 := oscillatingSet_density_eq_half h
  linarith

theorem oscillatingSet_not_hasPosDensity :
    ¬ oscillatingSet.HasPosDensity := by
  rintro ⟨d, _, hd⟩
  exact oscillatingSet_not_hasDensity d hd

theorem positive_lowerDensity_not_imply_hasPosDensity :
    ∃ S : Set ℕ, 0 < S.lowerDensity ∧ ¬ S.HasPosDensity := by
  exact ⟨oscillatingSet, oscillatingSet_lowerDensity_pos,
    oscillatingSet_not_hasPosDensity⟩

end StrictnessWitness

end Erdos822
