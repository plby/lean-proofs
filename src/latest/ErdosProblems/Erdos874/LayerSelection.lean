/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos874.Foundations

/-!
# Erdős 874: selection of a small restricted-sum layer

This file isolates the finite counting step used in the first
Deshouillers--Freiman paper.  Pairwise-disjoint layers which all live in one
finite ambient set have total cardinality at most the cardinality of that
ambient set.  A weighted pigeonhole argument then selects a layer whose
cardinality is small compared with a prescribed weight.

The last two results specialize this to the restricted-sum layers of an
admissible `A ⊆ {1, ..., N}`.  No asymptotic notation or unrecorded threshold
is hidden here: the exact finite capacity inequality needed by a later
application is an explicit hypothesis.
-/

open scoped BigOperators

namespace Erdos874

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## The finite disjoint-layer counting engine -/

/-- The total size of pairwise-disjoint finite layers contained in `U` is at
most `U.card`. -/
theorem sum_card_le_card_of_pairwiseDisjoint_subset
    {ι α : Type*} [DecidableEq α] (I : Finset ι) (f : ι → Finset α)
    (U : Finset α) (hdisj : (I : Set ι).PairwiseDisjoint f)
    (hsub : ∀ i ∈ I, f i ⊆ U) :
    ∑ i ∈ I, (f i).card ≤ U.card := by
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_biUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact hsub i hi hxi

/-- Weighted finite pigeonhole principle for disjoint layers.  If `c` times
the ambient capacity is strictly smaller than `d` times the sum of the
weights, some layer satisfies `c * card < d * weight`. -/
theorem exists_card_mul_lt_weight_of_pairwiseDisjoint_subset
    {ι α : Type*} [DecidableEq α] (I : Finset ι) (f : ι → Finset α)
    (U : Finset α) (w : ι → ℕ) (c d : ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint f)
    (hsub : ∀ i ∈ I, f i ⊆ U)
    (hcapacity : c * U.card < d * ∑ i ∈ I, w i) :
    ∃ i ∈ I, c * (f i).card < d * w i := by
  by_contra h
  push Not at h
  have hterm : ∀ i ∈ I, d * w i ≤ c * (f i).card := by
    intro i hi
    exact h i hi
  have hsum : ∑ i ∈ I, d * w i ≤ ∑ i ∈ I, c * (f i).card :=
    Finset.sum_le_sum hterm
  have hlayers := sum_card_le_card_of_pairwiseDisjoint_subset I f U hdisj hsub
  have hscaled : c * (∑ i ∈ I, (f i).card) ≤ c * U.card :=
    Nat.mul_le_mul_left c hlayers
  have hsum' : d * (∑ i ∈ I, w i) ≤ c * ∑ i ∈ I, (f i).card := by
    simpa only [Finset.mul_sum] using hsum
  clear hsum
  omega

/-! ## Restricted-sum layers of a bounded admissible set -/

/-- If `A ⊆ {1, ..., N}`, a positive `s`-fold restricted sum with `s ≤ hi`
lies in the integer interval `[1, hi * N]`. -/
lemma restrictedSumset_subset_Icc_of_bounded
    {N s hi : ℕ} {A : Finset ℤ} (hA : A ⊆ ambient N)
    (hspos : 0 < s) (hshi : s ≤ hi) :
    restrictedSumset s A ⊆ Finset.Icc (1 : ℤ) ((hi * N : ℕ) : ℤ) := by
  intro z hz
  obtain ⟨B, hBA, hBcard, hBsum⟩ := mem_restrictedSumset.mp hz
  have hposA : ∀ x ∈ A, 0 < x := by
    intro x hx
    have hx' := mem_ambient.mp (hA hx)
    omega
  have hBne : B.Nonempty := Finset.card_pos.mp (hBcard.symm ▸ hspos)
  have hzpos : 0 < z := by
    rw [← hBsum]
    exact sum_pos_of_subset hposA hBA hBne
  have hsum_le : (∑ x ∈ B, x) ≤ ∑ _x ∈ B, (N : ℤ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact (mem_ambient.mp (hA (hBA hx))).2
  have hs_hi : (s : ℤ) * (N : ℤ) ≤ (hi : ℤ) * (N : ℤ) := by
    exact Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hshi) (by positivity)
  have hzle : z ≤ ((hi * N : ℕ) : ℤ) := by
    calc
      z = ∑ x ∈ B, x := hBsum.symm
      _ ≤ ∑ _x ∈ B, (N : ℤ) := hsum_le
      _ = (s : ℤ) * (N : ℤ) := by simp [hBcard]
      _ ≤ (hi : ℤ) * (N : ℤ) := hs_hi
      _ = ((hi * N : ℕ) : ℤ) := by norm_num
  simp only [Finset.mem_Icc]
  omega

/-- The sum of the cardinalities of any consecutive positive collection of
restricted-sum layers of a bounded admissible set is at most `hi * N`.

This is the exact layer-counting form of the DF95 selection argument. -/
theorem sum_card_restrictedSumset_Icc_le
    {N lo hi : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A)
    (hlo : 0 < lo) :
    ∑ s ∈ Finset.Icc lo hi, (restrictedSumset s A).card ≤ hi * N := by
  let U : Finset ℤ := Finset.Icc (1 : ℤ) ((hi * N : ℕ) : ℤ)
  have hdisj : ((Finset.Icc lo hi : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun s ↦ restrictedSumset s A) := by
    intro r hr s hs hrs
    change r ∈ Finset.Icc lo hi at hr
    change s ∈ Finset.Icc lo hi at hs
    simp only [Finset.mem_Icc] at hr hs
    exact hA.2 (hlo.trans_le hr.1) (hlo.trans_le hs.1) hrs
  have hsub : ∀ s ∈ Finset.Icc lo hi, restrictedSumset s A ⊆ U := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    exact restrictedSumset_subset_Icc_of_bounded hA.1 (hlo.trans_le hs.1) hs.2
  have hcount := sum_card_le_card_of_pairwiseDisjoint_subset
    (Finset.Icc lo hi) (fun s ↦ restrictedSumset s A) U hdisj hsub
  have hUcard : U.card = hi * N := by
    change (Finset.Icc (1 : ℤ) ((hi * N : ℕ) : ℤ)).card = hi * N
    rw [Int.card_Icc]
    simp only [add_sub_cancel_right, Int.toNat_natCast]
  simpa [hUcard] using hcount

/-- Weighted layer selection for bounded admissible sets.  This formulation
is designed to be instantiated with `w s = s * (K - s)`, `c = 25`, and
`d = 36` in the DF95 structural argument. -/
theorem exists_restrictedSumset_card_mul_lt_of_capacity
    {N lo hi : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A)
    (hlo : 0 < lo) (w : ℕ → ℕ) (c d : ℕ)
    (hcapacity : c * (hi * N) < d * ∑ s ∈ Finset.Icc lo hi, w s) :
    ∃ s ∈ Finset.Icc lo hi,
      c * (restrictedSumset s A).card < d * w s := by
  let U : Finset ℤ := Finset.Icc (1 : ℤ) ((hi * N : ℕ) : ℤ)
  have hdisj : ((Finset.Icc lo hi : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun s ↦ restrictedSumset s A) := by
    intro r hr s hs hrs
    change r ∈ Finset.Icc lo hi at hr
    change s ∈ Finset.Icc lo hi at hs
    simp only [Finset.mem_Icc] at hr hs
    exact hA.2 (hlo.trans_le hr.1) (hlo.trans_le hs.1) hrs
  have hsub : ∀ s ∈ Finset.Icc lo hi, restrictedSumset s A ⊆ U := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    exact restrictedSumset_subset_Icc_of_bounded hA.1 (hlo.trans_le hs.1) hs.2
  apply exists_card_mul_lt_weight_of_pairwiseDisjoint_subset
    (Finset.Icc lo hi) (fun s ↦ restrictedSumset s A) U w c d hdisj hsub
  have hUcard : U.card = hi * N := by
    change (Finset.Icc (1 : ℤ) ((hi * N : ℕ) : ℤ)).card = hi * N
    rw [Int.card_Icc]
    simp only [add_sub_cancel_right, Int.toNat_natCast]
  simpa [hUcard] using hcapacity

/-! ## The numerical constant in DF95 Proposition 1 -/

/-- A denominator-free formula for the quadratic weight summed over an
initial interval.  It is stated in `ℤ` so that the polynomial identity has no
truncated subtraction. -/
private lemma six_mul_sum_range_int_mul_sub (K : ℤ) (n : ℕ) :
    6 * ∑ s ∈ Finset.range n, (s : ℤ) * (K - (s : ℤ)) =
      (n : ℤ) * ((n : ℤ) - 1) * (3 * K - (2 * (n : ℤ) - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- Exact evaluation of the clean subinterval used to control the rounding
in `K / 10` and `3 * K / 4`. -/
private lemma six_mul_sum_Icc_twenty_block (q : ℕ) :
    6 * ∑ s ∈ Finset.Icc (2 * q + 1) (15 * q),
        (s : ℤ) * ((20 * q : ℕ) - s : ℕ) =
      (6526 : ℤ) * q ^ 3 + 117 * q ^ 2 - 13 * q := by
  by_cases hq : q = 0
  · simp [hq]
  have hsq : ∀ s ∈ Finset.Icc (2 * q + 1) (15 * q), s ≤ 20 * q := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    omega
  have hcast :
      (∑ s ∈ Finset.Icc (2 * q + 1) (15 * q),
          (s : ℤ) * ((20 * q : ℕ) - s : ℕ)) =
        ∑ s ∈ Finset.Icc (2 * q + 1) (15 * q),
          (s : ℤ) * (((20 * q : ℕ) : ℤ) - (s : ℤ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [Nat.cast_sub (hsq s hs)]
  rw [hcast]
  have hinterval : Finset.Icc (2 * q + 1) (15 * q) =
      Finset.Ico (2 * q + 1) (15 * q + 1) := by
    ext s
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval, Finset.sum_Ico_eq_sub _ (by omega), mul_sub,
    six_mul_sum_range_int_mul_sub, six_mul_sum_range_int_mul_sub]
  push_cast
  ring

/-- The exact finite arithmetic behind the constants `1.96` and `1.44`.
The cutoff `20060` merely absorbs endpoint rounding; it is not optimized. -/
private lemma df95_capacity_of_card_sq
    {N K : ℕ} (hK : 20060 ≤ K)
    (hKN : 2401 * N < 625 * K ^ 2) :
    25 * ((3 * K / 4) * N) <
      36 * ∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s) := by
  let q := K / 20
  have hq : 1003 ≤ q := by
    dsimp [q]
    omega
  have hqK : 20 * q ≤ K := by
    dsimp [q]
    omega
  have hKq : K ≤ 20 * q + 19 := by
    dsimp [q]
    omega
  have hbq : 3 * K / 4 ≤ 15 * q + 14 := by
    dsimp [q]
    omega
  have hsubset : Finset.Icc (2 * q + 1) (15 * q) ⊆
      Finset.Icc (K / 10) (3 * K / 4) := by
    intro s hs
    simp only [Finset.mem_Icc] at hs ⊢
    dsimp [q] at hs ⊢
    omega
  let T := ∑ s ∈ Finset.Icc (2 * q + 1) (15 * q), s * (20 * q - s)
  let S := ∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s)
  have hTS : T ≤ S := by
    have hpoint :
        (∑ s ∈ Finset.Icc (2 * q + 1) (15 * q), s * (20 * q - s)) ≤
          ∑ s ∈ Finset.Icc (2 * q + 1) (15 * q), s * (K - s) := by
      apply Finset.sum_le_sum
      intro s hs
      exact Nat.mul_le_mul_left s (Nat.sub_le_sub_right hqK s)
    refine hpoint.trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ Nat.zero_le _)
  have hTformula :
      (6 : ℤ) * (T : ℤ) =
        (6526 : ℤ) * q ^ 3 + 117 * q ^ 2 - 13 * q := by
    dsimp [T]
    push_cast
    exact six_mul_sum_Icc_twenty_block q
  have hpoly :
      (625 : ℤ) * (20 * q + 19) ^ 2 * (150 * (15 * q + 14)) <
        36 * 2401 * ((6526 : ℤ) * q ^ 3 + 117 * q ^ 2 - 13 * q) := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hq
    rw [ht]
    push_cast
    have hP : (0 : ℤ) <
        1581336 * (t : ℤ) ^ 3 + 3174603036 * (t : ℤ) ^ 2 +
          1594232666226 * (t : ℤ) + 946427536926 := by
      positivity
    nlinarith only [hP]
  have hKNz : (2401 : ℤ) * N < 625 * K ^ 2 := by
    exact_mod_cast hKN
  have hbpos : (0 : ℤ) < 150 * (3 * K / 4 : ℕ) := by
    have hb : 0 < 3 * K / 4 := by omega
    exact_mod_cast Nat.mul_pos (by omega : 0 < 150) hb
  have hscale := Int.mul_lt_mul_of_pos_right hKNz hbpos
  have hupper :
      (625 : ℤ) * K ^ 2 * (150 * (3 * K / 4 : ℕ)) ≤
        625 * (20 * q + 19) ^ 2 * (150 * (15 * q + 14)) := by
    gcongr
    · exact_mod_cast hKq
    · exact_mod_cast hbq
  have htargetZ :
      (25 : ℤ) * (((3 * K / 4) * N : ℕ) : ℤ) < 36 * T := by
    have hchain := (hscale.trans_le hupper).trans hpoly
    rw [← hTformula] at hchain
    push_cast at hchain ⊢
    ring_nf at hchain ⊢
    nlinarith
  have htarget : 25 * ((3 * K / 4) * N) < 36 * T := by
    exact_mod_cast htargetZ
  exact htarget.trans_le (Nat.mul_le_mul_left 36 hTS)

/-- The rational-constant form used in DF95 Proposition 1.  The hypothesis is
the explicit finite numerical estimate which the eventual threshold supplies;
the conclusion is `|s^A| < 1.44 s(K-s)` with all divisions rounded exactly as
natural-number division dictates. -/
theorem exists_df95_small_restricted_sum_layer
    {N K : ℕ} {A : Finset ℤ} (hA : IsBoundedAdmissible N A)
    (hK : 10 ≤ K)
    (hcapacity :
      25 * ((3 * K / 4) * N) <
        36 * ∑ s ∈ Finset.Icc (K / 10) (3 * K / 4), s * (K - s)) :
    ∃ s, K / 10 ≤ s ∧ s ≤ 3 * K / 4 ∧
      25 * (restrictedSumset s A).card < 36 * s * (K - s) := by
  have hlo : 0 < K / 10 := Nat.div_pos (by omega) (by omega)
  obtain ⟨s, hs, hsmall⟩ := exists_restrictedSumset_card_mul_lt_of_capacity
    hA hlo (fun s ↦ s * (K - s)) 25 36 hcapacity
  simp only [Finset.mem_Icc] at hs
  exact ⟨s, hs.1, hs.2, by simpa [mul_assoc] using hsmall⟩

/-- DF95 Proposition 1 with a concrete (deliberately non-optimal) threshold.
The hypotheses and conclusion use exactly the published constants `1.96` and
`1.44`; the proof above makes all floor errors explicit. -/
theorem exists_df95_small_restricted_sum_layer_of_large
    {N : ℕ} {A : Finset ℤ} (hN : 105000000 ≤ N)
    (hA : IsBoundedAdmissible N A)
    (hlarge : (49 / 25 : ℝ) * Real.sqrt N < A.card) :
    ∃ s, A.card / 10 ≤ s ∧ s ≤ 3 * A.card / 4 ∧
      25 * (restrictedSumset s A).card < 36 * s * (A.card - s) := by
  have hNreal : (105000000 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hbase_sq : (((20060 : ℝ) * 25 / 49) ^ 2) ≤ (105000000 : ℝ) := by
    norm_num
  have hroot : (20060 : ℝ) * 25 / 49 ≤ Real.sqrt N :=
    Real.le_sqrt_of_sq_le (hbase_sq.trans hNreal)
  have hcardlarge : (20060 : ℝ) < (A.card : ℝ) := by
    calc
      (20060 : ℝ) = (49 / 25 : ℝ) * ((20060 : ℝ) * 25 / 49) := by norm_num
      _ ≤ (49 / 25 : ℝ) * Real.sqrt N := by gcongr
      _ < A.card := hlarge
  have hK : 20060 ≤ A.card := by
    exact_mod_cast (le_of_lt hcardlarge)
  have hsquared :
      ((49 / 25 : ℝ) * Real.sqrt N) ^ 2 < (A.card : ℝ) ^ 2 := by
    exact (sq_lt_sq₀ (by positivity) (by positivity)).2 hlarge
  have hcardSq : 2401 * N < 625 * A.card ^ 2 := by
    have hreal : (2401 : ℝ) * N < 625 * (A.card : ℝ) ^ 2 := by
      calc
        (2401 : ℝ) * N =
            625 * ((49 / 25 : ℝ) * Real.sqrt N) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N)]
              ring
        _ < 625 * (A.card : ℝ) ^ 2 := by gcongr
    exact_mod_cast hreal
  have hcapacity := df95_capacity_of_card_sq hK hcardSq
  exact exists_df95_small_restricted_sum_layer hA (hK.trans' (by omega)) hcapacity

/-- Existential-threshold form of DF95 Proposition 1, convenient for the
eventual structural theorem. -/
theorem exists_df95_layer_selection_threshold :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℤ,
      IsBoundedAdmissible N A →
      (49 / 25 : ℝ) * Real.sqrt N < A.card →
      ∃ s, A.card / 10 ≤ s ∧ s ≤ 3 * A.card / 4 ∧
        25 * (restrictedSumset s A).card < 36 * s * (A.card - s) := by
  exact ⟨105000000, fun _ hN A hA hlarge ↦
    exists_df95_small_restricted_sum_layer_of_large hN hA hlarge⟩

end

end Erdos874
