/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.HuePrefix

/-!
# Dyadic red mass in the CFP obstruction

This file contains the summation-by-parts estimate used to show that only a
small proportion of dyadic scales can have a large monochromatic red sum.
The estimates are deliberately stated with ample constant slack.
-/

namespace Erdos55

open scoped BigOperators

theorem card_rankPrefix {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) (N : ℕ) :
    (rankPrefix A N).card = countUpTo A N := by
  classical
  rw [countUpTo_eq_ncard_inter, ← Set.ncard_coe_finset]
  apply congrArg Set.ncard
  ext a
  rw [Finset.mem_coe, mem_rankPrefix_iff hA]
  simp only [Set.mem_inter_iff, Set.mem_Icc]
  constructor
  · rintro ⟨haA, haN⟩
    exact ⟨haA, hApos haA, haN⟩
  · rintro ⟨haA, _, haN⟩
    exact ⟨haA, haN⟩

/-- Number of elements through the dyadic cutoff `2^k`. -/
noncomputable def dyadicCount (A : Set ℕ) (k : ℕ) : ℕ :=
  (rankPrefix A (2 ^ k)).card

/-- The elements in the `k`th dyadic shell `(2^(k-1), 2^k]`. -/
noncomputable def dyadicShell (A : Set ℕ) (k : ℕ) : Finset ℕ :=
  rankPrefix A (2 ^ k) \ rankPrefix A (2 ^ (k - 1))

theorem dyadicCount_mono {A : Set ℕ} (hA : A.Infinite) :
    Monotone (dyadicCount A) := by
  intro k l hkl
  apply Finset.card_le_card
  intro a ha
  rw [mem_rankPrefix_iff hA] at ha ⊢
  refine ⟨ha.1, ha.2.trans ?_⟩
  exact Nat.pow_le_pow_right (by omega) hkl

theorem card_dyadicShell {A : Set ℕ} (hA : A.Infinite) {k : ℕ}
    (hk : 1 ≤ k) :
    (dyadicShell A k).card = dyadicCount A k - dyadicCount A (k - 1) := by
  classical
  apply Finset.card_sdiff_of_subset
  intro a ha
  rw [mem_rankPrefix_iff hA] at ha ⊢
  refine ⟨ha.1, ha.2.trans ?_⟩
  exact Nat.pow_le_pow_right (by omega) (Nat.sub_le k 1)

/-- A finite Abel identity for a real nondecreasing sequence. -/
theorem sum_Icc_difference_div (C : ℕ → ℝ) (K i : ℕ)
    (hK : 1 ≤ K) (hKi : K ≤ i) :
    (∑ k ∈ Finset.Icc K i, (C k - C (k - 1)) / k) =
      C i / i - C (K - 1) / K +
        ∑ k ∈ Finset.Ico K i, C k / ((k : ℝ) * (k + 1)) := by
  induction i, hKi using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton, Finset.Ico_self,
        Finset.sum_empty, add_zero]
      ring
  | succ i hKi ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hKi, ih]
      have hi : (0 : ℝ) < i := by exact_mod_cast hK.trans hKi
      have hisucc : (0 : ℝ) < i + 1 := by positivity
      have hid :
          (C (i + 1) - C i) / ((i : ℝ) + 1) =
            C (i + 1) / ((i : ℝ) + 1) - C i / i +
              C i / ((i : ℝ) * ((i : ℝ) + 1)) := by
        field_simp [ne_of_gt hi, ne_of_gt hisucc]
        ring
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [hid]
      ring

/-- Abel summation with an eventual quadratic bound.  The contribution of
the finitely many scales before `K` is isolated in the first sum. -/
theorem sum_difference_div_le_of_quadratic
    (C : ℕ → ℝ) (K i : ℕ) (β : ℝ)
    (hC : ∀ k, 0 ≤ C k) (hβ : 0 ≤ β) (hK : 1 ≤ K) (hKi : K ≤ i)
    (hquad : ∀ k, K ≤ k → C k ≤ β * (k : ℝ) ^ 2) :
    (∑ k ∈ Finset.Icc 1 i, (C k - C (k - 1)) / k) ≤
      (∑ k ∈ Finset.Ico 1 K, (C k - C (k - 1)) / k) +
        2 * β * i := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.sum_Ico_consecutive _ hK (by omega)]
  rw [Finset.Ico_add_one_right_eq_Icc]
  rw [sum_Icc_difference_div C K i hK hKi]
  have htail :
      C i / i - C (K - 1) / K +
          ∑ k ∈ Finset.Ico K i, C k / ((k : ℝ) * (k + 1)) ≤
        2 * β * i := by
    have hi : (0 : ℝ) < i := by exact_mod_cast hK.trans hKi
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    calc
      C i / i - C (K - 1) / K +
            ∑ k ∈ Finset.Ico K i, C k / ((k : ℝ) * (k + 1))
          ≤ C i / i +
            ∑ k ∈ Finset.Ico K i, C k / ((k : ℝ) * (k + 1)) := by
              have hy : 0 ≤ C (K - 1) / (K : ℝ) :=
                div_nonneg (hC _) hKpos.le
              linarith
      _ ≤ β * i + ∑ _k ∈ Finset.Ico K i, β := by
        apply add_le_add
        · calc
          C i / i ≤ (β * (i : ℝ) ^ 2) / i :=
            div_le_div_of_nonneg_right (hquad i hKi) hi.le
          _ = β * i := by field_simp
        · apply Finset.sum_le_sum
          intro k hk
          have hkK : K ≤ k := (Finset.mem_Ico.mp hk).1
          have hkpos : (0 : ℝ) < k := by exact_mod_cast hK.trans hkK
          have hksucc : (0 : ℝ) < k + 1 := by positivity
          calc
            C k / ((k : ℝ) * (k + 1)) ≤
                (β * (k : ℝ) ^ 2) / ((k : ℝ) * (k + 1)) :=
              div_le_div_of_nonneg_right (hquad k hkK)
                (mul_nonneg hkpos.le hksucc.le)
            _ ≤ β := by
              rw [div_le_iff₀ (mul_pos hkpos hksucc)]
              nlinarith [hβ]
      _ ≤ β * i + β * i := by
        have hconst : (∑ _k ∈ Finset.Ico K i, β) ≤ β * i := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcard : (Finset.Ico K i).card ≤ i := by simp
          calc
            ((Finset.Ico K i).card : ℝ) * β ≤ (i : ℝ) * β :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hβ
            _ = β * i := by ring
        linarith
      _ = 2 * β * i := by ring
  linarith

/-- Total size of the red prefix at scale `j`. -/
noncomputable def redMass (A : Set ℕ) (j : ℕ) : ℝ :=
  ∑ a ∈ rankPrefix A (2 ^ j), (a : ℝ)

/-- Normalized red mass, the quantity charged to scale `j`. -/
noncomputable def redCost (A : Set ℕ) (j : ℕ) : ℝ :=
  redMass A j / ((2 : ℝ) ^ j * j)

private theorem rankPrefix_pow_subset {A : Set ℕ} (hA : A.Infinite)
    {k l : ℕ} (hkl : k ≤ l) :
    rankPrefix A (2 ^ k) ⊆ rankPrefix A (2 ^ l) := by
  intro a ha
  rw [mem_rankPrefix_iff hA] at ha ⊢
  exact ⟨ha.1, ha.2.trans (Nat.pow_le_pow_right (by omega) hkl)⟩

theorem dyadicShell_mass_le {A : Set ℕ} (hA : A.Infinite) {k : ℕ}
    (hk : 1 ≤ k) :
    (∑ a ∈ dyadicShell A k, (a : ℝ)) ≤
      (2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ) := by
  have ha : ∀ a ∈ dyadicShell A k, (a : ℝ) ≤ (2 : ℝ) ^ k := by
    intro a ha
    have haP := (Finset.mem_sdiff.mp ha).1
    have hale := (mem_rankPrefix_iff hA).mp haP |>.2
    exact_mod_cast hale
  calc
    (∑ a ∈ dyadicShell A k, (a : ℝ)) ≤
        ∑ _a ∈ dyadicShell A k, (2 : ℝ) ^ k :=
      Finset.sum_le_sum ha
    _ = (2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ) := by
      simp [mul_comm]

theorem redMass_le_shells {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) {j : ℕ} (hj : 1 ≤ j) :
    redMass A j ≤ 4 +
      ∑ k ∈ Finset.Icc 2 j,
        (2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ) := by
  induction j, hj using Nat.le_induction with
  | base =>
      rw [show Finset.Icc 2 1 = ∅ by ext k; simp]
      simp only [Finset.sum_empty, add_zero]
      have hterm : ∀ a ∈ rankPrefix A (2 ^ 1), (a : ℝ) ≤ 2 := by
        intro a ha
        have hale := (mem_rankPrefix_iff hA).mp ha |>.2
        norm_num at hale ⊢
        exact_mod_cast hale
      have hcard : (rankPrefix A (2 ^ 1)).card ≤ 2 := by
        rw [card_rankPrefix hA hApos]
        exact countUpTo_le A 2
      calc
        redMass A 1 ≤ ∑ _a ∈ rankPrefix A (2 ^ 1), (2 : ℝ) :=
          Finset.sum_le_sum hterm
        _ = ((rankPrefix A (2 ^ 1)).card : ℝ) * 2 := by simp
        _ ≤ 2 * 2 := by gcongr; exact_mod_cast hcard
        _ = 4 := by norm_num
  | succ j hj ih =>
      have hsub : rankPrefix A (2 ^ j) ⊆ rankPrefix A (2 ^ (j + 1)) :=
        rankPrefix_pow_subset hA (by omega)
      have hdecomp :
          redMass A (j + 1) = redMass A j +
            ∑ a ∈ dyadicShell A (j + 1), (a : ℝ) := by
        rw [redMass, redMass, dyadicShell]
        simp only [Nat.add_sub_cancel]
        symm
        rw [add_comm]
        exact Finset.sum_sdiff hsub
      rw [hdecomp, Finset.sum_Icc_succ_top (by omega)]
      have hshell := dyadicShell_mass_le hA (A := A) (k := j + 1) (by omega)
      linarith

/-- A finite tail of powers of `1/2`, after restoring the leading power,
is at most `2`. -/
theorem sum_pow_div_pow_le_two (k i : ℕ) :
    (∑ j ∈ Finset.Icc k i, (2 : ℝ) ^ k / (2 : ℝ) ^ j) ≤ 2 := by
  have hgeom := geom_sum_Ico_le_of_lt_one
    (K := ℝ) (m := k) (n := i + 1) (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  rw [Finset.Ico_add_one_right_eq_Icc] at hgeom
  calc
    (∑ j ∈ Finset.Icc k i, (2 : ℝ) ^ k / (2 : ℝ) ^ j) =
        (2 : ℝ) ^ k * ∑ j ∈ Finset.Icc k i, ((1 : ℝ) / 2) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [one_div, inv_pow]
      ring
    _ ≤ (2 : ℝ) ^ k * (((1 : ℝ) / 2) ^ k / (1 - (1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 2 := by
      rw [one_div, inv_pow]
      field_simp <;> norm_num

/-- Exchange the order of summation over the finite triangle
`2 ≤ k ≤ j ≤ i`. -/
theorem sum_triangle_comm (F : ℕ → ℕ → ℝ) (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, ∑ k ∈ Finset.Icc 2 j, F k j) =
      ∑ k ∈ Finset.Icc 2 i, ∑ j ∈ Finset.Icc k i, F k j := by
  classical
  calc
    (∑ j ∈ Finset.Icc 1 i, ∑ k ∈ Finset.Icc 2 j, F k j) =
        ∑ j ∈ Finset.Icc 1 i, ∑ k ∈ Finset.Icc 2 i,
          if k ≤ j then F k j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hji : j ≤ i := (Finset.mem_Icc.mp hj).2
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro k hk
        rfl
    _ = ∑ k ∈ Finset.Icc 2 i, ∑ j ∈ Finset.Icc 1 i,
          if k ≤ j then F k j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ k ∈ Finset.Icc 2 i, ∑ j ∈ Finset.Icc k i, F k j := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      · intro j hj
        rfl

private theorem redCost_le_shells {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) {j : ℕ} (hj : 1 ≤ j) :
    redCost A j ≤
      4 / ((2 : ℝ) ^ j * j) +
        ∑ k ∈ Finset.Icc 2 j,
          ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
            ((2 : ℝ) ^ j * j) := by
  have hden : 0 ≤ (2 : ℝ) ^ j * j := by positivity
  unfold redCost
  calc
    redMass A j / ((2 : ℝ) ^ j * j) ≤
        (4 + ∑ k ∈ Finset.Icc 2 j,
          (2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
            ((2 : ℝ) ^ j * j) :=
      div_le_div_of_nonneg_right (redMass_le_shells hA hApos hj) hden
    _ = 4 / ((2 : ℝ) ^ j * j) +
        ∑ k ∈ Finset.Icc 2 j,
          ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
            ((2 : ℝ) ^ j * j) := by
      rw [add_div, Finset.sum_div]

private theorem low_redCost_sum_le (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, 4 / ((2 : ℝ) ^ j * j)) ≤ 4 := by
  have hterm : ∀ j ∈ Finset.Icc 1 i,
      4 / ((2 : ℝ) ^ j * j) ≤ 2 * ((2 : ℝ) ^ 1 / (2 : ℝ) ^ j) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hp : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    have hden : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ j * j := by
      nlinarith [show (1 : ℝ) ≤ j by exact_mod_cast hj1]
    calc
      4 / ((2 : ℝ) ^ j * j) ≤ 4 / (2 : ℝ) ^ j :=
        div_le_div_of_nonneg_left (by norm_num) hp hden
      _ = 2 * ((2 : ℝ) ^ 1 / (2 : ℝ) ^ j) := by norm_num; ring
  calc
    (∑ j ∈ Finset.Icc 1 i, 4 / ((2 : ℝ) ^ j * j)) ≤
        ∑ j ∈ Finset.Icc 1 i, 2 * ((2 : ℝ) ^ 1 / (2 : ℝ) ^ j) :=
      Finset.sum_le_sum hterm
    _ = 2 * ∑ j ∈ Finset.Icc 1 i, ((2 : ℝ) ^ 1 / (2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * 2 := mul_le_mul_of_nonneg_left (sum_pow_div_pow_le_two 1 i) (by norm_num)
    _ = 4 := by norm_num

private theorem shell_redCost_tail_le (A : Set ℕ) (k i : ℕ) (hk : 1 ≤ k) :
    (∑ j ∈ Finset.Icc k i,
      ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
        ((2 : ℝ) ^ j * j)) ≤
      2 * ((dyadicShell A k).card : ℝ) / k := by
  let d : ℝ := (dyadicShell A k).card
  have hd : 0 ≤ d := by positivity
  have hterm : ∀ j ∈ Finset.Icc k i,
      ((2 : ℝ) ^ k * d) / ((2 : ℝ) ^ j * j) ≤
        (d / k) * ((2 : ℝ) ^ k / (2 : ℝ) ^ j) := by
    intro j hj
    have hkj : k ≤ j := (Finset.mem_Icc.mp hj).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hjR : (0 : ℝ) < j := by exact_mod_cast hk.trans hkj
    have hpj : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
    calc
      ((2 : ℝ) ^ k * d) / ((2 : ℝ) ^ j * j) =
          (d * ((2 : ℝ) ^ k / (2 : ℝ) ^ j)) / j := by
        field_simp
      _ ≤ (d * ((2 : ℝ) ^ k / (2 : ℝ) ^ j)) / k := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hkR
        · exact_mod_cast hkj
      _ = (d / k) * ((2 : ℝ) ^ k / (2 : ℝ) ^ j) := by ring
  calc
    (∑ j ∈ Finset.Icc k i,
      ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
        ((2 : ℝ) ^ j * j)) ≤
        ∑ j ∈ Finset.Icc k i,
          (d / k) * ((2 : ℝ) ^ k / (2 : ℝ) ^ j) :=
      Finset.sum_le_sum hterm
    _ = (d / k) *
        ∑ j ∈ Finset.Icc k i, ((2 : ℝ) ^ k / (2 : ℝ) ^ j) := by
      rw [Finset.mul_sum]
    _ ≤ (d / k) * 2 :=
      mul_le_mul_of_nonneg_left (sum_pow_div_pow_le_two k i)
        (div_nonneg hd (by positivity))
    _ = 2 * ((dyadicShell A k).card : ℝ) / k := by
      dsimp only [d]
      ring

/-- The total normalized red mass is controlled by the Abel harmonic sum of
the dyadic counting increments. -/
theorem sum_redCost_le_harmonic {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) (i : ℕ) :
    (∑ j ∈ Finset.Icc 1 i, redCost A j) ≤
      4 + 2 * ∑ k ∈ Finset.Icc 1 i,
        ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k := by
  have hscale : ∀ j ∈ Finset.Icc 1 i, redCost A j ≤
      4 / ((2 : ℝ) ^ j * j) +
        ∑ k ∈ Finset.Icc 2 j,
          ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
            ((2 : ℝ) ^ j * j) := by
    intro j hj
    exact redCost_le_shells hA hApos (Finset.mem_Icc.mp hj |>.1)
  have hcard (k : ℕ) (hk : k ∈ Finset.Icc 2 i) :
      ((dyadicShell A k).card : ℝ) =
        (dyadicCount A k : ℝ) - dyadicCount A (k - 1) := by
    have hk1 : 1 ≤ k := by
      have hk2 := (Finset.mem_Icc.mp hk).1
      omega
    rw [card_dyadicShell hA hk1, Nat.cast_sub]
    exact dyadicCount_mono hA (Nat.sub_le k 1)
  have hinc (k : ℕ) :
      0 ≤ (dyadicCount A k : ℝ) - dyadicCount A (k - 1) := by
    exact sub_nonneg.mpr (by exact_mod_cast dyadicCount_mono hA (Nat.sub_le k 1))
  calc
    (∑ j ∈ Finset.Icc 1 i, redCost A j) ≤
        ∑ j ∈ Finset.Icc 1 i,
          (4 / ((2 : ℝ) ^ j * j) +
            ∑ k ∈ Finset.Icc 2 j,
              ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
                ((2 : ℝ) ^ j * j)) :=
      Finset.sum_le_sum hscale
    _ = (∑ j ∈ Finset.Icc 1 i, 4 / ((2 : ℝ) ^ j * j)) +
        ∑ j ∈ Finset.Icc 1 i,
          ∑ k ∈ Finset.Icc 2 j,
            ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
              ((2 : ℝ) ^ j * j) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ j ∈ Finset.Icc 1 i, 4 / ((2 : ℝ) ^ j * j)) +
        ∑ k ∈ Finset.Icc 2 i,
          ∑ j ∈ Finset.Icc k i,
            ((2 : ℝ) ^ k * ((dyadicShell A k).card : ℝ)) /
              ((2 : ℝ) ^ j * j) := by
      rw [sum_triangle_comm]
    _ ≤ 4 + ∑ k ∈ Finset.Icc 2 i,
          (2 * ((dyadicShell A k).card : ℝ) / k) := by
      apply add_le_add (low_redCost_sum_le i)
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : 1 ≤ k := by
        have hk2 := (Finset.mem_Icc.mp hk).1
        omega
      exact shell_redCost_tail_le A k i hk1
    _ = 4 + 2 * ∑ k ∈ Finset.Icc 2 i,
          ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hcard k hk]
      ring
    _ ≤ 4 + 2 * ∑ k ∈ Finset.Icc 1 i,
          ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k := by
      have hsum :
          (∑ k ∈ Finset.Icc 2 i,
            ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k) ≤
          ∑ k ∈ Finset.Icc 1 i,
            ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_Icc] at hk ⊢
          omega
        · intro k hk hnot
          exact div_nonneg (hinc k) (Nat.cast_nonneg k)
      linarith

/-- Combining the shell estimate with finite Abel summation. -/
theorem sum_redCost_le_of_quadratic {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) (K i : ℕ) (β : ℝ)
    (hβ : 0 ≤ β) (hK : 1 ≤ K) (hKi : K ≤ i)
    (hquad : ∀ k, K ≤ k → (dyadicCount A k : ℝ) ≤ β * (k : ℝ) ^ 2) :
    (∑ j ∈ Finset.Icc 1 i, redCost A j) ≤
      4 + 2 * (∑ k ∈ Finset.Ico 1 K,
        ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k) +
        4 * β * i := by
  have habel := sum_difference_div_le_of_quadratic
    (fun k ↦ (dyadicCount A k : ℝ)) K i β
    (fun _ ↦ Nat.cast_nonneg _) hβ hK hKi hquad
  have hred := sum_redCost_le_harmonic hA hApos i
  linarith

/-- An eventual natural-log-squared counting bound gives the required
quadratic bound at dyadic cutoffs. -/
theorem eventually_dyadicCount_le_quadratic {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) {c : ℝ} (hc : 0 ≤ c) (r N₀ : ℕ)
    (hcount : ∀ N, N₀ ≤ N →
      (countUpTo A N : ℝ) ≤ c * (r : ℝ) * Real.log (N : ℝ) ^ 2) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ k, K ≤ k →
      (dyadicCount A k : ℝ) ≤ (c * r) * (k : ℝ) ^ 2 := by
  refine ⟨N₀ + 1, by omega, ?_⟩
  intro k hk
  have hkN : N₀ ≤ 2 ^ k := by
    have hkpow : k ≤ 2 ^ k := Nat.le_of_lt k.lt_two_pow_self
    omega
  rw [dyadicCount, card_rankPrefix hA hApos]
  calc
    (countUpTo A (2 ^ k) : ℝ) ≤
        c * (r : ℝ) * Real.log ((2 ^ k : ℕ) : ℝ) ^ 2 :=
      hcount _ hkN
    _ ≤ (c * r) * (k : ℝ) ^ 2 := by
      have hlog : Real.log ((2 ^ k : ℕ) : ℝ) =
          (k : ℝ) * Real.log 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
      rw [hlog]
      have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog2le : Real.log 2 ≤ 1 := by
        linarith [Real.log_two_lt_d9]
      have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      have hkrlog : (k : ℝ) * Real.log 2 ≤ k := by nlinarith
      have hkrnonneg : 0 ≤ (k : ℝ) * Real.log 2 := mul_nonneg hkR hlog2nonneg
      have hsq : ((k : ℝ) * Real.log 2) ^ 2 ≤ (k : ℝ) ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hkrnonneg hkrlog
      have hcr : 0 ≤ c * (r : ℝ) := mul_nonneg hc (Nat.cast_nonneg r)
      nlinarith

end Erdos55
