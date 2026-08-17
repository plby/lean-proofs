/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.RedMass
import ErdosProblems.Erdos55.HueWindow

/-!
# Strong and weak scales in the CFP obstruction

The red part of a scale is strong when one hue has a prefix sum above the
target interval's lower endpoint.  Such a scale consumes a fixed amount of
the normalized red mass, so the Abel estimate makes red-strong scales sparse.
-/

namespace Erdos55

open scoped BigOperators

/-- Lower endpoint used for the omitted interval.  The extra constant `8`
absorbs the endpoint loss in the finite hue-balance lemma. -/
def redThreshold (j : ℕ) : ℕ :=
  2 ^ (j - 1) * (j + 8)

def RedStrong (A : Set ℕ) (h j : ℕ) : Prop :=
  ∃ s < h, redThreshold j < ∑ a ∈ rankHuePrefix A h s (2 ^ j), a

noncomputable def redStrongScales (A : Set ℕ) (h i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 i).filter (RedStrong A h)

theorem redCost_nonneg (A : Set ℕ) (j : ℕ) : 0 ≤ redCost A j := by
  unfold redCost redMass
  positivity

/-- A red-strong scale costs more than half the number of hues. -/
theorem redStrong_imp_cost {A : Set ℕ} (hA : A.Infinite)
    {h j : ℕ} (hh : 0 < h) (hj : 0 < j) (hstrong : RedStrong A h j) :
    (h : ℝ) / 2 < redCost A j := by
  rcases hstrong with ⟨s, hs, hsum⟩
  have hbal := huePrefix_sum_balance hA (h := h) (s := s)
    (N := 2 ^ j) hh hs
  let H : ℕ := ∑ a ∈ rankHuePrefix A h s (2 ^ j), a
  let T : ℕ := ∑ a ∈ rankPrefix A (2 ^ j), a
  have hbalR : (h : ℝ) * H ≤ T + 2 * h * (2 ^ j : ℕ) := by
    exact_mod_cast hbal
  have hsumR : (redThreshold j : ℝ) < H := by
    exact_mod_cast hsum
  have hpowNat : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    omega
  have hpowR : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
    exact_mod_cast hpowNat
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hpR : (0 : ℝ) < (2 : ℝ) ^ (j - 1) := by positivity
  have hTR : (h : ℝ) * (2 : ℝ) ^ (j - 1) * (j + 4) < T := by
    dsimp only [redThreshold] at hsumR
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_ofNat] at hsumR
    rw [hpowNat] at hbalR
    push_cast at hbalR
    nlinarith
  have hmass : redMass A j = (T : ℝ) := by
    simp only [redMass, T, Nat.cast_sum]
  have hden : (0 : ℝ) < (2 : ℝ) ^ j * j := by positivity
  rw [redCost, hmass, lt_div_iff₀ hden]
  rw [hpowR]
  nlinarith

theorem redStrong_card_charge {A : Set ℕ} (hA : A.Infinite)
    {h i : ℕ} (hh : 0 < h) :
    ((redStrongScales A h i).card : ℝ) * ((h : ℝ) / 2) ≤
      ∑ j ∈ Finset.Icc 1 i, redCost A j := by
  classical
  let S := redStrongScales A h i
  have hterm : ∀ j ∈ S, (h : ℝ) / 2 ≤ redCost A j := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact (redStrong_imp_cost hA hh (Finset.mem_Icc.mp hj'.1 |>.1) hj'.2).le
  calc
    (S.card : ℝ) * ((h : ℝ) / 2) = ∑ _j ∈ S, ((h : ℝ) / 2) := by simp
    _ ≤ ∑ j ∈ S, redCost A j := Finset.sum_le_sum hterm
    _ ≤ ∑ j ∈ Finset.Icc 1 i, redCost A j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact (Finset.mem_filter.mp hj).1
      · intro j _ _
        exact redCost_nonneg A j

/-- Under a sufficiently small quadratic dyadic counting constant, fewer
than one eighth of all large initial scales are red-strong. -/
theorem eventually_redStrong_card_lt_eighth_of_quadratic
    {A : Set ℕ} (hA : A.Infinite) (hApos : IsPositiveNatSet A)
    {h K : ℕ} (hh : 0 < h) (hK : 1 ≤ K) {β : ℝ} (hβ : 0 ≤ β)
    (hβsmall : 128 * β ≤ h)
    (hquad : ∀ k, K ≤ k →
      (dyadicCount A k : ℝ) ≤ β * (k : ℝ) ^ 2) :
    ∃ I : ℕ, K ≤ I ∧ ∀ i, I ≤ i →
      ((redStrongScales A h i).card : ℝ) < (i : ℝ) / 8 := by
  let E : ℝ := ∑ k ∈ Finset.Ico 1 K,
    ((dyadicCount A k : ℝ) - dyadicCount A (k - 1)) / k
  let D : ℝ := 4 + 2 * E
  have hE : 0 ≤ E := by
    dsimp only [E]
    apply Finset.sum_nonneg
    intro k hk
    have hmono := dyadicCount_mono hA (Nat.sub_le k 1)
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hmono)) (Nat.cast_nonneg k)
  have hD : 0 < D := by dsimp only [D]; linarith
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  obtain ⟨I₀, hI₀⟩ := exists_nat_gt (32 * D / (h : ℝ))
  refine ⟨max K I₀, le_max_left _ _, ?_⟩
  intro i hi
  have hKi : K ≤ i := (le_max_left K I₀).trans hi
  have hI₀i : I₀ ≤ i := (le_max_right K I₀).trans hi
  have hDsmall : D < (h : ℝ) * i / 32 := by
    have hI₀R : 32 * D / (h : ℝ) < (I₀ : ℝ) := hI₀
    have hIR : (I₀ : ℝ) ≤ i := by exact_mod_cast hI₀i
    rw [div_lt_iff₀ hhR] at hI₀R
    nlinarith
  have hred := sum_redCost_le_of_quadratic hA hApos K i β hβ hK hKi hquad
  have hcharge := redStrong_card_charge hA (i := i) hh
  have hbeterm : 4 * β * (i : ℝ) ≤ (h : ℝ) * i / 32 := by
    have hiR : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    nlinarith
  by_contra hnot
  have hcard : (i : ℝ) / 8 ≤ (redStrongScales A h i).card := le_of_not_gt hnot
  have hlower : (h : ℝ) * i / 16 ≤
      ((redStrongScales A h i).card : ℝ) * ((h : ℝ) / 2) := by
    nlinarith
  dsimp only [D, E] at hDsmall hred
  nlinarith

/-! ## Blue represented values -/

noncomputable def blueHueRepresented (A : Set ℕ) (h s j : ℕ) : Finset ℕ :=
  (subsetSumValues (blueHueWindow A h s j)).filter
    (fun n ↦ 1 ≤ n ∧ n ≤ j * 2 ^ j)

noncomputable def blueRepresented (A : Set ℕ) (h j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range h).biUnion fun s ↦ blueHueRepresented A h s j

def BlueStrong (A : Set ℕ) (h j : ℕ) : Prop :=
  2 ^ j ≤ (blueRepresented A h j).card

noncomputable def blueStrongScales (A : Set ℕ) (h i : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 i).filter (BlueStrong A h)

theorem card_blueHueRepresented_le {A : Set ℕ} (hA : A.Infinite)
    {h s j : ℕ} (hh : 0 < h) (hs : s < h) (hj : 1 ≤ j) :
    ((blueHueRepresented A h s j).card : ℝ) ≤
      Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) := by
  let q : ℕ := 2 ^ (j + 4)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hweighted := card_subsetSums_Icc_le_exp
    (blueHueWindow A h s j) (m := j * 2 ^ j) hq
  have hmass0 := blueHueWindow_exp_balance hA hh hs hj
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hmass :
      (∑ a ∈ blueHueWindow A h s j, Real.exp (-(a : ℝ) / q)) ≤
        blueMass A j / h + h := by
    dsimp only [q] at hmass0 ⊢
    calc
      (∑ a ∈ blueHueWindow A h s j,
          Real.exp (-(a : ℝ) / (2 ^ (j + 4) : ℕ))) ≤
          (blueMass A j + (h : ℝ) ^ 2) / h := by
        rw [le_div_iff₀ hhR]
        nlinarith
      _ = blueMass A j / h + h := by
        field_simp
  have hratio : ((j * 2 ^ j : ℕ) : ℝ) / q = (j : ℝ) / 16 := by
    dsimp only [q]
    push_cast
    rw [show j + 4 = 4 + j by omega, pow_add]
    norm_num
    field_simp
  dsimp only [blueHueRepresented]
  refine hweighted.trans (Real.exp_le_exp.mpr ?_)
  rw [hratio]
  linarith

theorem card_blueRepresented_le {A : Set ℕ} (hA : A.Infinite)
    {h j : ℕ} (hh : 0 < h) (hj : 1 ≤ j) :
    ((blueRepresented A h j).card : ℝ) ≤
      (h : ℝ) * Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) := by
  classical
  calc
    ((blueRepresented A h j).card : ℝ) ≤
        ∑ s ∈ Finset.range h, ((blueHueRepresented A h s j).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ Finset.range h,
        Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) := by
      apply Finset.sum_le_sum
      intro s hs
      exact card_blueHueRepresented_le hA hh (Finset.mem_range.mp hs) hj
    _ = (h : ℝ) * Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) := by simp

/-- A blue-strong scale forces a linear amount of exponential mass. -/
theorem blueStrong_imp_mass {A : Set ℕ} (hA : A.Infinite)
    {h j : ℕ} (hh : 0 < h) (hj : 1 ≤ j) (hstrong : BlueStrong A h j) :
    (j : ℝ) * Real.log 2 ≤
      2 * h + (j : ℝ) / 16 + blueMass A j / h := by
  have hcard := card_blueRepresented_le hA hh hj
  have hpow : ((2 ^ j : ℕ) : ℝ) ≤ (blueRepresented A h j).card := by
    exact_mod_cast hstrong
  have hhexp : (h : ℝ) ≤ Real.exp h := by
    have := Real.add_one_le_exp (h : ℝ)
    linarith
  have hpos : 0 < Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) := Real.exp_pos _
  have hbound : ((2 ^ j : ℕ) : ℝ) ≤
      Real.exp ((h : ℝ) + ((j : ℝ) / 16 + blueMass A j / h + h)) := by
    calc
      ((2 ^ j : ℕ) : ℝ) ≤ (blueRepresented A h j).card := hpow
      _ ≤ (h : ℝ) * Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) := hcard
      _ ≤ Real.exp h * Real.exp ((j : ℝ) / 16 + blueMass A j / h + h) :=
        mul_le_mul_of_nonneg_right hhexp hpos.le
      _ = Real.exp ((h : ℝ) + ((j : ℝ) / 16 + blueMass A j / h + h)) := by
        exact (Real.exp_add _ _).symm
  have hexp : Real.exp ((j : ℝ) * Real.log 2) = ((2 ^ j : ℕ) : ℝ) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  rw [← hexp] at hbound
  have := Real.exp_le_exp.mp hbound
  nlinarith

private theorem sum_subset_Icc_lower_of_three_quarters
    (S : Finset ℕ) (i : ℕ) (hS : S ⊆ Finset.Icc 1 i)
    (hcard : 3 * (i : ℝ) / 4 ≤ (S.card : ℝ)) :
    (i : ℝ) ^ 2 / 8 ≤ ∑ j ∈ S, (j : ℝ) := by
  classical
  let Lo := S.filter fun j ↦ j ≤ i / 2
  let Hi := S.filter fun j ↦ ¬j ≤ i / 2
  have hLoSubset : Lo ⊆ Finset.Icc 1 (i / 2) := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjS := Finset.mem_Icc.mp (hS hj'.1)
    exact Finset.mem_Icc.mpr ⟨hjS.1, hj'.2⟩
  have hLoCard : Lo.card ≤ i / 2 := by
    calc
      Lo.card ≤ (Finset.Icc 1 (i / 2)).card := Finset.card_le_card hLoSubset
      _ ≤ i / 2 := by simp
  have hpart : Lo.card + Hi.card = S.card := by
    simpa [Lo, Hi] using
      Finset.card_filter_add_card_filter_not (s := S) (fun j ↦ j ≤ i / 2)
  have hHiCard : (i : ℝ) / 4 ≤ (Hi.card : ℝ) := by
    have hLoCardR : (Lo.card : ℝ) ≤ (i : ℝ) / 2 := by
      have hcast : ((i / 2 : ℕ) : ℝ) ≤ (i : ℝ) / 2 := by
        have hnat : 2 * (i / 2) ≤ i := by omega
        have hnatR : (2 : ℝ) * (i / 2 : ℕ) ≤ i := by exact_mod_cast hnat
        linarith
      exact (by exact_mod_cast hLoCard : (Lo.card : ℝ) ≤ (i / 2 : ℕ)).trans hcast
    have hpartR : (Lo.card : ℝ) + Hi.card = S.card := by exact_mod_cast hpart
    linarith
  have hHiTerm : ∀ j ∈ Hi, (i : ℝ) / 2 ≤ j := by
    intro j hj
    have hjnot : ¬j ≤ i / 2 := (Finset.mem_filter.mp hj).2
    have hij : i ≤ 2 * j := by omega
    have hijR : (i : ℝ) ≤ 2 * j := by exact_mod_cast hij
    linarith
  have hHiSum : (Hi.card : ℝ) * ((i : ℝ) / 2) ≤
      ∑ j ∈ Hi, (j : ℝ) := by
    calc
      (Hi.card : ℝ) * ((i : ℝ) / 2) =
          ∑ _j ∈ Hi, ((i : ℝ) / 2) := by simp
      _ ≤ ∑ j ∈ Hi, (j : ℝ) := Finset.sum_le_sum hHiTerm
  have hHiSubset : Hi ⊆ S := Finset.filter_subset _ _
  have hHiLe : (∑ j ∈ Hi, (j : ℝ)) ≤ ∑ j ∈ S, (j : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hHiSubset
    intro j _ _
    positivity
  have hiR : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  nlinarith

theorem sum_blueMass_le_of_quadratic {A : Set ℕ} (hA : A.Infinite)
    (hApos : IsPositiveNatSet A) {K i : ℕ} {β : ℝ}
    (hi : 1 ≤ i) (hKi : K ≤ i) (hβ : 0 ≤ β)
    (hquad : ∀ k, K ≤ k →
      (dyadicCount A k : ℝ) ≤ β * (k : ℝ) ^ 2) :
    (∑ j ∈ Finset.Icc 1 i, blueMass A j) ≤ 128 * β * (i : ℝ) ^ 2 := by
  have hipow : i * 2 ^ i ≤ 2 ^ (2 * i) := by
    have hii : i ≤ 2 ^ i := Nat.le_of_lt i.lt_two_pow_self
    calc
      i * 2 ^ i ≤ 2 ^ i * 2 ^ i := Nat.mul_le_mul_right _ hii
      _ = 2 ^ (2 * i) := by rw [← pow_add]; congr 1; omega
  have hprefix : (rankPrefix A (i * 2 ^ i)).card ≤ dyadicCount A (2 * i) := by
    apply Finset.card_le_card
    apply rankPrefix_mono hA hipow
  have hKi2 : K ≤ 2 * i := hKi.trans (by omega)
  have hcount := hquad (2 * i) hKi2
  have hmass := sum_blueMass_le hA hApos i
  have hprefixR : ((rankPrefix A (i * 2 ^ i)).card : ℝ) ≤
      dyadicCount A (2 * i) := by exact_mod_cast hprefix
  calc
    (∑ j ∈ Finset.Icc 1 i, blueMass A j) ≤
        32 * ((rankPrefix A (i * 2 ^ i)).card : ℝ) := hmass
    _ ≤ 32 * (dyadicCount A (2 * i) : ℝ) := by gcongr
    _ ≤ 32 * (β * ((2 * i : ℕ) : ℝ) ^ 2) := by gcongr
    _ = 128 * β * (i : ℝ) ^ 2 := by push_cast; ring

/-- Fewer than three quarters of all sufficiently long initial scales are
blue-strong. -/
theorem eventually_blueStrong_card_lt_three_quarters_of_quadratic
    {A : Set ℕ} (hA : A.Infinite) (hApos : IsPositiveNatSet A)
    {h K : ℕ} (hh : 0 < h) (hK : 1 ≤ K) {β : ℝ} (hβ : 0 ≤ β)
    (hβsmall : 8192 * β ≤ h)
    (hquad : ∀ k, K ≤ k →
      (dyadicCount A k : ℝ) ≤ β * (k : ℝ) ^ 2) :
    ∃ I : ℕ, K ≤ I ∧ ∀ i, I ≤ i →
      ((blueStrongScales A h i).card : ℝ) < 3 * (i : ℝ) / 4 := by
  classical
  refine ⟨max K (64 * h + 1), le_max_left _ _, ?_⟩
  intro i hi
  have hKi : K ≤ i := (le_max_left K (64 * h + 1)).trans hi
  have hi1 : 1 ≤ i := hK.trans hKi
  have hbig : 64 * h < i := by
    have := (le_max_right K (64 * h + 1)).trans hi
    omega
  let S := blueStrongScales A h i
  have hS : S ⊆ Finset.Icc 1 i := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hterm : ∀ j ∈ S,
      7 * (j : ℝ) / 16 ≤ 2 * h + blueMass A j / h := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hj1 := (Finset.mem_Icc.mp hj'.1).1
    have hmass := blueStrong_imp_mass hA hh hj1 hj'.2
    have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    have hjR : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith
  have hsumTerm :
      7 / 16 * (∑ j ∈ S, (j : ℝ)) ≤
        2 * (h : ℝ) * S.card +
          (∑ j ∈ S, blueMass A j) / h := by
    calc
      7 / 16 * (∑ j ∈ S, (j : ℝ)) =
          ∑ j ∈ S, 7 * (j : ℝ) / 16 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ ∑ j ∈ S, (2 * (h : ℝ) + blueMass A j / h) :=
        Finset.sum_le_sum hterm
      _ = 2 * (h : ℝ) * S.card +
          (∑ j ∈ S, blueMass A j) / h := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
        simp
        ring
  have hmassSubset : (∑ j ∈ S, blueMass A j) ≤
      ∑ j ∈ Finset.Icc 1 i, blueMass A j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro j _ _
    unfold blueMass
    positivity
  have hmassAll := sum_blueMass_le_of_quadratic hA hApos hi1 hKi hβ hquad
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hmassDiv : (∑ j ∈ S, blueMass A j) / h ≤ (i : ℝ) ^ 2 / 64 := by
    have hsmall : 128 * β / (h : ℝ) ≤ 1 / 64 := by
      rw [div_le_iff₀ hhR]
      nlinarith
    have hiR : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    calc
      (∑ j ∈ S, blueMass A j) / h ≤
          (∑ j ∈ Finset.Icc 1 i, blueMass A j) / h :=
        div_le_div_of_nonneg_right hmassSubset hhR.le
      _ ≤ (128 * β * (i : ℝ) ^ 2) / h :=
        div_le_div_of_nonneg_right hmassAll hhR.le
      _ = (128 * β / h) * (i : ℝ) ^ 2 := by ring
      _ ≤ (1 / 64 : ℝ) * (i : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
      _ = (i : ℝ) ^ 2 / 64 := by ring
  have hScard : (S.card : ℝ) ≤ i := by
    exact_mod_cast (Finset.card_le_card hS).trans (by simp)
  by_contra hnot
  have hcardLower : 3 * (i : ℝ) / 4 ≤ (S.card : ℝ) := le_of_not_gt hnot
  have hsumLower := sum_subset_Icc_lower_of_three_quarters S i hS hcardLower
  have hbigR : 64 * (h : ℝ) < i := by exact_mod_cast hbig
  nlinarith

end Erdos55
