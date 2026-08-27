import Arxiv.Arxiv2411_18291.RelaxedCombinedRainbowExtensions
import Arxiv.Arxiv2411_18291.FiniteGeneratorCoefficient

/-! # The logarithmic generator palette fits at the printed threshold for q at least three -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem logarithmicColourTrialCount_mono {n f g : ℕ} (hn : 1 ≤ n) (hfg : f ≤ g) :
    logarithmicColourTrialCount n f ≤ logarithmicColourTrialCount n g := by
  apply Nat.ceil_mono
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hfg 2)
      (by norm_num : (0 : ℝ) ≤ 9)) hlog

def relaxedGeneratorPaletteSize {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}
    (n : ℕ) (S : ExchangeSystem W q (r + 1)) (P : Block W q) : ℕ :=
  relaxedExtensionPaletteSize n S P +
    logarithmicColourTrialCount n S.base.val.card * S.farCliques.card + 1

theorem relaxedGeneratorPaletteSize_le {W : Type*} [Fintype W] [DecidableEq W]
    {q r n h : ℕ} (hqr : r + 1 < q) (hn : 1 ≤ n)
    (S : ExchangeSystem W q (r + 1)) (P : Block W q)
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h) :
    relaxedGeneratorPaletteSize n S P ≤
      4 * (logarithmicColourTrialCount n (2 * q) * h + 1) := by
  let L := logarithmicColourTrialCount n (2 * q)
  have hroot : (S.base.val ∪ P.val).card ≤ 2 * q := by
    have hh := card_union_le S.base.val P.val
    rw [S.base.property, P.property] at hh
    omega
  have hnew (F : Finset W) : (newEdges F S.graph).card ≤ h :=
    (card_filter_le _ _).trans hSh
  have hfar : S.farCliques.card ≤ h := by
    have hk : 2 ≤ q.choose (r + 1) :=
      (show 2 ≤ q by omega).trans (q_le_choose_succ hqr)
    have hmul := Nat.mul_le_mul_right S.farCliques.card hk
    have hb := S.far_card_mul_le
    omega
  have h₁ : logarithmicColourTrialCount n (r + 1) * (q.choose (r + 1) - 1) ≤ L * h :=
    Nat.mul_le_mul (logarithmicColourTrialCount_mono hn (by omega))
      ((Nat.sub_le _ _).trans hqh)
  have h₂ : logarithmicColourTrialCount n q * (newEdges S.base.val S.graph).card ≤ L * h :=
    Nat.mul_le_mul (logarithmicColourTrialCount_mono hn (by omega)) (hnew _)
  have h₃ : logarithmicColourTrialCount n (S.base.val ∪ P.val).card *
      (newEdges (S.base.val ∪ P.val) S.graph).card ≤ L * h :=
    Nat.mul_le_mul (logarithmicColourTrialCount_mono hn hroot) (hnew _)
  have h₄ : logarithmicColourTrialCount n S.base.val.card * S.farCliques.card ≤ L * h := by
    rw [S.base.property]
    exact Nat.mul_le_mul (logarithmicColourTrialCount_mono hn (by omega)) hfar
  unfold relaxedGeneratorPaletteSize relaxedExtensionPaletteSize
  change _ ≤ 4 * (L * h + 1)
  omega

theorem relaxed_palette_log_coefficient_bound {q r : ℕ} (hqr : r + 1 < q) (hq : 3 ≤ q) :
    81 * 181 * (q + 1) * (3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) *
      paperInverseAlpha q (r + 1) * 2 ^ q ≤ (4 * q) ^ (4 * q) := by
  by_cases hq6 : 6 ≤ q
  · have hb : 1 ≤ 4 * q := by omega
    have hfront : 1583388 * (q + 1) ≤ (4 * q) ^ 6 := by
      calc
        _ ≤ (4 * q) ^ 5 * (4 * q) := Nat.mul_le_mul
          (by
            calc
              _ ≤ 24 ^ 5 := by norm_num
              _ ≤ _ := Nat.pow_le_pow_left (by omega) 5)
          (by omega)
        _ = _ := (pow_succ _ 5).symm
    have hk : (q.choose (r + 1)) ^ 4 * 2 ^ q ≤ 32 ^ q := by
      calc
        _ ≤ (2 ^ q) ^ 4 * 2 ^ q :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.choose_le_two_pow _ _) 4)
        _ = (2 ^ q) ^ 5 := (pow_succ _ 4).symm
        _ = _ := by rw [← pow_mul, Nat.mul_comm q 5, pow_mul]; norm_num
    have ha : ((2 * q) ^ (r + 1)) ^ 2 ≤ ((2 * q) ^ 2) ^ q := by
      calc
        _ ≤ ((2 * q) ^ q) ^ 2 :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right (by omega) hqr.le) 2
        _ = _ := by rw [← pow_mul, Nat.mul_comm q 2, pow_mul]
    have hbase : (2 * q) ^ 2 * 32 ≤ (4 * q) ^ 3 := by
      have hh := Nat.mul_le_mul_left (q ^ 2) hq
      nlinarith only [hh]
    have hback : ((2 * q) ^ (r + 1)) ^ 2 *
        ((q.choose (r + 1)) ^ 4 * 2 ^ q) ≤ (4 * q) ^ (3 * q) := by
      calc
        _ ≤ ((2 * q) ^ 2) ^ q * 32 ^ q := Nat.mul_le_mul ha hk
        _ = ((2 * q) ^ 2 * 32) ^ q := (mul_pow _ _ _).symm
        _ ≤ ((4 * q) ^ 3) ^ q := Nat.pow_le_pow_left hbase q
        _ = _ := (pow_mul _ _ _).symm
    calc
      _ = (1583388 * (q + 1)) *
          (((2 * q) ^ (r + 1)) ^ 2 * ((q.choose (r + 1)) ^ 4 * 2 ^ q)) := by
        unfold paperInverseAlpha
        ring
      _ ≤ (4 * q) ^ 6 * (4 * q) ^ (3 * q) := Nat.mul_le_mul hfront hback
      _ = (4 * q) ^ (6 + 3 * q) := (pow_add _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hb (by omega)
  · have hr : r ≤ 3 := by omega
    interval_cases q <;> interval_cases r <;> norm_num [paperInverseAlpha, Nat.choose] at *

end Arxiv2411_18291
