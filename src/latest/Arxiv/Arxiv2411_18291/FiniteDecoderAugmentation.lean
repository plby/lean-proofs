import Arxiv.Arxiv2411_18291.FlexibleLocalDecoders
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth
import Arxiv.Arxiv2411_18291.DecoderAugmentation

/-! # Finite decoder augmentation with an explicit coefficient budget -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem decoder_augmentation_coefficient_bound {q r : ℕ} (hqr : r + 1 < q) :
    1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) ≤
      (4 * q) ^ (2 * q + 1) := by
  have hK : q.choose (r + 1) ≤ (4 * q) ^ q :=
    (Nat.choose_le_two_pow q (r + 1)).trans (Nat.pow_le_pow_left (by omega) q)
  have hprod : q.choose (r + 1) * (q + (r + 1)).choose (r + 1) ≤ (4 * q) ^ q := by
    calc
      _ ≤ 2 ^ q * 2 ^ (q + (r + 1)) := Nat.mul_le_mul
        (Nat.choose_le_two_pow q (r + 1)) (Nat.choose_le_two_pow (q + (r + 1)) (r + 1))
      _ = 2 ^ (q + (q + (r + 1))) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (3 * q) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = 8 ^ q := by rw [pow_mul]; norm_num
      _ ≤ _ := Nat.pow_le_pow_left (by omega) q
  have hfac : (r + 1).factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have hp := Nat.mul_le_mul hfac hprod
  have hs : (4 * q) ^ q ≤ ((4 * q) ^ q) ^ 2 := Nat.le_self_pow two_ne_zero _
  have hbase : 1 ≤ (4 * q) ^ q := Nat.one_le_pow _ _ (by omega)
  have h1 : 1 ≤ ((4 * q) ^ q) ^ 2 := Nat.one_le_pow _ _ hbase
  calc
    _ ≤ 6 * ((4 * q) ^ q) ^ 2 := by nlinarith only [hK, hp, hs, h1]
    _ ≤ (4 * q) ^ 1 * ((4 * q) ^ q) ^ 2 :=
      Nat.mul_le_mul_right _ (by simp only [pow_one]; omega)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; omega

theorem decoder_augmentation_density_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {C : ℝ} (hC : 0 ≤ C) (hCb : C ≤ (4 * q : ℝ) ^ (6 * q)) :
    (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) *
        (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ≤
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hK : (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) : ℝ) ≤
      (4 * q : ℝ) ^ (2 * q + 1) := by
    exact_mod_cast decoder_augmentation_coefficient_bound hqr
  have hc : (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) : ℝ) * C ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    calc
      _ ≤ (4 * q : ℝ) ^ (2 * q + 1) * (4 * q : ℝ) ^ (6 * q) :=
        mul_le_mul hK hCb hC (by positivity)
      _ = (4 * q : ℝ) ^ (8 * q + 1) := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := by
        have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 8 * q + 1)
          (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
        convert hh using 1
        congr 1
        ring
  calc
    _ = ((1 + q.choose (r + 1) *
        (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) * C) *
          (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) := by ring
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) *
        (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem augment_with_local_decoders_at_exponent {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {C s : ℝ} (hC : 1 ≤ C) (hCb : C ≤ (4 * q : ℝ) ^ (24 * q))
    (hs : paperAlpha q (r + 1) / 3 ≤ s) (hshalf : s ≤ 1 / 2)
    (F : Finset (Block (Fin n) q)) (hF : IsCliqueFamilyBounded r F (C * (n : ℝ) ^ (-s))) :
    ∃ D : Finset (Block (Fin n) q), F ⊆ D ∧
      IsCliqueFamilyBounded r D
        ((1 + q.choose (r + 1) *
          (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) *
            (C * (n : ℝ) ^ (-s))) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ,
        (∀ e, e ∉ cliqueSupport (r + 1) F → J e = 0) →
        (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J := by
  obtain ⟨D₀, hD₀, _, hD₀b⟩ := exists_bounded_local_decoder_family_at_exponent
    hqr hn hC hCb hs hshalf (cliqueSupport (r + 1) F) hF.support_graphBounded
  refine ⟨F ∪ D₀, subset_union_left, ?_, fun J hJ hdiv => ?_⟩
  · simpa only [add_mul, one_mul] using hF.union hD₀b
  · exact (hD₀.generates_multiples J hJ hdiv).mono subset_union_right

/-- Half the final degree budget remains available for the original source graph. -/
theorem decoder_augmentation_half_density_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {C : ℝ} (hC : 0 ≤ C) (hCb : C ≤ (4 * q : ℝ) ^ (6 * q)) :
    (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) *
        (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ≤
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2 := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hK : (1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) : ℝ) ≤
      (4 * q : ℝ) ^ (2 * q + 1) := by
    exact_mod_cast decoder_augmentation_coefficient_bound hqr
  have hc : 2 * ((1 + q.choose (r + 1) *
      (1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1))) * C) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    calc
      _ ≤ (4 * q : ℝ) ^ 1 *
          ((4 * q : ℝ) ^ (2 * q + 1) * (4 * q : ℝ) ^ (6 * q)) :=
        mul_le_mul (by simp only [pow_one]; linarith only [hq])
          (mul_le_mul hK hCb hC (by positivity)) (by positivity) (by positivity)
      _ = (4 * q : ℝ) ^ (8 * q + 2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ _ := by
        have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 8 * q + 2)
          (t := (1 / 10 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
        simpa only [div_eq_mul_inv, one_mul] using hh
  have hscale := mul_le_mul_of_nonneg_right hc
    (Real.rpow_nonneg hn0.le (-(7 * paperAlpha q (r + 1) / 10)))
  have heq : (n : ℝ) ^ (paperAlpha q (r + 1) / 10) *
      (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)) =
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  rw [heq] at hscale
  linarith only [hscale]

theorem augment_with_local_decoders_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {C : ℝ} (hC : 1 ≤ C) (hCb : C ≤ (4 * q : ℝ) ^ (6 * q))
    (F : Finset (Block (Fin n) q))
    (hF : IsCliqueFamilyBounded r F (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) :
    ∃ D : Finset (Block (Fin n) q), F ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ,
        (∀ e, e ∉ cliqueSupport (r + 1) F → J e = 0) →
        (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J := by
  have hα := paperAlpha_pos hqr
  have hα1 := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hC24 : C ≤ (4 * q : ℝ) ^ (24 * q) := hCb.trans
    (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)) (by omega))
  obtain ⟨D, hFD, hD, hdecode⟩ := augment_with_local_decoders_at_exponent hqr hn hC hC24
    (by linarith only [hα] : paperAlpha q (r + 1) / 3 ≤ 7 * paperAlpha q (r + 1) / 10)
    (by linarith only [hα1] : 7 * paperAlpha q (r + 1) / 10 ≤ 1 / 2) F hF
  exact ⟨D, hFD, hD.mono
    (decoder_augmentation_half_density_paper_threshold hqr hn
      (le_trans zero_le_one hC) hCb), hdecode⟩

end Arxiv2411_18291
