import Arxiv.Arxiv2411_18291.FiniteColourTrials
import Arxiv.Arxiv2411_18291.FiniteNearFrameNumerics
import Arxiv.Arxiv2411_18291.ExchangeCliqueCounts

/-! # Palette space and the union bound over the colours of a base clique -/

noncomputable section

namespace Arxiv2411_18291

def correctedColourPaletteSize (q r m : ℕ) : ℕ := 40 * q ^ 2 * paperInverseAlpha q r * m

theorem colour_palette_room {q k a m f c : ℕ} (hq : 2 ≤ q) (hk : q ≤ k)
    (ha : 1 ≤ a) (hkm : k ≤ m) (hfm : k * f ≤ 2 * m) (hc : 145 ≤ c * q ^ 2) :
    k + 48 * (q + 1) * a * f ≤ c * q ^ 2 * a * m := by
  have hfactor : 48 * (q + 1) ≤ 72 * k := by omega
  have htrial : 48 * (q + 1) * a * f ≤ 144 * a * m := by
    calc
      _ ≤ 72 * k * a * f := Nat.mul_le_mul_right f (Nat.mul_le_mul_right a hfactor)
      _ = 72 * a * (k * f) := by ring
      _ ≤ 72 * a * (2 * m) := Nat.mul_le_mul_left _ hfm
      _ = _ := by ring
  have hka : k ≤ a * m := hkm.trans (by nlinarith only [ha])
  calc
    _ ≤ 145 * a * m := by nlinarith only [htrial, hka]
    _ ≤ _ := Nat.mul_le_mul_right m (Nat.mul_le_mul_right a hc)

theorem paperColourCount_le_correctedColourPaletteSize (q r m : ℕ) :
    paperColourCount q r m ≤ correctedColourPaletteSize q r m := by
  unfold paperColourCount correctedColourPaletteSize
  exact Nat.mul_le_mul_right m (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (by norm_num : 20 ≤ 40)))

theorem paper_colour_palette_room {W : Type*} [Fintype W] [DecidableEq W]
    {q r : ℕ} (hqr : r + 1 < q) (hq : 3 ≤ q) (S : ExchangeSystem W q (r + 1)) :
    q.choose (r + 1) + paperColourTrialCount q (r + 1) S.base.val.card * S.farCliques.card ≤
      paperColourCount q (r + 1) S.graph.card := by
  have hkm : q.choose (r + 1) ≤ S.graph.card := by
    simpa only [card_cliqueEdges] using
      Finset.card_le_card (S.positive_decomposition.clique_subset S.base_mem)
  simpa only [paperColourTrialCount, S.base.property, paperColourCount] using
    colour_palette_room (by omega : 2 ≤ q) (q_le_choose_succ hqr)
      (Nat.succ_le_of_lt (paperInverseAlpha_pos hqr)) hkm S.far_card_mul_le
      (by nlinarith only [hq] : 145 ≤ 20 * q ^ 2)

theorem corrected_colour_palette_room {W : Type*} [Fintype W] [DecidableEq W]
    {q r : ℕ} (hqr : r + 1 < q) (S : ExchangeSystem W q (r + 1)) :
    q.choose (r + 1) + paperColourTrialCount q (r + 1) S.base.val.card * S.farCliques.card ≤
      correctedColourPaletteSize q (r + 1) S.graph.card := by
  have hq : 2 ≤ q := by omega
  have hkm : q.choose (r + 1) ≤ S.graph.card := by
    simpa only [card_cliqueEdges] using
      Finset.card_le_card (S.positive_decomposition.clique_subset S.base_mem)
  simpa only [paperColourTrialCount, S.base.property, correctedColourPaletteSize] using
    colour_palette_room hq (q_le_choose_succ hqr)
      (Nat.succ_le_of_lt (paperInverseAlpha_pos hqr)) hkm S.far_card_mul_le
      (by nlinarith only [hq] : 145 ≤ 40 * q ^ 2)

theorem paperInverseAlpha_le_base_power {q r : ℕ} (hqr : r + 1 < q) :
    paperInverseAlpha q (r + 1) ≤ (4 * q) ^ (4 * q) := by
  have hq : 2 ≤ q := by omega
  have hb : 1 ≤ 4 * q := by omega
  have hp : (2 * q) ^ (r + 1) ≤ (4 * q) ^ q :=
    (Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right hb hqr.le)
  have hk : q.choose (r + 1) ≤ (4 * q) ^ q :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have h6k : 6 * q.choose (r + 1) ≤ (4 * q) ^ (q + 1) := by
    rw [pow_succ]
    nlinarith only [hk, show 6 ≤ 4 * q by omega]
  calc
    _ ≤ (4 * q) ^ q * ((4 * q) ^ (q + 1)) ^ 2 :=
      Nat.mul_le_mul hp (Nat.pow_le_pow_left h6k 2)
    _ = (4 * q) ^ (3 * q + 2) := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right hb (by omega)

theorem choose_le_inverse_alpha {q r : ℕ} (hqr : r < q) :
    q.choose r ≤ paperInverseAlpha q r := by
  have hp : 1 ≤ (2 * q) ^ r := one_le_pow₀ (by omega)
  have hk : 1 ≤ q.choose r := Nat.succ_le_of_lt (Nat.choose_pos hqr.le)
  have hm := Nat.mul_le_mul_right ((6 * q.choose r) ^ 2) hp
  unfold paperInverseAlpha
  nlinarith only [hk, hm]

theorem corrected_colour_palette_size_le_power {q r m : ℕ} (hqr : r + 1 < q)
    (hm : m ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    correctedColourPaletteSize q (r + 1) m ≤ (4 * q) ^ (10 * q) := by
  have hq : 2 ≤ q := by omega
  have hb : 1 ≤ 4 * q := by omega
  have hA := paperInverseAlpha_le_base_power hqr
  have hM := (configuration_lt_inverseAlpha hqr hm).le.trans hA
  have hc : 40 * q ^ 2 ≤ (4 * q) ^ 3 := by nlinarith only [hq]
  calc
    _ ≤ (4 * q) ^ 3 * (4 * q) ^ (4 * q) * (4 * q) ^ (4 * q) :=
      Nat.mul_le_mul (Nat.mul_le_mul hc hA) hM
    _ = (4 * q) ^ (8 * q + 3) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right hb (by omega)

theorem colour_palette_power_le_paper_threshold {q r m u : ℕ} (hqr : r + 1 < q)
    (hm : m ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hu : u ≤ correctedColourPaletteSize q (r + 1) m) :
    u ^ q.choose (r + 1) ≤ paperSizeThreshold q (r + 1) := by
  have hb : 1 ≤ 4 * q := by omega
  have hA := choose_le_inverse_alpha hqr
  calc
    _ ≤ ((4 * q) ^ (10 * q)) ^ q.choose (r + 1) :=
      Nat.pow_le_pow_left (hu.trans (corrected_colour_palette_size_le_power hqr hm)) _
    _ = (4 * q) ^ (10 * q * q.choose (r + 1)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right hb
      (by nlinarith only [Nat.mul_le_mul_left (10 * q) hA])

theorem common_colour_trials_fit_paper_palette {q r m M : ℕ} (hq : 3 ≤ q) (hm : m ≤ M) :
    paperCommonColourTrialCount q r * m ≤ paperColourCount q r M := by
  have hc : 60 * q ≤ 20 * q ^ 2 := by nlinarith only [hq]
  exact Nat.mul_le_mul (Nat.mul_le_mul_right (paperInverseAlpha q r) hc) hm

theorem colour_palette_power_le_cuberoot_paper_threshold {q r m u n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hm : m ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hu : u ≤ correctedColourPaletteSize q (r + 1) m) :
    (u : ℝ) ^ q.choose (r + 1) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnat : u ^ q.choose (r + 1) ≤ (4 * q) ^ (10 * q * q.choose (r + 1)) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (hu.trans (corrected_colour_palette_size_le_power hqr hm)) _
  have hA := choose_le_inverse_alpha hqr
  have hs : 10 * q * q.choose (r + 1) ≤ 30 * q * paperInverseAlpha q (r + 1) := by
    nlinarith only [Nat.mul_le_mul_left (10 * q) hA]
  have hsR : ((10 * q * q.choose (r + 1) : ℕ) : ℝ) ≤
      ((90 * q * paperInverseAlpha q (r + 1) : ℕ) : ℝ) * (1 / 3 : ℝ) := by
    have hh : (10 * q * q.choose (r + 1) : ℝ) ≤ 30 * q * paperInverseAlpha q (r + 1) := by
      exact_mod_cast hs
    push_cast
    nlinarith only [hh]
  have hreal : (u : ℝ) ^ q.choose (r + 1) ≤
      (4 * q : ℝ) ^ (10 * q * q.choose (r + 1)) := by exact_mod_cast hnat
  exact hreal.trans
    (paper_threshold_rpow_lower hqr hn (by norm_num : (0 : ℝ) ≤ 1 / 3) hsR)

theorem four_colour_failures_le_paper_threshold {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    4 * (n : ℝ) ^ (-(5 / 3 : ℝ)) ≤ (n : ℝ) ^ (-1 : ℝ) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hqA : 1 ≤ q * paperInverseAlpha q (r + 1) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by omega) (paperInverseAlpha_pos hqr))
  have hexp : (2 : ℝ) ≤ ((90 * q * paperInverseAlpha q (r + 1) : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith only [Nat.mul_le_mul_left 90 hqA] :
      2 ≤ 90 * q * paperInverseAlpha q (r + 1))
  have hb := paper_threshold_rpow_lower hqr hn (s := 1)
    (by norm_num : (0 : ℝ) ≤ 2 / 3) (by linarith only [hexp])
  have h4 : (4 : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hh : (4 : ℝ) ≤ (4 * q : ℝ) ^ 1 := by
      simp only [pow_one]
      nlinarith only [hq]
    exact hh.trans hb
  calc
    _ ≤ (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(5 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
