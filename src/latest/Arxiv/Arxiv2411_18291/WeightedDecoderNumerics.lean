import Arxiv.Arxiv2411_18291.WeightedDecoderTail
import Arxiv.Arxiv2411_18291.FlexibleDecoderPlacement

/-! # Finite weighted decoder parameters and capacity density

Input density `n^(-3*alpha/5)` and deviation `n^(alpha/10)` yield decoder
capacities bounded at density `n^(-2*alpha/5)` at the printed threshold.
Both legal-choice and simultaneous-failure conditions are discharged.
-/

noncomputable section

namespace Arxiv2411_18291

def weightedDecoderCoefficient (q r : ℕ) : ℕ :=
  (2 ^ q * (r + 1).factorial) *
    (1 + (q + 1).choose (q - r) * (q + (r + 1)).choose (r + 1) *
      (8 * (r + 1).factorial))

theorem weightedDecoderCoefficient_le {q r : ℕ} (hqr : r + 1 < q) :
    weightedDecoderCoefficient q r ≤ (4 * q) ^ (9 * q) := by
  have hq : 2 ≤ q := by omega
  have hb : 1 ≤ 4 * q := by omega
  have hf : (r + 1).factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have h2 : 2 ^ q ≤ (4 * q) ^ q := Nat.pow_le_pow_left (by omega) q
  have hJ : (q + 1).choose (q - r) ≤ (4 * q) ^ (q + 1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_left (by omega) _)
  have hK : (q + (r + 1)).choose (r + 1) ≤ (4 * q) ^ (2 * q) :=
    (small_clique_pattern_bounds_sharp hq (by omega : q + (r + 1) ≤ 2 * q)).2
  have h8f : 8 * (r + 1).factorial ≤ (4 * q) ^ (q + 1) := by
    rw [pow_succ]
    nlinarith only [hf, show 8 ≤ 4 * q by omega]
  have hinner : (q + 1).choose (q - r) * (q + (r + 1)).choose (r + 1) *
      (8 * (r + 1).factorial) ≤ (4 * q) ^ (4 * q + 2) := by
    calc
      _ ≤ (4 * q) ^ (q + 1) * (4 * q) ^ (2 * q) * (4 * q) ^ (q + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hJ hK) h8f
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hsum : 1 + (q + 1).choose (q - r) * (q + (r + 1)).choose (r + 1) *
      (8 * (r + 1).factorial) ≤ (4 * q) ^ (4 * q + 3) := by
    have hp : 1 ≤ (4 * q) ^ (4 * q + 2) := one_le_pow₀ hb
    rw [show 4 * q + 3 = (4 * q + 2) + 1 by omega, pow_succ]
    nlinarith only [hinner, hp, show 2 ≤ 4 * q by omega]
  calc
    _ ≤ ((4 * q) ^ q * (4 * q) ^ q) * (4 * q) ^ (4 * q + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul h2 hf) hsum
    _ = (4 * q) ^ (6 * q + 3) := by rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ _ := Nat.pow_le_pow_right hb (by omega)

theorem weightedDecoderCoefficient_graph_le (q r : ℕ) :
    1 + (q + (r + 1)).choose (r + 1) * (8 * (r + 1).factorial) ≤
      weightedDecoderCoefficient q r := by
  have hJ : 1 ≤ (q + 1).choose (q - r) := Nat.choose_pos (by omega)
  have hC : 1 ≤ 2 ^ q * (r + 1).factorial := Nat.succ_le_of_lt (by positivity)
  have hh := Nat.mul_le_mul_right
    ((q + (r + 1)).choose (r + 1) * (8 * (r + 1).factorial)) hJ
  unfold weightedDecoderCoefficient
  apply le_trans _ (le_mul_of_one_le_left (Nat.zero_le _) hC)
  nlinarith only [hh]

theorem weighted_decoder_scales {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let α := paperAlpha q (r + 1)
    let θ := (n : ℝ) ^ (-(3 * α / 5))
    let c := (n : ℝ) ^ (α / 10)
    let η := (n : ℝ) ^ (-(α / 2))
    θ ≤ η ∧ 1 ≤ θ * n ∧ 1 ≤ c ∧
      (1 + c) * (2 * (r + 1).factorial * (θ + θ)) ≤ 8 * (r + 1).factorial * η := by
  dsimp only
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hc : 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) :=
    Real.one_le_rpow hn1 (by positivity)
  refine ⟨Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα]), ?_, hc, ?_⟩
  · rw [← Real.rpow_add_one hn0.ne']
    exact Real.one_le_rpow hn1 (by linarith only [hαmax])
  · have hprod : (n : ℝ) ^ (paperAlpha q (r + 1) / 10) *
        (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) =
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    calc
      _ ≤ (2 * (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) *
          (2 * (r + 1).factorial * ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) +
            (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :=
        mul_le_mul_of_nonneg_right (by linarith only [hc]) (by positivity)
      _ = _ := by rw [← hprod]; ring

theorem weighted_decoder_finite_conditions {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let α := paperAlpha q (r + 1)
    let θ := (n : ℝ) ^ (-(3 * α / 5))
    let c := (n : ℝ) ^ (α / 10)
    let L := (1 + c) * (2 * (r + 1).factorial * (θ + θ))
    let K := (q + (r + 1)).choose (r + 1)
    0 < n ∧ 4 * (q + (r + 1)) ^ 2 ≤ n ∧
      (K : ℝ) * (θ + K * L) ≤ 1 / 4 ∧
      (K : ℝ) * n.choose r *
        Real.exp (-(2 * (r + 1).factorial * (θ + θ) * n * c ^ 2 /
          ((2 + c) * (1 + θ * n)))) < 1 := by
  dsimp only
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  obtain ⟨hw, hK⟩ := small_clique_pattern_bounds_sharp (r := r + 1)
    (by omega : 2 ≤ q) (by omega : q + (r + 1) ≤ 2 * q)
  obtain ⟨hn0, hsize, _, hsmall, _⟩ := small_pattern_separated_greedy_numerics hqr hn hw hK
    (d := 0) (Nat.zero_le _) (A := 1) le_rfl
    (one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)))
    (ρ := paperAlpha q (r + 1) / 2) (by linarith only [hα])
    (by linarith only [hαmax])
  simp only [one_mul] at hsmall
  obtain ⟨hθη, hθn, hc, hL⟩ := weighted_decoder_scales hqr hn
  refine ⟨hn0, hsize, ?_, ?_⟩
  · apply le_trans _ hsmall
    gcongr
  · have hM : (q + (r + 1)).choose (r + 1) ≤ n := hK.trans
      ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
        ((boost_threshold_le_paper_threshold hqr).trans hn))
    have hexp := weighted_decoder_exponent_lower (r := r) hθn hc
    apply lt_of_le_of_lt _ (weighted_decoder_polynomial_tail hqr hn hM)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (neg_le_neg hexp)

theorem weighted_decoder_output_density {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let α := paperAlpha q (r + 1)
    let θ := (n : ℝ) ^ (-(3 * α / 5))
    let c := (n : ℝ) ^ (α / 10)
    let L := (1 + c) * (2 * (r + 1).factorial * (θ + θ))
    let K := (q + (r + 1)).choose (r + 1)
    θ + K * L ≤ (n : ℝ) ^ (-(2 * α / 5)) ∧
      (2 ^ q * (r + 1).factorial : ℕ) * (θ + (q + 1).choose (q - r) * (K * L)) ≤
        (n : ℝ) ^ (-(2 * α / 5)) := by
  dsimp only
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  obtain ⟨hθη, _, _, hL⟩ := weighted_decoder_scales hqr hn
  have hcoef : (weightedDecoderCoefficient q r : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
    have hh := paper_threshold_alpha_rpow_lower (s := 9 * q) hqr hn
      (by norm_num : (0 : ℝ) ≤ 1 / 10) (by push_cast; linarith)
    have hc : (weightedDecoderCoefficient q r : ℝ) ≤ (4 * q : ℝ) ^ (9 * q) := by
      exact_mod_cast weightedDecoderCoefficient_le hqr
    exact hc.trans (by simpa only [div_eq_mul_inv, one_mul] using hh)
  have hprod : (weightedDecoderCoefficient q r : ℝ) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) ≤
        (n : ℝ) ^ (-(2 * paperAlpha q (r + 1) / 5)) := by
    calc
      _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10) *
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring
  constructor
  · apply le_trans _ hprod
    have hc : (1 + (q + (r + 1)).choose (r + 1) * (8 * (r + 1).factorial) : ℝ) ≤
        weightedDecoderCoefficient q r := by
      exact_mod_cast weightedDecoderCoefficient_graph_le q r
    calc
      _ ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) +
          (q + (r + 1)).choose (r + 1) *
            (8 * (r + 1).factorial * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) := by
        gcongr
      _ = (1 + (q + (r + 1)).choose (r + 1) * (8 * (r + 1).factorial)) *
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  · apply le_trans _ hprod
    calc
      _ ≤ (2 ^ q * (r + 1).factorial : ℕ) *
          ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)) + (q + 1).choose (q - r) *
            ((q + (r + 1)).choose (r + 1) *
              (8 * (r + 1).factorial * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))) := by
        gcongr
      _ = _ := by
        simp only [weightedDecoderCoefficient, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Nat.cast_ofNat]
        ring

end Arxiv2411_18291
