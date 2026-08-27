import Arxiv.Arxiv2411_18291.TypicalityBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Typical graphs at polynomially small density

For `ρ*h + 2*δ < 1`, a sampling probability at least `n^(-ρ)` and a relative
error of order `n^(-δ)` satisfy the explicit finite existence criterion for
all sufficiently large `n`. No informal high-probability assertion is assumed.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem typicality_exp_bound_tendsto (r h : ℕ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun n : ℕ => 2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
      Real.exp (-((n : ℝ) ^ α / 12))) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((r * h : ℕ) / α) (1 / 12) (by norm_num)).comp (tendsto_rpow_atTop hα)
  have hp : Tendsto (fun x : ℝ => x ^ (r * h) * Real.exp (-(x ^ α / 12))) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    dsimp only [Function.comp_def]
    rw [← Real.rpow_mul hx, show α * ((r * h : ℕ) / α) = (r * h : ℕ) by
      field_simp, Real.rpow_natCast]
    congr 2
    ring
  have hn := hp.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, mul_zero, mul_assoc] using hn.const_mul (2 * (h + 2 : ℝ))

theorem rpow_count_scale {x : ℝ} (hx : 0 < x) (ρ δ : ℝ) (h : ℕ) :
    x * (x ^ (-ρ)) ^ h * (x ^ (-δ)) ^ 2 = x ^ (1 - ρ * h - 2 * δ) := by
  have ht : x ^ (-δ * 2) = (x ^ (-δ)) ^ 2 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hx.le (-δ) 2
  calc
    _ = x ^ (1 + (-ρ) * h + (-δ) * 2) := by
      rw [Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one,
        Real.rpow_mul_natCast hx.le (-ρ) h, ht]
    _ = _ := by congr 1; ring

/-- The failure probability is bounded by a polynomial times a decaying exponential. -/
theorem typicalFailureBound_power_le (n r h : ℕ) (hn : 1 ≤ n) (hh : 1 ≤ h)
    (hsize : 2 * (h * r) ≤ n) {ρ δ : ℝ} (hδ : 0 ≤ δ)
    (p : unitInterval) (hp : (n : ℝ) ^ (-ρ) ≤ p) :
    typicalFailureBound n r h p ((n : ℝ) ^ (-δ)) ≤
      2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
        Real.exp (-((n : ℝ) ^ (1 - ρ * h - 2 * δ) / 12)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num) hn1
  have hc := Real.rpow_nonneg (Nat.cast_nonneg n) (-δ)
  have hc1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hδ)
  refine (typicalFailureBound_le n r h hn hh p.property.1 p.property.2 hc hc1 hsize).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 12)
  rw [← rpow_count_scale hn0 ρ δ h]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hp h) hn0.le)
    (sq_nonneg _)

/-- Uniform actual probability bounds at polynomial density and error scales. -/
theorem eventually_typical_failure_probability_power (r h : ℕ) (hh : 1 ≤ h) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hexp : ρ * h + 2 * δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ p : unitInterval, (n : ℝ) ^ (-ρ) ≤ p →
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-δ) * p ∧
          IsTypical (sampleGraph ω) ((4 + 2 * h * 2 ^ h) * (n : ℝ) ^ (-δ)) h)} ≤
        2 * (h + 2 : ℝ) * (n : ℝ) ^ (r * h) *
          Real.exp (-((n : ℝ) ^ (1 - ρ * h - 2 * δ) / 12)) := by
  have hδ1 : δ < 1 := by nlinarith [mul_nonneg hρ (Nat.cast_nonneg h)]
  have hclim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-δ) * h * 2 ^ h) atTop (𝓝 0) := by
    have ht := ((tendsto_rpow_neg_atTop hδ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).mul_const (h : ℝ) |>.mul_const ((2 : ℝ) ^ h)
    simpa only [Function.comp_def, zero_mul] using ht
  have hgrowth := (tendsto_rpow_atTop (by linarith : 0 < 1 - δ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmall := hclim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlarge := hgrowth.eventually (eventually_ge_atTop (h * r : ℝ))
  filter_upwards [eventually_ge_atTop (max 1 (max (r + 1) (2 * (h * r)))),
    hsmall, hlarge] with n hn hcn hln
  intro p hp
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnr : r + 1 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hsize : 2 * (h * r) ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hc := Real.rpow_nonneg (Nat.cast_nonneg n) (-δ)
  have hc1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn1 : (1 : ℝ) ≤ n) (by linarith : -δ ≤ 0)
  have hs : (h * r : ℝ) ≤ (n : ℝ) ^ (-δ) * n := by
    have he : (n : ℝ) ^ (1 - δ) = (n : ℝ) ^ (-δ) * n := by
      rw [show 1 - δ = -δ + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
    simpa only [Function.comp_def, he] using hln
  have hb := typical_failure_probability (V := Fin n) p hc hc1
    (by simpa only [Fintype.card_fin] using hnr)
    (by simpa only [Fintype.card_fin] using hs) hcn.le
  simp only [Fintype.card_fin] at hb
  exact hb.trans (typicalFailureBound_power_le n r h hn1 hh hsize hδ.le p hp)

/-- Typical sparse graphs exist for all sufficiently large sizes. The
hypotheses concern only fixed exponents, not any unproved construction. -/
theorem eventually_exists_typicalGraph (r h : ℕ) (hh : 1 ≤ h) {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ) (hexp : ρ * h + 2 * δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ p : unitInterval, (n : ℝ) ^ (-ρ) ≤ p →
      ∃ G : Hypergraph (Fin n) (r + 1),
        |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-δ) * p ∧
        IsTypical G ((4 + 2 * h * 2 ^ h) * (n : ℝ) ^ (-δ)) h := by
  have hα : 0 < 1 - ρ * h - 2 * δ := by linarith
  filter_upwards [eventually_typical_failure_probability_power r h hh hρ hδ hexp,
    (typicality_exp_bound_tendsto r h hα).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hbound hsmall
  intro p hp
  have hb := hbound p hp
  by_contra hnone
  have hbad : {ω : BernoulliSubset.Sample (Block (Fin n) (r + 1)) |
      ¬ (|density (sampleGraph ω) - (p : ℝ)| ≤ (n : ℝ) ^ (-δ) * p ∧
        IsTypical (sampleGraph ω) ((4 + 2 * h * 2 ^ h) * (n : ℝ) ^ (-δ)) h)} = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro ω hω
    exact hnone ⟨sampleGraph ω, hω⟩
  rw [hbad, MeasureTheory.probReal_univ] at hb
  exact (not_lt_of_ge hb) hsmall

/-- The density and error scales in Lemma 5.3, with an eventual size threshold.
The explicit probability estimates above replace the paper's `whp` shorthand. -/
theorem eventually_exists_typicalGraph_paper_parameters (r h : ℕ) (hh : 1 ≤ h) :
    ∀ᶠ n : ℕ in atTop, ∀ p : unitInterval, (n : ℝ) ^ (-(1 / (2 * h : ℝ))) ≤ p →
      ∃ G : Hypergraph (Fin n) (r + 1),
        |density G - (p : ℝ)| ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) * p ∧
        IsTypical G ((n : ℝ) ^ (-(1 / 10 : ℝ))) h := by
  have hhpos : (0 : ℝ) < h := by exact_mod_cast hh
  have hρ : (0 : ℝ) ≤ 1 / (2 * h) := by positivity
  have heq : (1 / (2 * h : ℝ)) * h = 1 / 2 := by field_simp
  have hexp : (1 / (2 * h : ℝ)) * h + 2 * (1 / 5 : ℝ) < 1 := by
    rw [heq]
    norm_num
  have hgen := eventually_exists_typicalGraph r h hh hρ (by norm_num : (0 : ℝ) < 1 / 5) hexp
  have hK := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop (4 + 2 * h * 2 ^ h : ℝ))
  filter_upwards [hgen, hK, eventually_ge_atTop (1 : ℕ)] with n hgn hKn hn
  intro p hp
  obtain ⟨G, hd, hT⟩ := hgn p hp
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have herror : (4 + 2 * h * 2 ^ h : ℝ) * (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) := by
    calc
      _ ≤ (n : ℝ) ^ (1 / 10 : ℝ) * (n : ℝ) ^ (-(1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_right hKn (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = _ := by rw [← Real.rpow_add hnpos]; norm_num
  have hc : (n : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (n : ℝ) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  exact ⟨G, hd.trans (mul_le_mul_of_nonneg_right hc p.property.1), hT.mono herror le_rfl⟩

end Arxiv2411_18291
