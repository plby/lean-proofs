import Arxiv.Arxiv2411_18291.AsymptoticTypicality

/-!
# Typical graphs with a prescribed density scale

An intermediate, slightly smaller error absorbs the fixed constant
in the random typicality estimate. The resulting graph has typicality error
exactly `n^(-δ)` and density within that relative error of `n^(-α)`.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_exists_typicalGraph_density_scale (r h : ℕ) (hh : 1 ≤ h)
    {α δ : ℝ} (hα : 0 ≤ α) (hδ : 0 < δ) (hgap : α * h + 2 * δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h ∧
      |density K - (n : ℝ) ^ (-α)| ≤ (n : ℝ) ^ (-δ) * (n : ℝ) ^ (-α) ∧
      (1 / 2 : ℝ) * (n : ℝ) ^ (-α) ≤ density K ∧
      density K ≤ 2 * (n : ℝ) ^ (-α) := by
  let δ' := δ + (1 - α * h - 2 * δ) / 4
  have hδδ' : δ < δ' := by dsimp [δ']; linarith
  have hδ' : 0 < δ' := hδ.trans hδδ'
  have hgap' : α * h + 2 * δ' < 1 := by dsimp [δ']; linarith
  have hgen := eventually_exists_typicalGraph r h hh hα hδ' hgap'
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < δ' - δ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (4 + 2 * h * 2 ^ h : ℝ))
  have hsmall := ((tendsto_rpow_neg_atTop hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hgen, hlarge, hsmall, eventually_ge_atTop (1 : ℕ)] with n hgn hln hsn hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 := Real.rpow_nonneg hnpos.le (-α)
  have hp1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hα)
  let p : unitInterval := ⟨(n : ℝ) ^ (-α), hp0, hp1⟩
  obtain ⟨K, hd, hT⟩ := hgn p le_rfl
  have hTerror : (4 + 2 * h * 2 ^ h : ℝ) * (n : ℝ) ^ (-δ') ≤
      (n : ℝ) ^ (-δ) := by
    calc
      _ ≤ (n : ℝ) ^ (δ' - δ) * (n : ℝ) ^ (-δ') :=
        mul_le_mul_of_nonneg_right hln (Real.rpow_nonneg hnpos.le _)
      _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; ring
  have hc : (n : ℝ) ^ (-δ') ≤ (n : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hδδ'.le)
  have hd' : |density K - (n : ℝ) ^ (-α)| ≤
      (n : ℝ) ^ (-δ) * (n : ℝ) ^ (-α) :=
    hd.trans (mul_le_mul_of_nonneg_right hc hp0)
  have hsmall' : (n : ℝ) ^ (-δ) ≤ 1 / 2 := hsn.le
  have hhalf := hd'.trans (mul_le_mul_of_nonneg_right hsmall' hp0)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hhalf
  refine ⟨K, hT.mono hTerror le_rfl, hd', ?_, ?_⟩ <;> linarith

end Arxiv2411_18291
