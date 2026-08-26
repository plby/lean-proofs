import ErdosProblems.Erdos76.SingleColorRounding

/-!
# Haxell–Rödl transference for triangle packings

Capped LP duality and triangle removal smooth an arbitrary fractional packing.
The proved weighted hypergraph matching theorem then rounds the small weights.
-/

open Finset Filter
open scoped BigOperators

namespace Erdos76

attribute [local instance] Classical.propDecidable

private lemma cover_scaling_error {α q s : ℝ}
    (hα : 0 ≤ α) (hα₂ : α ≤ 1 / 2) (hs : 0 ≤ s) (hqs : q ≤ s) :
    q / (1 - α) ≤ q + 2 * α * s := by
  have hd : 0 < 1 - α := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hqs hα
  have h₂ : α * s ≤ 2 * α * s * (1 - α) := by
    have hfactor : (1 : ℝ) ≤ 2 * (1 - α) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hfactor (mul_nonneg hα hs)
    nlinarith
  apply (div_le_iff₀ hd).mpr
  nlinarith

/-- Uniform arbitrary-weight Haxell–Rödl rounding for triangles, with all
linear-programming and probabilistic ingredients proved in Lean. -/
theorem haxellRodlRounding : HaxellRodlRounding := by
  intro η hη
  let α : ℝ := min (η / 8) (1 / 4)
  have hα : 0 < α := by dsimp [α]; positivity
  have hα₁ : α < 1 := by have := min_le_right (η / 8) (1 / 4 : ℝ); dsimp [α]; linarith
  have hα₂ : α ≤ 1 / 2 := by have := min_le_right (η / 8) (1 / 4 : ℝ); dsimp [α]; linarith
  have hαη : α ≤ η / 8 := min_le_left _ _
  obtain ⟨θ, hθ, hrepair⟩ := CoverRepair.exists_uniform_cover_repair α (η / 4) hα hα₁ (by positivity)
  obtain ⟨δ, hδ, hround⟩ := SingleColorRounding.small_weight_rounding (η / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (4 / (α * θ * δ)))
  filter_upwards [eventually_ge_atTop N] with n hn
  intro G u hu
  have hnr : max 1 (4 / (α * θ * δ)) < (n : ℝ) := hN.trans_le (by exact_mod_cast hn)
  have hnpos : (0 : ℝ) < n := by have := (le_max_left _ _).trans_lt hnr; linarith
  have hnlarge : 4 / (α * θ * δ) < (n : ℝ) := (le_max_right _ _).trans_lt hnr
  let μ : ℝ := 4 / (α * θ * (n : ℝ))
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμδ : μ ≤ δ := by
    dsimp [μ]
    apply (div_le_iff₀ (by positivity : 0 < α * θ * (n : ℝ))).mpr
    have h := (div_lt_iff₀ (by positivity : 0 < α * θ * δ)).mp hnlarge
    nlinarith
  obtain ⟨w, z, r, hw, hcap, hz, hr, hcover, heq⟩ := CappedGraph.exists_capped_graph_pair G μ hμ
  have hsize : fractionalSize G w ≤ (n : ℝ) ^ 2 := by
    simpa only [Fintype.card_fin] using CappedGraph.fractionalSize_le_card_sq hw
  have hzsum : 0 ≤ ∑ e ∈ G.edgeFinset, z e := sum_nonneg hz
  have hrsum : 0 ≤ fractionalSize G r := sum_nonneg hr
  have hzle : (∑ e ∈ G.edgeFinset, z e) ≤ fractionalSize G w := by
    have := mul_nonneg hμ.le hrsum
    linarith
  have hrle : μ * fractionalSize G r ≤ (n : ℝ) ^ 2 := by linarith
  have hdef := CappedGraph.defect_card_bound hr hcover (α / 2)
  have hdefmul : μ * (α / 2) * (CoverRepair.badTriangles G z (α / 2)).card ≤ (n : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hdef hμ.le
    nlinarith
  have hidentity : μ * (α / 2) * (θ * (n : ℝ) ^ 3) = 2 * (n : ℝ) ^ 2 := by
    dsimp [μ]
    field_simp
    ring
  have hbad : ((CoverRepair.badTriangles G z (α / 2)).card : ℝ) < θ * (n : ℝ) ^ 3 := by
    by_contra! hnot
    have hcoef : 0 ≤ μ * (α / 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hnot hcoef
    rw [hidentity] at hmul
    nlinarith [sq_pos_of_pos hnpos]
  obtain ⟨z', hz', hcost⟩ := hrepair (Fin n) G z hz (by simpa only [Fintype.card_fin] using hbad)
  simp only [Fintype.card_fin] at hcost
  have hucover := LPDuality.fractionalSize_le_edgeCover_sum G u z' hu hz'
  have hscale := cover_scaling_error hα.le hα₂ (sq_nonneg (n : ℝ)) (hzle.trans hsize)
  have hαerr : 2 * α * (n : ℝ) ^ 2 ≤ η / 4 * (n : ℝ) ^ 2 := by
    have hfactor : 2 * α ≤ η / 4 := by linarith
    exact mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
  have happrox : fractionalSize G u ≤ fractionalSize G w + η / 2 * (n : ℝ) ^ 2 := by
    linarith
  obtain ⟨P, hP, hdis, hPsize⟩ := hround (Fin n) G w hw (fun t ht ↦ (hcap t ht).trans hμδ)
  simp only [Fintype.card_fin] at hPsize
  refine ⟨P, hP, hdis, ?_⟩
  linarith

end Erdos76
