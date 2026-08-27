import Arxiv.Arxiv2411_18291.AsymptoticNearCompleteCliques

/-! # Rooted clique counts with a fixed complement bound -/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

/-- A fixed complement density gives any fixed relative error above the
explicit extension loss, uniformly for all sufficiently large vertex sets. -/
theorem eventually_rootedClique_count_of_constant_complement (q r a : ℕ) (haq : a ≤ q)
    {θ ε : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hmargin : (q + 1 : ℝ) * (q.choose r : ℝ) * θ < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) θ →
      ∀ I : Block (Fin n) a,
        |((rootedCliques G I q).card : ℝ) - (n : ℝ) ^ (q - a) / (q - a).factorial| ≤
          ε * ((n : ℝ) ^ (q - a) / (q - a).factorial) := by
  let C : ℝ := (q + 1 : ℝ) * (q.choose r : ℝ) * θ
  have hgap : 0 < ε - C := sub_pos.mpr hmargin
  have hlarge := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop ((q + 1 : ℝ) * q / (ε - C)))
  filter_upwards [hlarge] with n hn
  have hlinear : (q + 1 : ℝ) * q ≤ (ε - C) * n := by
    have hh := (div_le_iff₀ hgap).mp hn
    simpa only [mul_comm] using hh
  let M : ℝ := q + (q.choose r : ℝ) * θ * n
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hmajor : (q + 1 : ℝ) * M ≤ ε * n := by
    dsimp only [M, C] at *
    nlinarith only [hlinear]
  have hsize : M ≤ (n : ℝ) := by
    have hq : (1 : ℝ) ≤ q + 1 := le_add_of_nonneg_left (Nat.cast_nonneg q)
    have hh := mul_le_mul_of_nonneg_right hq hM
    have he := mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith only [hh, hmajor, he]
  have herror : ((q - a : ℕ) : ℝ) * M ≤ ε * n := by
    have hqa : ((q - a : ℕ) : ℝ) ≤ q + 1 := by exact_mod_cast (by omega : q - a ≤ q + 1)
    exact (mul_le_mul_of_nonneg_right hqa hM).trans hmajor
  intro G hG I
  simpa only [Fintype.card_fin] using rootedCliques_relative_error_of_complement_bounded
    hG hθ hε.le I haq (by simpa only [Fintype.card_fin] using hsize)
      (by simpa only [Fintype.card_fin] using herror)

end Arxiv2411_18291
