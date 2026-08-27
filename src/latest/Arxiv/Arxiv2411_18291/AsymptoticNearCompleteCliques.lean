import Arxiv.Arxiv2411_18291.NearCompleteCliqueCounts
import Arxiv.Arxiv2411_18291.ColourProbabilityNumerics

/-!
# Uniform clique counts when the complement has polynomially small degree

For every fixed `0 < κ < min(δ,1)`, a complement bounded by `n^(-δ)`
gives relative rooted-clique count error at most `n^(-κ)`, for all
sufficiently large ambient sizes. This includes the decoding-set counts.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_rootedClique_count_of_bounded_complement (q r a : ℕ) (haq : a ≤ q)
    {κ δ : ℝ} (hκ : 0 < κ) (hκδ : κ < δ) (hκ1 : κ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ G : Hypergraph (Fin n) (r + 1),
      IsGraphBounded (complete (Fin n) (r + 1) \ G) ((n : ℝ) ^ (-δ)) →
      ∀ I : Block (Fin n) a,
        |((rootedCliques G I q).card : ℝ) - (n : ℝ) ^ (q - a) / (q - a).factorial| ≤
          (n : ℝ) ^ (-κ) * ((n : ℝ) ^ (q - a) / (q - a).factorial) := by
  filter_upwards [eventually_const_mul_rpow_le (2 * (q + 1 : ℝ) * q)
      (β := 1) (κ := κ) hκ1,
    eventually_const_mul_rpow_le (2 * (q + 1 : ℝ) * q.choose r) hκδ,
    eventually_ge_atTop (1 : ℕ)] with n hlinear hpower hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hθ : 0 ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg hnpos.le _
  have hε : 0 ≤ (n : ℝ) ^ (-κ) := Real.rpow_nonneg hnpos.le _
  have hε1 : (n : ℝ) ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast hn) (neg_nonpos.mpr hκ.le)
  have hl := mul_le_mul_of_nonneg_right hlinear hnpos.le
  simp only [Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ hnpos.ne', mul_one] at hl
  have hp := mul_le_mul_of_nonneg_right hpower hnpos.le
  let M : ℝ := q + (q.choose r : ℝ) * (n : ℝ) ^ (-δ) * n
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hmajor : (q + 1 : ℝ) * M ≤ (n : ℝ) ^ (-κ) * n := by
    dsimp only [M]
    nlinarith only [hl, hp]
  have hsize : M ≤ (n : ℝ) := by
    have hq : (1 : ℝ) ≤ q + 1 := le_add_of_nonneg_left (Nat.cast_nonneg q)
    have hh := mul_le_mul_of_nonneg_right hq hM
    have he := mul_le_mul_of_nonneg_right hε1 hnpos.le
    nlinarith only [hh, hmajor, he]
  have herror : ((q - a : ℕ) : ℝ) * M ≤ (n : ℝ) ^ (-κ) * n := by
    have hqa : ((q - a : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q a
    exact (mul_le_mul_of_nonneg_right
      (hqa.trans (show (q : ℝ) ≤ q + 1 by linarith)) hM).trans hmajor
  intro G hG I
  simpa only [Fintype.card_fin] using rootedCliques_relative_error_of_complement_bounded
    hG hθ hε I haq (by simpa only [Fintype.card_fin] using hsize)
      (by simpa only [Fintype.card_fin] using herror)

end Arxiv2411_18291
