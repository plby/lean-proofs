import Arxiv.Arxiv2411_18291.AsymptoticTypicality
import Arxiv.Arxiv2411_18291.FiniteCliqueSamplingNumerics

/-!
# Simultaneous sampling succeeds at every relative exponent below one half

The common edge mean has scale `n^m/(2*m!)` with `m≥1`. For relative
error `n^(-κ)`, `κ<1/2`, the Chernoff exponent dominates a positive power
of n, so the union bound over all possible graph edges tends to zero.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem eventually_clique_sampling_failure_lt_one (r m : ℕ) (hm : 1 ≤ m)
    {κ : ℝ} (hκ : 0 ≤ κ) (hκhalf : κ < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, (n.choose r : ℝ) *
      (2 * Real.exp (-((((n : ℝ) ^ m / m.factorial) / 2) *
        ((n : ℝ) ^ (-κ)) ^ 2 / (2 * (1 + 2 * (n : ℝ) ^ (-κ)))))) < 1 := by
  let α : ℝ := (1 - 2 * κ) / 2
  have hα : 0 < α := by dsimp only [α]; linarith only [hκhalf]
  have hgrowth := (tendsto_rpow_atTop hα).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [(typicality_exp_bound_tendsto r 1 hα).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hgrowth.eventually (eventually_ge_atTop (m.factorial : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with n hfail hlarge hn
  have hfail' : 6 * (n : ℝ) ^ r * Real.exp (-((n : ℝ) ^ α / 12)) < 1 := by
    norm_num only [Nat.mul_one, Nat.cast_one] at hfail
    exact hfail
  apply clique_sampling_failure_of_scalar_bounds r m n hκ hn hlarge ?_ hfail'
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  dsimp only [α]
  linarith only [hm']

end Arxiv2411_18291
