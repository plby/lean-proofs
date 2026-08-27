import Arxiv.Arxiv2411_18291.FiniteCliqueSamplingNumerics
import Arxiv.Arxiv2411_18291.ExplicitBoostTail

/-! # Clique sampling succeeds at the explicit Boost size bound -/

namespace Arxiv2411_18291

theorem clique_sampling_failure_explicit {q r m n : ℕ}
    (hq : 2 ≤ q) (hr : r ≤ q) (hmq : m ≤ q) (hm : 1 ≤ m)
    (hn : (4 * q) ^ (90 * q) ≤ n) :
    let c : ℝ := (n : ℝ) ^ (-(2 / 5 : ℝ))
    let μ : ℝ := ((n : ℝ) ^ m / m.factorial) / 2
    (n.choose r : ℝ) * (2 * Real.exp (-(μ * c ^ 2 / (2 * (1 + 2 * c))))) < 1 := by
  dsimp only
  have hn1 : 1 ≤ n := by
    have hh := (boost_threshold_root_size_bounds hq hn).2.2
    omega
  apply clique_sampling_failure_of_scalar_bounds r m n (by norm_num) hn1
    (boost_threshold_factorial_le hq hmq hn) ?_ (boost_sampling_tail_lt_one hq hr hn)
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith only [hm']

end Arxiv2411_18291
