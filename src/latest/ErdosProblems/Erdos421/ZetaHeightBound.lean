import ErdosProblems.Erdos421.ZetaHeightParameters
import ErdosProblems.Erdos421.ZetaTailScale

/-! # An unconditional height-dependent estimate near Re(s) = 1 -/

namespace Erdos421

/-- The free-parameter strip bound with a quadratic truncation point.
Only the short initial polynomial contributes height-dependent growth. -/
theorem riemannZeta_height_scale_bound {u : ℕ} (hu : 0 < u) (R K : ℕ)
    (hK : 2 * R + 4 ≤ K) (hK8 : 8 ≤ K) (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≤ 1)
    (hstrip : 1 - s.re ≤ logarithmicSavingExponent R K / 2)
    (hlo : ((2 ^ ((R + 1) * u) : ℕ) : ℝ) ≤ |s.im|)
    (hhi : |s.im| ≤ ((2 ^ ((R + 1) * (u + 1)) : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤ (u + 1 : ℕ) * (((2 ^ (u + 1) : ℕ) : ℝ)) ^ (1 - s.re) +
      zetaStripConstant R K + 9 := by
  let V := (R + 1) * (u + 1)
  have hV : 0 < V := by dsimp only [V]; positivity
  have hL : 0 < 2 * V := by positivity
  have hJL : u + 1 ≤ 2 * V := by
    have hv : u + 1 ≤ V := by dsimp only [V]; nlinarith
    omega
  have hlow : (((2 ^ (2 * V) : ℕ) : ℝ)) ^ (2 / (K : ℝ)) ≤ |s.im| :=
    (zeta_height_scale_lower_frequency hu hK8 R).trans hlo
  have hhigh : |s.im| ≤ (((2 ^ (u + 1) : ℕ) : ℝ)) ^ (R + 1) := by
    have he : (((2 ^ (u + 1) : ℕ) : ℝ)) ^ (R + 1) =
        ((2 ^ ((R + 1) * (u + 1)) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← pow_mul, Nat.mul_comm (u + 1)]
    rwa [he]
  have hb := riemannZeta_dyadic_strip_bound hJL hL R K hK s hs hs1 hstrip hlow hhigh
  have hδ := logarithmicSavingExponent_le_half R (by omega : 2 ≤ K)
  have hη : 1 - s.re ≤ 1 / 4 := by linarith
  have hhalf : 1 / 2 ≤ s.re := by linarith
  have hweight : (((2 ^ (2 * V) : ℕ) : ℝ)) ^ (1 - s.re) ≤ |s.im| :=
    (zeta_height_scale_pole_weight hu R hη).trans hlo
  have hpole := zeta_pole_term_le_one (by positivity : 0 < 2 ^ (2 * V)) s hweight
  have hN : 0 < 2 ^ (2 * V) - 1 := by
    have h := Nat.one_lt_pow (by omega : 2 * V ≠ 0) (by omega : 1 < 2)
    omega
  have hB : (2 : ℝ) ≤ (2 ^ V : ℕ) := by
    exact_mod_cast (show 2 ≤ 2 ^ V by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 2) hV)
  have htail := zeta_tail_error_le_eight hN hB (quadratic_dyadic_cutoff hV) s hhalf hs1 hhi
  linarith

end Erdos421
