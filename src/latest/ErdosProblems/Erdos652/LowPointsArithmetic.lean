import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped Real

namespace Erdos652

lemma low_points_contradiction_arithmetic
    {ε C k n q t : ℝ}
    (hε : 0 < ε) (hC : 0 < C) (hk : 0 < k) (hn : 0 < n)
    (hq : n / 2 ≤ q)
    (hK : 2 * C ^ 2 / ε ^ 2 < k)
    (hlower : ε * Real.sqrt (k * q) ≤ t)
    (hupper : t < C * Real.sqrt n) : False := by
  have hkq : 0 ≤ k * q := by
    have hq0 : 0 ≤ q := le_trans (by positivity : 0 ≤ n / 2) hq
    positivity
  have hsqrtN : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
  have hsqrtKQ : (Real.sqrt (k * q)) ^ 2 = k * q := Real.sq_sqrt hkq
  have hstrict : ε * Real.sqrt (k * q) < C * Real.sqrt n :=
    hlower.trans_lt hupper
  have hleft0 : 0 ≤ ε * Real.sqrt (k * q) := by positivity
  have hright0 : 0 ≤ C * Real.sqrt n := by positivity
  have hsquare := (sq_lt_sq₀ hleft0 hright0).mpr hstrict
  rw [mul_pow, hsqrtKQ, mul_pow, hsqrtN] at hsquare
  have hcompare : ε ^ 2 * (k * (n / 2)) ≤ ε ^ 2 * (k * q) := by
    gcongr
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hscaled : (ε ^ 2 * k / 2) * n < C ^ 2 * n := by
    calc
      (ε ^ 2 * k / 2) * n = ε ^ 2 * (k * (n / 2)) := by ring
      _ ≤ ε ^ 2 * (k * q) := hcompare
      _ < C ^ 2 * n := by simpa [mul_assoc] using hsquare
  have hkSmall : ε ^ 2 * k < 2 * C ^ 2 := by
    have hhalf : ε ^ 2 * k / 2 < C ^ 2 :=
      lt_of_mul_lt_mul_right hscaled hn.le
    linarith
  have hkLarge : 2 * C ^ 2 < ε ^ 2 * k := by
    have := (div_lt_iff₀ hεsq).mp hK
    simpa [mul_comm] using this
  linarith

end Erdos652
