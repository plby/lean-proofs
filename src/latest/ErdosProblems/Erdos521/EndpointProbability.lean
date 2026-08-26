/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Power decay of maximal root-count events at the logarithmic endpoint scale.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.EndpointTerms

namespace Erdos521

open MeasureTheory Filter

theorem eventually_endpoint_probability_bound {a b d τ p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hd₁ : d < 1 / 2)
    (hpd : p ≤ d / 2) (hpa : p ≤ 2 * a - 2 * d)
    (hgap : 4 * max (4 * b - a) 0 + 2 * d + p < τ * Real.log 4) :
    ∀ᶠ n : ℕ in atTop,
      sequenceLaw.real {ε | ∃ m, n ≤ m ∧ m ≤ 2 * n ∧
        endpointThreshold τ n ≤ localRootCount ε m (endpointCenter a n) (endpointRadius b n)} ≤
        (4 * Real.exp (1 / 2) + 7) * (n : ℝ) ^ (-p) := by
  let c : ℝ := 1 / (4 * Real.pi ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  filter_upwards [eventually_endpointCenter_bounds ha,
    eventually_endpoint_smallBall_sqrt ha hc hd,
    eventually_endpoint_variance_exp ha hc (-p), eventually_endpoint_cutoff_exp hd₁ (-p),
    eventually_endpoint_boundary_term ha hb.le hgap, eventually_ge_atTop 2]
    with n hx hsqrt hvar hcutoff hboundary hn
  have hnNat : 0 < n := by omega
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hr : 0 < endpointRadius b n := by
    have hlog₀ : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    exact div_pos (mul_pos hb hlog₀) hn₀
  have h := localRootCount_maximal_probability n (2 * n) (endpointThreshold τ n) 0
    (by omega) hx.1 hx.2.le hr (endpointCutoff_pos d hnNat)
  dsimp only at h
  simp only [pow_zero, inv_one, mul_one, show 2 * n - n = n by omega,
    Nat.cast_mul, Nat.cast_ofNat] at h
  have hsqrt' := hsqrt.trans (Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith : -d / 2 ≤ -p))
  have htail := (endpoint_tail_term_le (d := d) ha.le (by omega : 1 ≤ n)
    (by linarith [hx.1]) hx.2.le).trans
      (Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith : -2 * a + 2 * d ≤ -p))
  have hsmall := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hsqrt' hvar) (mul_le_mul_of_nonneg_left hcutoff (by norm_num : (0 : ℝ) ≤ 2)))
    (Real.exp_pos (1 / 2)).le
  apply h.trans
  calc
    _ ≤ Real.exp (1 / 2) * ((n : ℝ) ^ (-p) + (n : ℝ) ^ (-p) + 2 * (n : ℝ) ^ (-p)) +
        (n : ℝ) ^ (-p) + 6 * (n : ℝ) ^ (-p) :=
      add_le_add (add_le_add hsmall htail) hboundary
    _ = _ := by ring

/-- A narrow interval at logarithmic distance from `1` has a maximal root-count
tail that decays as a positive power of the degree. -/
theorem endpoint_local_probability_decay {a b τ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hgeometry : 4 * max (4 * b - a) 0 < τ * Real.log 4) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n : ℕ in atTop,
      sequenceLaw.real {ε | ∃ m, n ≤ m ∧ m ≤ 2 * n ∧
        endpointThreshold τ n ≤ localRootCount ε m (endpointCenter a n) (endpointRadius b n)} ≤
        (4 * Real.exp (1 / 2) + 7) * (n : ℝ) ^ (-p) := by
  let gap := τ * Real.log 4 - 4 * max (4 * b - a) 0
  have hgap : 0 < gap := sub_pos.mpr hgeometry
  let d := min (1 / 4 : ℝ) (min (a / 2) (gap / 8))
  have hd : 0 < d := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hd₁ : d ≤ 1 / 4 := min_le_left _ _
  have hda : d ≤ a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hdgap : d ≤ gap / 8 := (min_le_right _ _).trans (min_le_right _ _)
  let p := min (d / 2) (gap / 4)
  have hp : 0 < p := lt_min (by positivity) (by positivity)
  have hpd : p ≤ d / 2 := min_le_left _ _
  have hpgap : p ≤ gap / 4 := min_le_right _ _
  refine ⟨p, hp, eventually_endpoint_probability_bound ha hb hd (by linarith) hpd (by linarith) ?_⟩
  dsimp [gap] at hgap hdgap hpgap
  linarith

end Erdos521
