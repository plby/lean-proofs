import ErdosProblems.Erdos796.LargeMultiplierPruning
import ErdosProblems.Erdos796.ElementaryPruningErrors

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Negligibility of the two complete-box pruning losses

The first pruning uses the cutoff `Y = L^112`; the second uses
`W = L^20`, where `L = floor(log_2 n) + 1`.  Their dyadic complete-box
majorants are respectively at most `8n/L^25` and `8n/L^2`.  This file also
packages the real estimates as natural ceilings for the final finite bound.
-/

namespace Erdos796

open Filter Topology

namespace BoxPruningError

open PruningScales

/-- The fourth root of a fourth power of a nonnegative real. -/
theorem realFourthRoot_pow_four {x : ℝ} (hx : 0 ≤ x) :
    Tripartite.realFourthRoot (x ^ 4) = x := by
  unfold Tripartite.realFourthRoot
  rw [show x ^ 4 = (x ^ 2) ^ 2 by ring]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (sq_nonneg x)]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx]

/-- Dividing the argument by two costs at most a factor two after taking a
fourth root.  This deliberately coarse form keeps the later algebra simple. -/
theorem half_power_fourthRoot_lower {x : ℝ} (hx : 0 ≤ x) :
    x / 2 ≤ Tripartite.realFourthRoot (x ^ 4 / 2) := by
  have harg : (x / 2) ^ 4 ≤ x ^ 4 / 2 := by
    have hx4 : 0 ≤ x ^ 4 := pow_nonneg hx 4
    nlinarith [hx4]
  have hmono := Tripartite.realFourthRoot_mono harg
  rw [realFourthRoot_pow_four (div_nonneg hx (by norm_num))] at hmono
  exact hmono

theorem fourthRoot_W_lower (n : ℕ) :
    (logScale n : ℝ) ^ 5 / 2 ≤
      Tripartite.realFourthRoot ((W n : ℝ) / 2) := by
  let L : ℝ := logScale n
  have h := half_power_fourthRoot_lower
    (x := L ^ 5) (pow_nonneg (Nat.cast_nonneg _) 5)
  have hpow : (L ^ 5) ^ 4 = (W n : ℝ) := by
    dsimp [L]
    rw [W, Nat.cast_pow, ← pow_mul]
  rwa [hpow] at h

theorem fourthRoot_Y_lower (n : ℕ) :
    (logScale n : ℝ) ^ 28 / 2 ≤
      Tripartite.realFourthRoot ((Y n : ℝ) / 2) := by
  let L : ℝ := logScale n
  have h := half_power_fourthRoot_lower
    (x := L ^ 28) (pow_nonneg (Nat.cast_nonneg _) 28)
  have hpow : (L ^ 28) ^ 4 = (Y n : ℝ) := by
    dsimp [L]
    rw [Y, Nat.cast_pow, ← pow_mul]
  rwa [hpow] at h

/-- Real majorant supplied by the first dyadic complete-box pruning. -/
noncomputable def badPruningMajorant (n : ℕ) : ℝ :=
  (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
    ((4 * (n : ℝ)) /
      Tripartite.realFourthRoot ((Y n : ℝ) / 2))

/-- Real majorant supplied by pruning large residual multipliers. -/
noncomputable def largeMultiplierMajorant (n : ℕ) : ℝ :=
  (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
    ((4 * (n : ℝ)) /
      Tripartite.realFourthRoot ((W n : ℝ) / 2))

noncomputable def badPruningError (n : ℕ) : ℕ :=
  Nat.ceil (badPruningMajorant n)

noncomputable def largeMultiplierError (n : ℕ) : ℕ :=
  Nat.ceil (largeMultiplierMajorant n)

/-- The first real pruning majorant has a power-saving polylogarithmic
upper bound. -/
theorem badPruningMajorant_le {n : ℕ} (hn : 2 ≤ n) :
    badPruningMajorant n ≤
      8 * (n : ℝ) / (logScale n : ℝ) ^ 25 := by
  let L : ℝ := logScale n
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast (show 0 < logScale n by simp [logScale])
  have hrootLower : L ^ 28 / 2 ≤
      Tripartite.realFourthRoot ((Y n : ℝ) / 2) := by
    change (logScale n : ℝ) ^ 28 / 2 ≤
      Tripartite.realFourthRoot ((Y n : ℝ) / 2)
    exact fourthRoot_Y_lower n
  have hhalfPos : 0 < L ^ 28 / 2 := by positivity
  have hdiv :
      (4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((Y n : ℝ) / 2) ≤
        (4 * (n : ℝ)) / (L ^ 28 / 2) := by
    exact div_le_div₀ (by positivity) le_rfl hhalfPos hrootLower
  have hcast :
      ((((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ)) = L ^ 3 := by
    dsimp [L, logScale]
    rw [Nat.cast_pow]
  rw [badPruningMajorant, hcast]
  calc
    L ^ 3 *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((Y n : ℝ) / 2)) ≤
        L ^ 3 * ((4 * (n : ℝ)) / (L ^ 28 / 2)) :=
      mul_le_mul_of_nonneg_left hdiv (pow_nonneg hLpos.le 3)
    _ = 8 * (n : ℝ) / L ^ 25 := by
      field_simp [hLpos.ne']
      ring

/-- The large-multiplier real majorant also has a power-saving
polylogarithmic upper bound. -/
theorem largeMultiplierMajorant_le {n : ℕ} (hn : 2 ≤ n) :
    largeMultiplierMajorant n ≤
      8 * (n : ℝ) / (logScale n : ℝ) ^ 2 := by
  let L : ℝ := logScale n
  have hLpos : 0 < L := by
    dsimp [L]
    exact_mod_cast (show 0 < logScale n by simp [logScale])
  have hrootLower : L ^ 5 / 2 ≤
      Tripartite.realFourthRoot ((W n : ℝ) / 2) := by
    change (logScale n : ℝ) ^ 5 / 2 ≤
      Tripartite.realFourthRoot ((W n : ℝ) / 2)
    exact fourthRoot_W_lower n
  have hhalfPos : 0 < L ^ 5 / 2 := by positivity
  have hdiv :
      (4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((W n : ℝ) / 2) ≤
        (4 * (n : ℝ)) / (L ^ 5 / 2) := by
    exact div_le_div₀ (by positivity) le_rfl hhalfPos hrootLower
  have hcast :
      ((((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ)) = L ^ 3 := by
    dsimp [L, logScale]
    rw [Nat.cast_pow]
  rw [largeMultiplierMajorant, hcast]
  calc
    L ^ 3 *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((W n : ℝ) / 2)) ≤
        L ^ 3 * ((4 * (n : ℝ)) / (L ^ 5 / 2)) :=
      mul_le_mul_of_nonneg_left hdiv (pow_nonneg hLpos.le 3)
    _ = 8 * (n : ℝ) / L ^ 2 := by
      field_simp [hLpos.ne']
      ring

theorem inv_logScale_pow_tendsto_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ => (1 : ℝ) / (logScale n : ℝ) ^ k)
      atTop (nhds 0) := by
  have hLtop : Tendsto (fun n : ℕ => (logScale n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_logScale_atTop
  have hpowTop : Tendsto (fun n : ℕ => (logScale n : ℝ) ^ k)
      atTop atTop := (tendsto_pow_atTop (α := ℝ) hk.ne').comp hLtop
  exact tendsto_const_nhds.div_atTop hpowTop

theorem badPruningMajorant_negligible :
    Tendsto (fun n : ℕ => badPruningMajorant n / secondOrderScale n)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n : ℕ => 8 * ((1 : ℝ) / (logScale n : ℝ) ^ 24))
      atTop (nhds 0) := by
    simpa using! (inv_logScale_pow_tendsto_zero 24 (by norm_num)).const_mul 8
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    have hmajorNonneg : 0 ≤ badPruningMajorant n := by
      unfold badPruningMajorant
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (by positivity)
          (Tripartite.realFourthRoot_nonneg _))
    exact div_nonneg hmajorNonneg hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let L : ℝ := logScale n
    have hLpos : 0 < L := by
      dsimp [L]
      exact_mod_cast (show 0 < logScale n by simp [logScale])
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      positivity
    have hmajor := badPruningMajorant_le hn
    have hlogL : Real.log (n : ℝ) ≤ L := by
      simpa [L] using! log_natCast_le_logScale (show 0 < n by omega)
    calc
      badPruningMajorant n / secondOrderScale n ≤
          (8 * (n : ℝ) / L ^ 25) / secondOrderScale n :=
        (div_le_div_iff_of_pos_right hscale).mpr (by simpa [L] using! hmajor)
      _ = 8 * (Real.log (n : ℝ) / L ^ 25) := by
        unfold secondOrderScale
        field_simp [hnpos.ne', hlog.ne', hLpos.ne']
      _ ≤ 8 * (L / L ^ 25) := by
        exact mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right (pow_pos hLpos 25)).mpr hlogL)
          (by norm_num)
      _ = 8 * ((1 : ℝ) / L ^ 24) := by
        field_simp [hLpos.ne']

theorem largeMultiplierMajorant_negligible :
    Tendsto
      (fun n : ℕ => largeMultiplierMajorant n / secondOrderScale n)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun n : ℕ => 8 * ((1 : ℝ) / (logScale n : ℝ)))
      atTop (nhds 0) := by
    simpa using! (inv_logScale_pow_tendsto_zero 1 (by norm_num)).const_mul 8
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    have hmajorNonneg : 0 ≤ largeMultiplierMajorant n := by
      unfold largeMultiplierMajorant
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (by positivity)
          (Tripartite.realFourthRoot_nonneg _))
    exact div_nonneg hmajorNonneg hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let L : ℝ := logScale n
    have hLpos : 0 < L := by
      dsimp [L]
      exact_mod_cast (show 0 < logScale n by simp [logScale])
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      positivity
    have hmajor := largeMultiplierMajorant_le hn
    have hlogL : Real.log (n : ℝ) ≤ L := by
      simpa [L] using! log_natCast_le_logScale (show 0 < n by omega)
    calc
      largeMultiplierMajorant n / secondOrderScale n ≤
          (8 * (n : ℝ) / L ^ 2) / secondOrderScale n :=
        (div_le_div_iff_of_pos_right hscale).mpr (by simpa [L] using! hmajor)
      _ = 8 * (Real.log (n : ℝ) / L ^ 2) := by
        unfold secondOrderScale
        field_simp [hnpos.ne', hlog.ne', hLpos.ne']
      _ ≤ 8 * (L / L ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right (pow_pos hLpos 2)).mpr hlogL)
          (by norm_num)
      _ = 8 * ((1 : ℝ) / L) := by
        field_simp [hLpos.ne']

/-- Taking a natural ceiling preserves negligibility for a nonnegative real
majorant. -/
theorem ceil_error_negligible
    {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n)
    (hlim : Tendsto (fun n : ℕ => f n / secondOrderScale n)
      atTop (nhds 0)) :
    Tendsto (fun n : ℕ => (Nat.ceil (f n) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  have hone := ElementaryPruningErrors.one_div_secondOrder_tendsto_zero
  have hupper : Tendsto
      (fun n : ℕ => f n / secondOrderScale n +
        1 / secondOrderScale n) atTop (nhds 0) := by
    simpa using! hlim.add hone
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    exact div_nonneg (Nat.cast_nonneg _) hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    have hceil : (Nat.ceil (f n) : ℝ) ≤ f n + 1 :=
      (le_of_lt (Nat.ceil_lt_add_one (hf n)))
    calc
      (Nat.ceil (f n) : ℝ) / secondOrderScale n ≤
          (f n + 1) / secondOrderScale n :=
        (div_le_div_iff_of_pos_right hscale).mpr hceil
      _ = f n / secondOrderScale n + 1 / secondOrderScale n := by ring

theorem badPruningError_negligible :
    Tendsto (fun n : ℕ => (badPruningError n : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  exact ceil_error_negligible
    (fun n => by
      unfold badPruningMajorant
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (by positivity)
          (Tripartite.realFourthRoot_nonneg _)))
    badPruningMajorant_negligible

theorem largeMultiplierError_negligible :
    Tendsto
      (fun n : ℕ => (largeMultiplierError n : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  exact ceil_error_negligible
    (fun n => by
      unfold largeMultiplierMajorant
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (by positivity)
          (Tripartite.realFourthRoot_nonneg _)))
    largeMultiplierMajorant_negligible

end BoxPruningError

end Erdos796
