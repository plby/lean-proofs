/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Asymptotic normalized small-ball estimates as the variance diverges.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.NormalizedSmallBall
import ErdosProblems.Erdos521.VarianceLimits

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

noncomputable def normalizedSmallBallConstant : ℝ :=
  Real.exp (1 / 2) * Real.sqrt (Real.pi / (1 / (4 * Real.pi ^ 2)))

noncomputable def normalizedSmallBallError (V t : ℝ) : ℝ :=
  Real.exp (1 / 2) * (Real.exp (-(1 / (4 * Real.pi ^ 2)) * V) + 2 * Real.exp (-(t ^ 2 / 2) * V))

theorem normalizedSmallBallConstant_pos : 0 < normalizedSmallBallConstant := by
  unfold normalizedSmallBallConstant
  positivity

theorem normalizedSmallBallError_tendsto_zero (V : ℕ → ℝ) (hV : Tendsto V atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun j ↦ normalizedSmallBallError (V j) t) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun j ↦ Real.exp (-(1 / (4 * Real.pi ^ 2)) * V j)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hV.const_mul_atTop_of_neg (by
      have : 0 < (1 / (4 * Real.pi ^ 2) : ℝ) := by positivity
      linarith))
  have h₂ : Tendsto (fun j ↦ Real.exp (-(t ^ 2 / 2) * V j)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hV.const_mul_atTop_of_neg (by
      have : 0 < t ^ 2 / 2 := by positivity
      linarith))
  simpa only [normalizedSmallBallError, mul_zero, add_zero] using
    (h₁.add (h₂.const_mul 2)).const_mul (Real.exp (1 / 2))

theorem powerSum_smallBall_normalized_error (n : ℕ) {x t : ℝ}
    (hx : 1 / 2 ≤ x) (hx₁ : x ≤ 1) (ht : 0 < t) :
    sequenceLaw.real {ε | |powerSum ε (n + 1) x| ≤ t * Real.sqrt (geometricVariance x (n + 1))} ≤
      normalizedSmallBallConstant * t + normalizedSmallBallError (geometricVariance x (n + 1)) t := by
  have h := powerSum_smallBall_normalized n 0 (by omega) hx hx₁ ht
  dsimp only at h
  have he : -((t * Real.sqrt (geometricVariance x (n + 1))) * (x ^ 0)⁻¹) ^ 2 / 2 =
      -(t ^ 2 / 2) * geometricVariance x (n + 1) := by
    rw [pow_zero, inv_one, mul_one, mul_pow, Real.sq_sqrt (geometricVariance_nonneg _ _)]
    ring
  rw [he] at h
  apply h.trans_eq
  unfold normalizedSmallBallConstant normalizedSmallBallError
  ring

theorem polynomial_zero_probability_tendsto_zero (d : ℕ → ℕ) (x : ℕ → ℝ)
    (hd : Tendsto d atTop atTop) (hx : Tendsto x atTop (𝓝 1))
    (hI : ∀ᶠ j : ℕ in atTop, x j ≤ 1) :
    Tendsto (fun j ↦ sequenceLaw.real {ε | powerSum ε (d j + 1) (x j) = 0}) atTop (𝓝 0) := by
  have hV : Tendsto (fun j ↦ geometricVariance (x j) (d j + 1)) atTop atTop :=
    geometricVariance_tendsto_atTop _ x ((tendsto_add_atTop_nat 1).comp hd) hx
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j ↦ ha.trans_le (measureReal_nonneg))
  · intro η hη
    let t := η / (2 * normalizedSmallBallConstant)
    have ht : 0 < t := div_pos hη (mul_pos (by norm_num) normalizedSmallBallConstant_pos)
    have htK : normalizedSmallBallConstant * t = η / 2 := by
      dsimp [t]
      field_simp [normalizedSmallBallConstant_pos.ne']
    filter_upwards [hI, hx.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      (normalizedSmallBallError_tendsto_zero _ hV ht).eventually (gt_mem_nhds (by linarith : 0 < η / 2))]
      with j hj₁ hj₀ hjerr
    have hsub : {ε | powerSum ε (d j + 1) (x j) = 0} ⊆
        {ε | |powerSum ε (d j + 1) (x j)| ≤ t * Real.sqrt (geometricVariance (x j) (d j + 1))} := by
      intro ε hε
      change powerSum ε (d j + 1) (x j) = 0 at hε
      change |powerSum ε (d j + 1) (x j)| ≤ _
      rw [hε, abs_zero]
      positivity
    have h := (measureReal_mono (μ := sequenceLaw) hsub).trans
      (powerSum_smallBall_normalized_error (d j) hj₀.le hj₁ ht)
    rw [htK] at h
    linarith

end Erdos521
