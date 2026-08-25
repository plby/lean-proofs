import Util.Bernays.CharacterEulerProduct

/-!
# The exact half-pole of the local norm series

The zeta residue and nonvanishing of a nontrivial quadratic Dirichlet
L-function give the positive constant needed by the Tauberian theorem.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem tendsto_real_one_add_zero :
    Tendsto (fun t : ℝ => 1 + t) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  simpa only [add_zero] using
    ((show Continuous (fun t : ℝ => (1 : ℝ) + t) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_complex_one_add_zero :
    Tendsto (fun t : ℝ => (1 : ℂ) + (t : ℂ)) (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  simpa only [Complex.ofReal_zero, add_zero] using
    ((show Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ)) by fun_prop).tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_zeta_norm_residue :
    Tendsto (fun t : ℝ => t * ‖riemannZeta ((1 : ℂ) + (t : ℂ))‖)
      (𝓝[Set.Ioi 0] 0) (𝓝 1) := by
  have hshift : Tendsto (fun t : ℝ => (1 : ℂ) + (t : ℂ))
      (𝓝[Set.Ioi 0] 0) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_complex_one_add_zero, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change (1 : ℂ) + (t : ℂ) ≠ 1
    intro heq
    have hr := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at hr
    have : 0 < t := ht
    linarith
  have h := (riemannZeta_residue_one.comp hshift).norm
  rw [norm_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change ‖((1 : ℂ) + (t : ℂ) - 1) * riemannZeta ((1 : ℂ) + (t : ℂ))‖ = _
  rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]

noncomputable def characterLocalConstant {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  sqrt (‖χ.LFunction 1‖ * squareCorrection (fun p : ℕ => χ p = -1) 1 *
    ramifiedCorrection (ramifiedPrimes N) 1)

theorem characterLocalConstant_pos {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : 0 < characterLocalConstant χ := by
  apply sqrt_pos.mpr
  exact mul_pos (mul_pos (norm_pos_iff.mpr (χ.LFunction_apply_one_ne_zero hχ))
    (squareCorrection_pos _ _)) (ramifiedCorrection_pos _ _)

theorem localParity_realDirichlet_nonneg (S : ℕ → Prop) (s : ℝ) :
    0 ≤ realDirichlet (localParity S) s :=
  tsum_nonneg fun n => div_nonneg (localParity_nonneg S (n + 1))
    (rpow_nonneg (Nat.cast_nonneg _) s)

theorem localParity_dirichlet_halfPole {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun t : ℝ => sqrt t * realDirichlet (localParity (fun p : ℕ => χ p = -1)) (1 + t))
      (𝓝[Set.Ioi 0] 0) (𝓝 (characterLocalConstant χ)) := by
  let S : ℕ → Prop := fun p => χ p = -1
  let F : ℝ → ℝ := realDirichlet (localParity S)
  let G : ℝ → ℝ := squareCorrection S
  let R : ℝ → ℝ := ramifiedCorrection (ramifiedPrimes N)
  have hF (s : ℝ) : 0 ≤ F s := localParity_realDirichlet_nonneg S s
  have hL : Tendsto (fun t : ℝ => ‖χ.LFunction ((1 : ℂ) + (t : ℂ))‖)
      (𝓝[Set.Ioi 0] 0) (𝓝 ‖χ.LFunction 1‖) :=
    (((χ.differentiableAt_LFunction 1 (Or.inr hχ)).continuousAt.tendsto).comp
      tendsto_complex_one_add_zero).norm
  have hG : Tendsto (fun t : ℝ => G (1 + t)) (𝓝[Set.Ioi 0] 0) (𝓝 (G 1)) :=
    (continuous_squareCorrection S).continuousAt.tendsto.comp tendsto_real_one_add_zero
  have hR : Tendsto (fun t : ℝ => R (1 + t)) (𝓝[Set.Ioi 0] 0) (𝓝 (R 1)) :=
    (continuous_ramifiedCorrection (ramifiedPrimes N)).continuousAt.tendsto.comp tendsto_real_one_add_zero
  have hm := ((tendsto_zeta_norm_residue.mul hL).mul hG).mul hR
  simp only [one_mul] at hm
  have hsq : Tendsto (fun t : ℝ => t * (F (1 + t)) ^ 2) (𝓝[Set.Ioi 0] 0)
      (𝓝 (‖χ.LFunction 1‖ * G 1 * R 1)) := by
    apply hm.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hs : 1 < 1 + t := by have : 0 < t := ht; linarith
    have heq := congrArg norm (localParity_dirichlet_square χ hχ₂ hs)
    simp only [Complex.ofReal_add, Complex.ofReal_one] at heq
    have hGn : 0 ≤ G (1 + t) := (squareCorrection_pos S (1 + t)).le
    have hRn : 0 ≤ R (1 + t) := (ramifiedCorrection_pos (ramifiedPrimes N) (1 + t)).le
    change ‖(F (1 + t) : ℂ) ^ 2‖ =
      ‖riemannZeta ((1 : ℂ) + (t : ℂ)) * χ.LFunction ((1 : ℂ) + (t : ℂ)) *
        (G (1 + t) : ℂ) * (R (1 + t) : ℂ)‖ at heq
    simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hF (1 + t)), abs_of_nonneg hGn, abs_of_nonneg hRn] at heq
    change t * ‖riemannZeta ((1 : ℂ) + (t : ℂ))‖ * ‖χ.LFunction ((1 : ℂ) + (t : ℂ))‖ *
      G (1 + t) * R (1 + t) = t * F (1 + t) ^ 2
    rw [heq]
    ring
  have hroot := (continuous_sqrt.tendsto (‖χ.LFunction 1‖ * G 1 * R 1)).comp hsq
  apply hroot.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change sqrt (t * F (1 + t) ^ 2) = sqrt t * F (1 + t)
  rw [sqrt_mul (le_of_lt ht), sqrt_sq (hF (1 + t))]

theorem localParity_reciprocal_asymptotic {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => reciprocalSum (localParity (fun p : ℕ => χ p = -1)) ⌊x⌋₊ /
      sqrt (log x)) atTop (𝓝 (2 * characterLocalConstant χ / sqrt π)) :=
  reciprocalSum_div_sqrt_log_tendsto (localParity_nonneg _) (localParity_le_one _)
    (characterLocalConstant_pos χ hχ) (localParity_dirichlet_halfPole χ hχ₂ hχ)

end Bernays
