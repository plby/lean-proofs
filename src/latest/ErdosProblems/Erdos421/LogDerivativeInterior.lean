import ErdosProblems.Erdos421.LogDerivativeBound

/-! # Logarithmic derivatives throughout the interior of a nonvanishing disk -/

namespace Erdos421

open Metric

theorem norm_deriv_inner_le_of_re_bound {g : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hg : DifferentiableOn ℂ g (ball 0 R)) (hg0 : g 0 = 0)
    (hreal : ∀ z ∈ ball 0 R, (g z).re ≤ A) {w : ℂ} (hw : ‖w‖ ≤ R / 4) :
    ‖deriv g w‖ ≤ 16 * A / R := by
  have hsmall : ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖g z‖ ≤ 2 * A := by
    intro z hz
    have hzR : z ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
    have hb := Complex.borelCaratheodory_zero hA hg hreal hR hzR hg0
    apply hb.trans
    apply (div_le_iff₀ (by linarith : 0 < R - ‖z‖)).mpr
    nlinarith only [hz, hA]
  have hnear : ∀ z ∈ ball w (R / 4), ‖z‖ ≤ R / 2 := by
    intro z hz
    have hdist : ‖z - w‖ < R / 4 := by simpa only [mem_ball, dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z w
    linarith
  have hsub : ball w (R / 4) ⊆ ball (0 : ℂ) R := by
    intro z hz
    exact mem_ball_zero_iff.mpr (lt_of_le_of_lt (hnear z hz) (by linarith))
  have hwg : ‖g w‖ ≤ 2 * A := hsmall w (by linarith)
  have hmaps : Set.MapsTo g (ball w (R / 4)) (closedBall (g w) (4 * A)) := by
    intro z hz
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hsmall z (hnear z hz)])
  have hb := Complex.norm_deriv_le_div_of_mapsTo_ball (hg.mono hsub) hmaps
    (by linarith : 0 < R / 4)
  exact hb.trans_eq (by ring)

theorem logarithmic_derivative_bound_inside_ball {f : ℂ → ℂ} {c : ℂ} {R A : ℝ}
    (hR : 0 < R) (hA : 0 < A) (hf : DifferentiableOn ℂ f (ball c R))
    (hzero : ∀ z ∈ ball c R, f z ≠ 0)
    (hbound : ∀ z ∈ ball c R, ‖f z‖ ≤ Real.exp A * ‖f c‖)
    {w : ℂ} (hw : ‖w‖ ≤ R / 4) :
    ‖deriv f (c + w) / f (c + w)‖ ≤ 16 * A / R := by
  obtain ⟨g, hgc, hg, he⟩ := exists_normalized_log_on_ball hR hf hzero
  have hc : c ∈ ball c R := mem_ball_self hR
  have hfc : 0 < ‖f c‖ := norm_pos_iff.mpr (hzero c hc)
  have hreal : ∀ z ∈ ball c R, (g z).re ≤ A := by
    intro z hz
    have hnorm := congrArg norm (he z hz)
    rw [Complex.norm_exp, norm_div] at hnorm
    apply Real.exp_le_exp.mp
    rw [hnorm]
    exact (div_le_iff₀ hfc).mpr (hbound z hz)
  let G : ℂ → ℂ := fun z ↦ g (c + z)
  have htrans : ∀ z ∈ ball (0 : ℂ) R, c + z ∈ ball c R := by
    intro z hz
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hG : DifferentiableOn ℂ G (ball 0 R) := by
    intro z hz
    exact ((hg (c + z) (htrans z hz)).differentiableAt.comp z
      ((differentiableAt_const c).add differentiableAt_id)).differentiableWithinAt
  have hG0 : G 0 = 0 := by simpa only [G, add_zero] using hgc
  have hb := norm_deriv_inner_le_of_re_bound hR hA hG hG0
    (fun z hz ↦ hreal (c + z) (htrans z hz)) hw
  have hwR : w ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (by linarith)
  have hd : HasDerivAt G (deriv f (c + w) / f (c + w)) w := by
    have h := (hg (c + w) (htrans w hwR)).comp w
      ((hasDerivAt_const w c).add (hasDerivAt_id w))
    convert! h using 1
    simp only [zero_add, mul_one]
  rwa [hd.deriv] at hb

end Erdos421
