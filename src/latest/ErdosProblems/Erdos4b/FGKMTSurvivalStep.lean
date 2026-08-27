/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Global stability of the scalar covering survival step -/

namespace Erdos4b.FGKMT

noncomputable section

def survivalStep (P d : ℝ) : ℝ := P * Real.exp (-d / P)

theorem survivalStep_hasDerivAt_left {P d : ℝ} (hP : 0 < P) :
    HasDerivAt (fun Q => survivalStep Q d)
      (Real.exp (-d / P) * (1 + d / P)) P := by
  have h := (hasDerivAt_id P).mul
    (((hasDerivAt_const P (-d)).div (hasDerivAt_id P) hP.ne').exp)
  apply h.congr_deriv
  change 1 * Real.exp (-d / P) + P * (Real.exp (-d / P) *
    ((0 * P - -d * 1) / P ^ 2)) = Real.exp (-d / P) * (1 + d / P)
  field_simp
  ring

theorem survivalStep_hasDerivAt_right {P d : ℝ} (hP : 0 < P) :
    HasDerivAt (fun b => survivalStep P b) (-Real.exp (-d / P)) d := by
  have h := (((hasDerivAt_id d).neg.div_const P).exp).const_mul P
  apply h.congr_deriv
  change P * (Real.exp (-d / P) * (-1 / P)) = -Real.exp (-d / P)
  field_simp

theorem survivalStep_left_derivative_bound {P d : ℝ} (hP : 0 < P) (hd : 0 ≤ d) :
    |Real.exp (-d / P) * (1 + d / P)| ≤ 1 := by
  have ht : 0 ≤ d / P := div_nonneg hd hP.le
  rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (by linarith))]
  calc
    _ ≤ Real.exp (-d / P) * Real.exp (d / P) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (d / P)])
        (Real.exp_pos _).le
    _ = 1 := by rw [neg_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

theorem survivalStep_right_derivative_bound {P d : ℝ} (hP : 0 < P) (hd : 0 ≤ d) :
    |-Real.exp (-d / P)| ≤ 1 := by
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd) hP.le)

theorem survivalStep_lipschitz_left {P Q d : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hd : 0 ≤ d) :
    |survivalStep P d - survivalStep Q d| ≤ |P - Q| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun R => survivalStep R d)
    (f' := fun R => Real.exp (-d / R) * (1 + d / R)) (C := 1)
    (fun R hR => (survivalStep_hasDerivAt_left hR).hasDerivWithinAt)
    (fun R hR => by simpa only [Real.norm_eq_abs] using
      survivalStep_left_derivative_bound hR hd)
    (convex_Ioi (0 : ℝ)) hQ hP
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem survivalStep_lipschitz_right {P d b : ℝ}
    (hP : 0 < P) (hd : 0 ≤ d) (hb : 0 ≤ b) :
    |survivalStep P d - survivalStep P b| ≤ |d - b| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun a => survivalStep P a)
    (f' := fun a => -Real.exp (-a / P)) (C := 1)
    (fun a _ => (survivalStep_hasDerivAt_right hP).hasDerivWithinAt)
    (fun a ha => by simpa only [Real.norm_eq_abs] using
      survivalStep_right_derivative_bound hP ha)
    (convex_Ici (0 : ℝ)) hb hd
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem survivalStep_sub_le {P Q d b : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (hd : 0 ≤ d) (hb : 0 ≤ b) :
    |survivalStep P d - survivalStep Q b| ≤ |P - Q| + |d - b| := by
  exact (abs_sub_le (survivalStep P d) (survivalStep Q d) (survivalStep Q b)).trans
    (add_le_add (survivalStep_lipschitz_left hP hQ hd)
      (survivalStep_lipschitz_right hQ hd hb))

end

end Erdos4b.FGKMT
