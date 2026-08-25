import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.PrefixCertificate
import Mathlib

/-!
# Actual endpoint bounds for the strict prefix and suffix faces

The support inequalities below are obtained from source points, square containment of the
right placement, and the actual endpoints of a supported face. No hull-arc projection
inequality is an input.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

noncomputable section

private theorem sin_pos_acute {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_pos])

private theorem cos_pos_acute {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθπ⟩

theorem rightMap_e_upper {P : Set Plane} {θ u v : ℝ}
    (hfit : rightMap θ u v '' P ⊆ unitSquare) {p : Plane} (hp : p ∈ P) :
    eCoord θ p ≤ u := by
  have hx := (hfit (mem_image_of_mem _ hp)).1.2
  rw [rightMap_zero_coord] at hx
  linarith only [hx]

theorem rightMap_f_upper {P : Set Plane} {θ u v : ℝ}
    (hfit : rightMap θ u v '' P ⊆ unitSquare) {p : Plane} (hp : p ∈ P) :
    fCoord θ p ≤ v := by
  have hy := (hfit (mem_image_of_mem _ hp)).2.2
  rw [rightMap_one_coord] at hy
  linarith only [hy]

theorem rightMap_f_lower {P : Set Plane} {θ u v : ℝ}
    (hfit : rightMap θ u v '' P ⊆ unitSquare) {p : Plane} (hp : p ∈ P) :
    v - 1 ≤ fCoord θ p := by
  have hy := (hfit (mem_image_of_mem _ hp)).2.1
  rw [rightMap_one_coord] at hy
  linarith only [hy]

@[simp] theorem eCoord_incomingEnd (θ u v R : ℝ) :
    eCoord θ (incomingEnd θ u v R) = u := by
  dsimp [eCoord, incomingEnd, sourceCorner]
  linear_combination u * (Real.sin_sq_add_cos_sq θ)

@[simp] theorem fCoord_incomingEnd (θ u v R : ℝ) :
    fCoord θ (incomingEnd θ u v R) = v - R := by
  dsimp [fCoord, incomingEnd, sourceCorner]
  linear_combination (v - R) * (Real.sin_sq_add_cos_sq θ)

@[simp] theorem eCoord_outgoingEnd (θ u v T : ℝ) :
    eCoord θ (outgoingEnd θ u v T) = u - T := by
  dsimp [eCoord, outgoingEnd, sourceCorner]
  linear_combination (u - T) * (Real.sin_sq_add_cos_sq θ)

@[simp] theorem fCoord_outgoingEnd (θ u v T : ℝ) :
    fCoord θ (outgoingEnd θ u v T) = v := by
  dsimp [fCoord, outgoingEnd, sourceCorner]
  linear_combination v * (Real.sin_sq_add_cos_sq θ)

theorem eCoord_frame (θ φ : ℝ) (p : Plane) :
    eCoord φ p = Real.cos (θ - φ) * eCoord θ p -
      Real.sin (θ - φ) * fCoord θ p := by
  dsimp [eCoord, fCoord]
  rw [Real.cos_sub, Real.sin_sub]
  linear_combination -(Real.cos φ * p 0 + Real.sin φ * p 1) *
    (Real.sin_sq_add_cos_sq θ)

theorem fCoord_frame (θ φ : ℝ) (p : Plane) :
    fCoord φ p = -Real.sin (φ - θ) * eCoord θ p +
      Real.cos (φ - θ) * fCoord θ p := by
  dsimp [eCoord, fCoord]
  rw [Real.cos_sub, Real.sin_sub]
  linear_combination (Real.sin φ * p 0 - Real.cos φ * p 1) *
    (Real.sin_sq_add_cos_sq θ)

theorem eCoord_add_perpRay (φ t : ℝ) (p : Plane) :
    eCoord φ (p + t • ThreeCorners.perpRay φ) = eCoord φ p := by
  simp [eCoord, ThreeCorners.perpRay]
  ring

theorem fCoord_add_perpRay (θ φ t : ℝ) (p : Plane) :
    fCoord θ (p + t • ThreeCorners.perpRay φ) =
      fCoord θ p + t * Real.cos (θ - φ) := by
  simp [fCoord, ThreeCorners.perpRay, Real.cos_sub]
  ring

theorem fCoord_sub_ray (φ t : ℝ) (p : Plane) :
    fCoord φ (p - t • ThreeCorners.ray φ) = fCoord φ p := by
  simp [fCoord, ThreeCorners.ray]
  ring

theorem eCoord_sub_ray (θ φ t : ℝ) (p : Plane) :
    eCoord θ (p - t • ThreeCorners.ray φ) =
      eCoord θ p - t * Real.cos (φ - θ) := by
  simp [eCoord, ThreeCorners.ray, Real.cos_sub]
  ring

/-- The left source leg and nonnegative first coordinate of the outgoing endpoint give
the source-arm projection bound directly. -/
theorem outgoing_arm_bound_of_endpoints {P : Set Plane} {θ u v l T : ℝ}
    (hP : P ⊆ unitSquare) (hfit : rightMap θ u v '' P ⊆ unitSquare)
    (hL : !₂[0, l] ∈ P) (hF : outgoingEnd θ u v T ∈ P)
    (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) : T + l * Real.sin θ ≤ u := by
  have hc := cos_pos_acute hθ hθπ
  have hs := sin_pos_acute hθ hθπ
  have hv : Real.cos θ * l ≤ v := by
    simpa [fCoord] using rightMap_f_upper hfit hL
  have hFx := (hP hF).1.1
  change 0 ≤ u * Real.cos θ - v * Real.sin θ - T * Real.cos θ at hFx
  have hscaled : Real.cos θ * (T + l * Real.sin θ) ≤ Real.cos θ * u := by
    nlinarith only [hFx, mul_le_mul_of_nonneg_left hv hs.le]
  exact le_of_mul_le_mul_left hscaled hc

/-- Actual source endpoints and both sides of the inverse normal strip imply all five
rows of the strict prefix certificate, and hence exclude the configuration. -/
theorem prefix_inconsistent_of_endpoints {P : Set Plane} {θ φ u v l T : ℝ} {X Y : Plane}
    (hP : P ⊆ unitSquare) (hfit : rightMap θ u v '' P ⊆ unitSquare)
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P)
    (hL : !₂[0, l] ∈ P) (hR : !₂[1, l] ∈ P)
    (hE : incomingEnd θ u v (1 - l) ∈ P) (hF : outgoingEnd θ u v T ∈ P)
    (hu : u ≤ 1 / 2) (hl : 0 < l)
    (hφ : 0 < φ) (hφθ : φ < θ) (hθπ : θ < Real.pi / 2)
    (hX : X ∈ P) (hY : Y ∈ P)
    (hface : Y = X + (1 - 2 * T) • ThreeCorners.perpRay φ)
    (hsupport : ∀ p ∈ P, eCoord φ p ≤ eCoord φ X)
    (hstrip : ∀ p ∈ P, eCoord φ X - 1 ≤ eCoord φ p) : False := by
  have hθ : 0 < θ := hφ.trans hφθ
  have hφπ : φ < Real.pi / 2 := hφθ.trans hθπ
  have hc := cos_pos_acute hθ hθπ
  have hs := sin_pos_acute hθ hθπ
  have hcp := cos_pos_acute hφ hφπ
  have hsp := sin_pos_acute hφ hφπ
  have hδ : 0 < θ - φ := by linarith only [hφθ]
  have hδπ : θ - φ < Real.pi / 2 := by linarith only [hφ, hθπ]
  have hAc := cos_pos_acute hδ hδπ
  have hBs := sin_pos_acute hδ hδπ
  have hv_lower : Real.cos θ * l ≤ v := by
    simpa [fCoord] using rightMap_f_upper hfit hL
  have hv_upper : v ≤ 1 - Real.sin θ := by
    have hb := rightMap_f_lower hfit hB
    norm_num [fCoord, corner, Fin.ext_iff] at hb
    linarith only [hb]
  have hm : eCoord φ X ≤ 1 := by
    have ha := hstrip _ hA
    norm_num [eCoord, corner, Fin.ext_iff] at ha
    dsimp [eCoord]
    linarith only [ha]
  -- The two width bounds and the outgoing arm give the first three certificate rows.
  have hla : l ≤ Real.cos θ / (1 + Real.sin θ) := by
    have hwidth : Real.sin θ + l * Real.cos θ ≤ 1 := by
      nlinarith only [hv_lower, hv_upper]
    have hfactor : 0 < 1 + Real.sin θ := by linarith only [hs]
    have hmul := mul_le_mul_of_nonneg_right hwidth hfactor.le
    have hscaled : Real.cos θ * (l * (1 + Real.sin θ)) ≤ Real.cos θ * Real.cos θ := by
      nlinarith only [hmul, Real.sin_sq_add_cos_sq θ]
    exact (le_div_iff₀ hfactor).mpr (le_of_mul_le_mul_left hscaled hc)
  have hlb : l ≤ Real.tan (φ / 2) := by
    have hright := hsupport _ hR
    have hwidth : Real.cos φ + l * Real.sin φ ≤ 1 := by
      dsimp [eCoord] at hright hm
      nlinarith only [hright, hm]
    exact PrefixCertificate.side_fit_le_tan_half hφ hφπ hwidth
  have hT : T + l * Real.sin θ ≤ 1 / 2 :=
    (outgoing_arm_bound_of_endpoints hP hfit hL hF hθ hθπ).trans hu
  -- Comparing the supported face with the incoming endpoint gives the fourth row.
  have hface_normal : eCoord φ Y = eCoord φ X := by
    rw [hface, eCoord_add_perpRay]
  have hE_support : eCoord φ (incomingEnd θ u v (1 - l)) ≤ eCoord φ Y := by
    rw [hface_normal]
    exact hsupport _ hE
  have hE_frame := eCoord_frame θ φ (incomingEnd θ u v (1 - l))
  rw [eCoord_incomingEnd, fCoord_incomingEnd] at hE_frame
  have hY_frame := eCoord_frame θ φ Y
  have hY_e := rightMap_e_upper hfit hY
  have hY_e_mul := mul_le_mul_of_nonneg_left hY_e hAc.le
  have hY_f_scaled : Real.sin (θ - φ) * fCoord θ Y ≤
      Real.sin (θ - φ) * (v - (1 - l)) := by
    nlinarith only [hE_support, hE_frame, hY_frame, hY_e_mul]
  have hY_f : fCoord θ Y ≤ v - (1 - l) :=
    le_of_mul_le_mul_left hY_f_scaled hBs
  have hX_x : X 0 ≤ 1 := (hP hX).1.2
  have hright_support := hsupport _ hR
  have hX_y_scaled : Real.sin φ * l ≤ Real.sin φ * X 1 := by
    dsimp [eCoord] at hright_support
    nlinarith only [hright_support, mul_le_mul_of_nonneg_left hX_x hcp.le]
  have hX_y : l ≤ X 1 := le_of_mul_le_mul_left hX_y_scaled hsp
  have hX_f : -Real.sin θ + Real.cos θ * l ≤ fCoord θ X := by
    dsimp [fCoord]
    nlinarith only [mul_le_mul_of_nonneg_left hX_x hs.le,
      mul_le_mul_of_nonneg_left hX_y hc.le]
  have hface_projection : fCoord θ Y =
      fCoord θ X + (1 - 2 * T) * Real.cos (θ - φ) := by
    rw [hface, fCoord_add_perpRay]
  have hj : (1 - 2 * T) * Real.cos (θ - φ) ≤ l * (1 - Real.cos θ) := by
    nlinarith only [hY_f, hX_f, hv_upper, hface_projection]
  -- The outgoing endpoint and the first-face support give the fifth row.
  have hF_x := (hP hF).1.1
  change 0 ≤ u * Real.cos θ - v * Real.sin θ - T * Real.cos θ at hF_x
  have hu_scaled : T * Real.cos θ + Real.sin θ * v ≤ Real.cos θ * u := by
    nlinarith only [hF_x]
  have hE_projection : eCoord φ (incomingEnd θ u v (1 - l)) =
      Real.cos (θ - φ) * u + Real.sin (θ - φ) * (1 - l - v) := by
    rw [eCoord_frame θ φ, eCoord_incomingEnd, fCoord_incomingEnd]
    ring
  have hfit_lower := PrefixCertificate.support_fit_lower_bound hc hAc.le hsp.le
    (PrefixCertificate.support_projection_relation θ φ) hu_scaled hv_lower
  have hfit_row : T * Real.cos (θ - φ) + (1 - l) * Real.sin (θ - φ) +
      l * Real.sin φ ≤ 1 := by
    have hE_upper := hsupport _ hE
    nlinarith only [hfit_lower, hE_projection, hE_upper, hm]
  exact PrefixCertificate.inconsistent_original_angles hφ hφθ hθπ hl
    hla hlb hT hj hfit_row

private theorem sin_gt_half_of_cos_le_half {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ < Real.pi / 2) (hc_half : Real.cos θ ≤ 1 / 2) :
    (1 : ℝ) / 2 < Real.sin θ := by
  have hc := cos_pos_acute hθ hθπ
  have hs := sin_pos_acute hθ hθπ
  have hc_sq : Real.cos θ ^ 2 ≤ 1 / 4 := by
    nlinarith only [hc_half, mul_nonneg hc.le (sub_nonneg.mpr hc_half)]
  by_contra h
  have hs_half : Real.sin θ ≤ 1 / 2 := le_of_not_gt h
  have hs_sq : Real.sin θ ^ 2 ≤ 1 / 4 := by
    nlinarith only [hs_half, mul_nonneg hs.le (sub_nonneg.mpr hs_half)]
  nlinarith only [hc_sq, hs_sq, Real.sin_sq_add_cos_sq θ]

/-- The strict suffix face is impossible by finite endpoint support inequalities. -/
theorem suffix_inconsistent_of_endpoints {P : Set Plane} {θ φ u v l T : ℝ} {X Y : Plane}
    (hP : P ⊆ unitSquare) (hfit : rightMap θ u v '' P ⊆ unitSquare)
    (hB : corner 1 ∈ P) (hL : !₂[0, l] ∈ P) (hF : outgoingEnd θ u v T ∈ P)
    (hu : u ≤ 1 / 2) (hl : 0 < l)
    (hθ : 0 < θ) (hθφ : θ < φ) (hφπ : φ < Real.pi / 2)
    (hX : X ∈ P) (hY : Y ∈ P)
    (hface : Y = X - (1 - 2 * T) • ThreeCorners.ray φ)
    (hsupport : ∀ p ∈ P, fCoord φ p ≤ fCoord φ X) : False := by
  have hθπ : θ < Real.pi / 2 := hθφ.trans hφπ
  have hφ : 0 < φ := hθ.trans hθφ
  have hc := cos_pos_acute hθ hθπ
  have hs := sin_pos_acute hθ hθπ
  have hcp := cos_pos_acute hφ hφπ
  have hsp := sin_pos_acute hφ hφπ
  have hδ : 0 < φ - θ := by linarith only [hθφ]
  have hδπ : φ - θ < Real.pi / 2 := by linarith only [hθ, hφπ]
  have hAc := cos_pos_acute hδ hδπ
  have hBs := sin_pos_acute hδ hδπ
  have hc_half : Real.cos θ ≤ 1 / 2 := by
    have hb := rightMap_e_upper hfit hB
    norm_num [eCoord, corner, Fin.ext_iff] at hb
    linarith only [hb, hu]
  have hs_half := sin_gt_half_of_cos_le_half hθ hθπ hc_half
  have hcos_gt_sin : Real.sin θ < Real.cos (φ - θ) := by
    rw [← Real.cos_pi_div_two_sub θ]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith only [hθφ])
      (by linarith only [hθ, Real.pi_pos]) (by linarith only [hφπ])
  have hcos_half : (1 : ℝ) / 2 < Real.cos (φ - θ) := hs_half.trans hcos_gt_sin
  have harm := outgoing_arm_bound_of_endpoints hP hfit hL hF hθ hθπ
  have hls : 0 < l * Real.sin θ := mul_pos hl hs
  have hj_pos : 0 < 1 - 2 * T := by linarith only [harm, hu, hls]
  -- Compare the suffix face with the outgoing endpoint, then project its finite segment.
  have hF_support := hsupport _ hF
  have hF_frame := fCoord_frame θ φ (outgoingEnd θ u v T)
  rw [eCoord_outgoingEnd, fCoord_outgoingEnd] at hF_frame
  have hX_frame := fCoord_frame θ φ X
  have hX_f := rightMap_f_upper hfit hX
  have hX_f_mul := mul_le_mul_of_nonneg_left hX_f hAc.le
  have hX_e_scaled : Real.sin (φ - θ) * eCoord θ X ≤
      Real.sin (φ - θ) * (u - T) := by
    nlinarith only [hF_support, hF_frame, hX_frame, hX_f_mul]
  have hX_e : eCoord θ X ≤ u - T := le_of_mul_le_mul_left hX_e_scaled hBs
  have hface_normal : fCoord φ Y = fCoord φ X := by
    rw [hface, fCoord_sub_ray]
  have hL_support : fCoord φ !₂[0, l] ≤ fCoord φ Y := by
    rw [hface_normal]
    exact hsupport _ hL
  have hY_x : 0 ≤ Y 0 := (hP hY).1.1
  have hY_y_scaled : Real.cos φ * l ≤ Real.cos φ * Y 1 := by
    dsimp [fCoord] at hL_support
    nlinarith only [hL_support, mul_nonneg hsp.le hY_x]
  have hY_y : l ≤ Y 1 := le_of_mul_le_mul_left hY_y_scaled hcp
  have hY_e : Real.sin θ * l ≤ eCoord θ Y := by
    dsimp [eCoord]
    nlinarith only [mul_nonneg hc.le hY_x, mul_le_mul_of_nonneg_left hY_y hs.le]
  have hface_projection : eCoord θ Y =
      eCoord θ X - (1 - 2 * T) * Real.cos (φ - θ) := by
    rw [hface, eCoord_sub_ray]
  have hprojection : (1 - 2 * T) * Real.cos (φ - θ) ≤ u - T - Real.sin θ * l := by
    nlinarith only [hX_e, hY_e, hface_projection]
  have hstrict := mul_pos hj_pos (sub_pos.mpr hcos_half)
  nlinarith only [hprojection, hstrict, hu, hls]

end

end Puzzling139335.N4TwoOneOne
