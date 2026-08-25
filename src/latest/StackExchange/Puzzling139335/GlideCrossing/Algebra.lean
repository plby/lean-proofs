import Mathlib

/-!+# Algebra for the reversed-straddle glide obstruction

The geometric input consists of support-face endpoint bounds.  The results
in this file are scalar identities and inequalities and use no topological
assumptions or computational axioms.
-/

namespace Puzzling139335.GlideCrossing

theorem firstDet_identity (C S c s x₁ y₁ x₂ y₂ : ℝ)
    (hcircle : C ^ 2 + S ^ 2 = 1) :
    S * (1 - (-C * x₁ + S * y₁) - (c * x₂ + s * y₂)) +
        C * ((-S * x₁ - C * y₁) - (-s * x₂ + c * y₂)) =
      S - y₁ - (S * c - C * s) * x₂ - (C * c + S * s) * y₂ := by
  calc
    _ = S - (C ^ 2 + S ^ 2) * y₁ - (S * c - C * s) * x₂ -
        (C * c + S * s) * y₂ := by ring
    _ = _ := by rw [hcircle]; ring

theorem secondDet_identity (C S c s x₁ y₁ x₂ y₂ : ℝ)
    (hcircle : c ^ 2 + s ^ 2 = 1) :
    s * (1 - (-C * x₁ + S * y₁) - (c * x₂ + s * y₂)) +
        c * ((-S * x₁ - C * y₁) - (-s * x₂ + c * y₂)) =
      s - (S * c - C * s) * x₁ - (C * c + S * s) * y₁ - y₂ := by
  calc
    _ = s - (S * c - C * s) * x₁ - (C * c + S * s) * y₁ -
        (c ^ 2 + s ^ 2) * y₂ := by ring
    _ = _ := by rw [hcircle]; ring

theorem firstCoefficient_identity (C S c s : ℝ)
    (hcircle : c ^ 2 + s ^ 2 = 1) :
    (C * c + S * s) * c - (S * c - C * s) * s = C := by
  calc
    _ = C * (c ^ 2 + s ^ 2) := by ring
    _ = C := by rw [hcircle]; ring

theorem secondCoefficient_identity (C S c s : ℝ)
    (hcircle : C ^ 2 + S ^ 2 = 1) :
    (S * c - C * s) * S + (C * c + S * s) * C = c := by
  calc
    _ = c * (C ^ 2 + S ^ 2) := by ring
    _ = c := by rw [hcircle]; ring

theorem firstDet_lower (C S c s D K p r x₂ y₁ y₂ : ℝ)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hcoef : K * c - D * s = C)
    (hy₁ : y₁ ≤ 1 / 2 - C * r) (hx₂ : x₂ ≤ 1 + s * p)
    (hy₂ : y₂ ≤ 1 / 2 - c * p) :
    S - (1 + K) / 2 + C * (p + r) ≤
      (S - y₁ - D * x₂ - K * y₂) + D := by
  have hx := mul_le_mul_of_nonneg_left hx₂ hD
  have hy := mul_le_mul_of_nonneg_left hy₂ hK
  have hc := congrArg (fun z : ℝ => z * p) hcoef
  nlinarith only [hy₁, hx, hy, hc]

theorem secondDet_lower (C S c s D K p r x₁ y₁ y₂ : ℝ)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hcoef : D * S + K * C = c)
    (hx₁ : x₁ ≤ 1 - S * r) (hy₁ : y₁ ≤ 1 / 2 - C * r)
    (hy₂ : y₂ ≤ 1 / 2 - c * p) :
    s - (1 + K) / 2 + c * (p + r) ≤
      (s - D * x₁ - K * y₁ - y₂) + D := by
  have hx := mul_le_mul_of_nonneg_left hx₁ hD
  have hy := mul_le_mul_of_nonneg_left hy₁ hK
  have hc := congrArg (fun z : ℝ => z * r) hcoef
  nlinarith only [hy₂, hx, hy, hc]

theorem firstArm_lower (C S c s K a b : ℝ) (hC : 0 ≤ C)
    (ha : a ≤ min (1 / 2) (c / (1 + s))) (hb : b ≤ C / (1 + S)) :
    S - (1 + K) / 2 + C * (1 - min (1 / 2) (c / (1 + s)) - C / (1 + S)) ≤
      S - (1 + K) / 2 + C * ((1 / 2 - a) + (1 / 2 - b)) := by
  have hsum : 1 - min (1 / 2) (c / (1 + s)) - C / (1 + S) ≤
      (1 / 2 - a) + (1 / 2 - b) := by linarith
  linarith only [mul_le_mul_of_nonneg_left hsum hC]

theorem halfLengthSum_lower (C p r b B : ℝ) (hC : 0 ≤ C)
    (hr : r = 1 / 2 - b) (hp : 2 * C * r ≤ p) (hb : b ≤ B) :
    1 / 2 + C - (1 + 2 * C) * B ≤ p + r := by
  have hfactor : 0 ≤ 1 + 2 * C := by positivity
  have hmul := mul_le_mul_of_nonneg_left hb hfactor
  rw [hr] at hp ⊢
  nlinarith only [hp, hmul]

theorem secondArm_lower (C S c s K a b : ℝ) (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hheight : 2 * C * (1 / 2 - b) ≤ 1 / 2 - a)
    (hb : b ≤ min (s / (1 + c)) (C / (1 + S))) :
    s - (1 + K) / 2 + c *
        (1 / 2 + C - (1 + 2 * C) * min (s / (1 + c)) (C / (1 + S))) ≤
      s - (1 + K) / 2 + c * ((1 / 2 - a) + (1 / 2 - b)) := by
  have hsum := halfLengthSum_lower C (1 / 2 - a) (1 / 2 - b) b
    (min (s / (1 + c)) (C / (1 + S))) hC rfl hheight hb
  linarith only [mul_le_mul_of_nonneg_left hsum hc]

theorem faceHeight_product (C c p r : ℝ) (hc : 0 ≤ c) (hr : 0 < r)
    (h₁ : 2 * C * r ≤ p) (h₂ : 2 * c * p ≤ r) : 4 * C * c ≤ 1 := by
  have hmul : (4 * C * c) * r ≤ 1 * r := by
    calc
      (4 * C * c) * r = (2 * c) * (2 * C * r) := by ring
      _ ≤ (2 * c) * p := mul_le_mul_of_nonneg_left h₁ (by positivity)
      _ ≤ 1 * r := by simpa using h₂
  exact le_of_mul_le_mul_right hmul hr

theorem smallerCos_le_half (C c : ℝ) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hprod : 4 * C * c ≤ 1) : C ≤ 1 / 2 := by
  have hmul := mul_nonneg hC (sub_nonneg.mpr hCc)
  nlinarith [sq_nonneg (C - 1 / 2)]

/-- In an excluded noncrossing half-plane, a common point can only be the
intrinsic corner.  Topology is needed only to rule out that singleton contact. -/
theorem corner_intersection_coordinates (F D K x y : ℝ)
    (hF : 0 ≤ F) (hD : 0 < D) (hK : 0 < K) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hline : F + D * x + K * y ≤ 0) : F = 0 ∧ x = 0 ∧ y = 0 := by
  have hDx := mul_nonneg hD.le hx
  have hKy := mul_nonneg hK.le hy
  have hFzero : F = 0 := by linarith
  have hDxzero : D * x = 0 := by linarith
  have hKyzero : K * y = 0 := by linarith
  exact ⟨hFzero, (mul_eq_zero.mp hDxzero).resolve_left hD.ne',
    (mul_eq_zero.mp hKyzero).resolve_left hK.ne'⟩

end Puzzling139335.GlideCrossing
