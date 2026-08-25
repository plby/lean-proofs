import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.N5Facet

/-!
# The strict incoming-face obstruction from actual points

Two supporting-line inequalities order the vertical coordinates of the
face endpoints.  This replaces any appeal to variation along a convex-hull
chain: only the displayed points and their supporting lines are used.
-/

open Set

namespace Puzzling139335.N5

private theorem vertical_order_of_support_lines {c s p q x y : ℝ}
    (hc : 0 < c) (hp : 0 < p) (hdet : 0 < p * s - c * q)
    (hC : 0 ≤ c * x + s * y) (hF : p * x + q * y ≤ 0) : 0 ≤ y := by
  have hleft := mul_nonneg hp.le hC
  have hright := mul_nonpos_of_nonneg_of_nonpos hc.le hF
  have hprod : 0 ≤ (p * s - c * q) * y := by
    nlinarith only [hleft, hright]
  by_contra hy
  have hneg := mul_neg_of_pos_of_neg hdet (lt_of_not_ge hy)
  linarith

/-- The actual prefix-face endpoints and the incoming corner-arm endpoint
force the vertical lower bound used in the scalar obstruction. -/
theorem prefix_height_bound_of_points {P : Set Plane} {X Y : Plane}
    {t φ h k b T j : ℝ}
    (hP : P ⊆ unitSquare)
    (ht : 0 < t) (ht4 : t < Real.pi / 4) (hφ : 0 < φ) (hφt : φ < t)
    (hE : (!₂[1, b] : Plane) ∈ P)
    (hF : (!₂[h + T * Real.sin t, k - T * Real.cos t] : Plane) ∈ P)
    (hX : X ∈ P) (hY : Y ∈ P)
    (hcorner : ∀ p ∈ P,
      Real.cos t * (p 0 - h) + Real.sin t * (p 1 - k) ≤ 0)
    (hface : ∀ p ∈ P,
      Real.cos φ * (p 0 - X 0) + Real.sin φ * (p 1 - X 1) ≤ 0)
    (hXY₀ : X 0 = Y 0 - j * Real.sin φ)
    (hXY₁ : X 1 = Y 1 + j * Real.cos φ) :
    b + j * Real.cos φ + T * Real.cos t ≤ k := by
  obtain ⟨hp, hq, hc, hs⟩ := N5Facet.suffix_trig_pos hφ hφt ht4
  have hdet : 0 < Real.cos φ * Real.sin t - Real.cos t * Real.sin φ := by
    have hd := N5Facet.sin_sub_pos hφ hφt ht4
    rw [Real.sin_sub] at hd
    nlinarith only [hd]
  have hEline := hface _ hE
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one] at hEline
  have hElineY :
      Real.cos φ * (1 - Y 0) + Real.sin φ * (b - Y 1) ≤ 0 := by
    rw [hXY₀, hXY₁] at hEline
    nlinarith only [hEline]
  have hYx : Y 0 ≤ 1 := (hP hY).1.2
  have hbY : b ≤ Y 1 := by
    have hnonneg := mul_nonneg hp.le (sub_nonneg.mpr hYx)
    by_contra hnot
    have hpositive := mul_pos hq (sub_pos.mpr (lt_of_not_ge hnot))
    nlinarith only [hElineY, hnonneg, hpositive]
  have hFline := hface _ hF
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one] at hFline
  have hXcorner := hcorner _ hX
  have hCF : 0 ≤
      Real.cos t * (h + T * Real.sin t - X 0) +
      Real.sin t * (k - T * Real.cos t - X 1) := by
    nlinarith only [hXcorner]
  have hYF : X 1 ≤ k - T * Real.cos t := by
    have hnonneg := vertical_order_of_support_lines hc hp hdet hCF hFline
    linarith
  linarith

/-- An actual strict incoming supporting face contradicts the N5 bounds.
No monotonicity assertion about an unparametrized hull chain is assumed. -/
theorem prefix_face_impossible_of_points {P : Set Plane} {X Y : Plane}
    {t φ h k b T j : ℝ}
    (hP : P ⊆ unitSquare)
    (ht : 0 < t) (ht4 : t < Real.pi / 4) (hφ : 0 < φ) (hφt : φ < t)
    (hk : k < Real.cos t) (hb : 0 < b) (hj : 0 < j)
    (hJT : j + T = 1 - b)
    (hE : (!₂[1, b] : Plane) ∈ P)
    (hF : (!₂[h + T * Real.sin t, k - T * Real.cos t] : Plane) ∈ P)
    (hX : X ∈ P) (hY : Y ∈ P)
    (hcorner : ∀ p ∈ P,
      Real.cos t * (p 0 - h) + Real.sin t * (p 1 - k) ≤ 0)
    (hface : ∀ p ∈ P,
      Real.cos φ * (p 0 - X 0) + Real.sin φ * (p 1 - X 1) ≤ 0)
    (hXY₀ : X 0 = Y 0 - j * Real.sin φ)
    (hXY₁ : X 1 = Y 1 + j * Real.cos φ) : False :=
  N5Facet.prefix_face_impossible ht ht4 hφ hφt hk hb hj hJT
    (prefix_height_bound_of_points hP ht ht4 hφ hφt hE hF hX hY hcorner hface hXY₀ hXY₁)

end Puzzling139335.N5
