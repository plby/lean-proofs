import StackExchange.Puzzling139335.N7.CornerGap
import StackExchange.Puzzling139335.AcuteCorner.Cone

/-!
# A metric pair bound for the actual narrow source wedge

Two actual points of the source satisfy an affine-invariant determinant
bound.  If a congruent copy fixing the corner contains both endpoints of
the gap, this bound forces the source height to be exactly one half.
There is no angle-sum or sector-germ assumption.
-/

open Set

namespace Puzzling139335.N7

open AcuteCorner

private theorem directed_wedge_pair_bound {c s : ℝ} {u v : Plane}
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ c * u 1 ≤ s * u 0)
    (hv : 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ c * v 1 ≤ s * v 0) :
    c * det u v ≤ s * dot u v := by
  have hfit := mul_le_mul_of_nonneg_left hv.2.2 hu.1
  have hcross := mul_nonneg (mul_nonneg hc hu.2.1) hv.1
  have hpositive := mul_nonneg (mul_nonneg hs hu.2.1) hv.2.1
  dsimp [det, dot]
  nlinarith only [hfit, hcross, hpositive]

/-- The determinant-to-scalar-product bound for an explicit narrow cone. -/
theorem wedge_pair_bound {c s : ℝ} {u v : Plane}
    (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hu : 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ c * u 1 ≤ s * u 0)
    (hv : 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ c * v 1 ≤ s * v 0) :
    c * |det u v| ≤ s * dot u v := by
  have hupper := directed_wedge_pair_bound hc hs hu hv
  have hlower := directed_wedge_pair_bound hc hs hv hu
  have hneg : -(s * dot u v) ≤ c * det u v := by
    dsimp [det, dot] at hlower ⊢
    nlinarith only [hlower]
  have habs := abs_le.mpr ⟨hneg, hupper⟩
  simpa only [abs_mul, abs_of_nonneg hc] using habs

/-- The same bound at the source bottom-right point, for actual source
members rather than hull points. -/
theorem source_wedge_pair_bound {P : Set Plane} {c s : ℝ}
    (hP : P ⊆ unitSquare) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hsupport : ∀ p ∈ P, c * p 1 ≤ s * (1 - p 0))
    {p q : Plane} (hp : p ∈ P) (hq : q ∈ P) :
    c * |det (p - corner 1) (q - corner 1)| ≤
      s * dot (p - corner 1) (q - corner 1) := by
  let u : Plane := !₂[1 - p 0, p 1]
  let v : Plane := !₂[1 - q 0, q 1]
  have hu : 0 ≤ u 0 ∧ 0 ≤ u 1 ∧ c * u 1 ≤ s * u 0 :=
    ⟨sub_nonneg.mpr (hP hp).1.2, (hP hp).2.1, hsupport p hp⟩
  have hv : 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ c * v 1 ≤ s * v 0 :=
    ⟨sub_nonneg.mpr (hP hq).1.2, (hP hq).2.1, hsupport q hq⟩
  have hdet : det u v = -det (p - corner 1) (q - corner 1) := by
    simp [det, u, v, corner, Fin.ext_iff]
    ring
  have hdot : dot u v = dot (p - corner 1) (q - corner 1) := by
    simp [dot, u, v, corner, Fin.ext_iff]
    ring
  have h := wedge_pair_bound hc hs hu hv
  simpa only [hdet, hdot, abs_neg] using h

/-- Transport the bound through any actual affine isometry carrying the
source corner to the target corner. -/
theorem image_wedge_pair_bound {P : Set Plane} {c s : ℝ}
    (hP : P ⊆ unitSquare) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hsupport : ∀ p ∈ P, c * p 1 ≤ s * (1 - p 0))
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e (corner 1) = corner 2)
    {p q : Plane} (hp : p ∈ e '' P) (hq : q ∈ e '' P) :
    c * |det (p - corner 2) (q - corner 2)| ≤
      s * dot (p - corner 2) (q - corner 2) := by
  obtain ⟨x, hx, rfl⟩ := hp
  obtain ⟨y, hy, rfl⟩ := hq
  rw [← he, affine_abs_det_sub, affine_dot_sub]
  exact source_wedge_pair_bound hP hc hs hsupport hx hy

/-- Containing the two actual gap endpoints forces the maximal source
height. This replaces the thirty-degree angular-sum calculation. -/
theorem half_height_of_gap_endpoints {P : Set Plane} {c s : ℝ}
    (hP : P ⊆ unitSquare) (hc : 0 < c) (hs : 0 < s)
    (hst : s < c) (hhalf : s ≤ (1 / 2 : ℝ))
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hsupport : ∀ p ∈ P, c * p 1 ≤ s * (1 - p 0))
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e (corner 1) = corner 2)
    (hleft : gapLeft c s ∈ e '' P) (hright : gapRight c s ∈ e '' P) :
    s = (1 / 2 : ℝ) := by
  have hpair := image_wedge_pair_bound hP hc.le hs.le hsupport e he hleft hright
  have hdet : det (gapLeft c s - corner 2) (gapRight c s - corner 2) =
      (c ^ 2 - s ^ 2) / 16 := by
    simp [det, gapLeft, gapRight, corner, Fin.ext_iff]
    ring
  have hdot : dot (gapLeft c s - corner 2) (gapRight c s - corner 2) = c * s / 8 := by
    simp [dot, gapLeft, gapRight, corner, Fin.ext_iff]
    ring
  have hdetpos : 0 ≤ (c ^ 2 - s ^ 2) / 16 := by
    have hsquares := mul_self_le_mul_self hs.le hst.le
    nlinarith only [hsquares]
  rw [hdet, hdot, abs_of_nonneg hdetpos] at hpair
  have hproduct : c * (c ^ 2 - 3 * s ^ 2) ≤ 0 := by
    nlinarith only [hpair]
  have hdiff : c ^ 2 - 3 * s ^ 2 ≤ 0 := by
    by_contra hnot
    exact (not_le_of_gt (mul_pos hc (lt_of_not_ge hnot))) hproduct
  have hsLower : (1 / 2 : ℝ) ≤ s := by
    nlinarith only [hdiff, hunit, hs, hhalf]
  exact le_antisymm hhalf hsLower

end Puzzling139335.N7
