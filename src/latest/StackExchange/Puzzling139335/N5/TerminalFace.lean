import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# A terminal diagonal support excludes the center

The two possible orientations of the placement give explicit strict
half-plane inequalities.  Only actual point containment above the source
base is needed.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

/-- If the top support normal is proportional to `(-1,1)` and the source
origin maps to the open top side, the image of the source upper half-plane
does not contain the center.  Both orientation parities are covered. -/
theorem terminal_top_normal_excludes_center {P : Set Plane}
    (hP : ∀ p ∈ P, 0 ≤ p 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {r : ℝ} (hr : 0 < r)
    (hrow₀ : linearMatrix e 1 0 = -r)
    (hrow₁ : linearMatrix e 1 1 = r)
    (htop : (e 0) 1 = 1)
    (hleft : 0 < (e 0) 0) (hright : (e 0) 0 < 1) :
    squareCenter ∉ e '' P := by
  rintro ⟨p, hp, hep⟩
  have hnonneg := mul_nonneg hr.le (hP p hp)
  have hcoordinates := affine_apply_eq_matrix_coordinates e p
  rw [hep] at hcoordinates
  have hx := congrArg (fun q : Plane => q 0) hcoordinates
  have hy := congrArg (fun q : Plane => q 1) hcoordinates
  obtain ⟨c, s, _, hM | hM⟩ := linearMatrix_classification e
  · have hs : s = -r := by simpa [hM] using hrow₀
    have hc : c = r := by simpa [hM] using hrow₁
    simp [hM, hc, hs, htop] at hx hy
    nlinarith only [hx, hy, hnonneg, hleft]
  · have hs : s = -r := by simpa [hM] using hrow₀
    have hc : c = -r := by
      have hneg : -c = r := by simpa [hM] using hrow₁
      linarith only [hneg]
    simp [hM, hc, hs, htop] at hx hy
    nlinarith only [hx, hy, hnonneg, hright]

end Puzzling139335.N5
