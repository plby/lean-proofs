import StackExchange.Puzzling139335.N7.CornerGap
import StackExchange.Puzzling139335.N7.SingletonPlacement.Parameters

/-!
# The singleton placement is forced by the actual gap endpoints

An affine isometry carrying the source bottom-right corner to the target
top-right corner can contain both gap endpoints only in one of two
positions.  The proof uses actual preimages in the source and its global
support inequality.  No local sector or boundary regularity is assumed.
-/

open Set

namespace Puzzling139335.N7

open PlaneIsometries

private theorem direct_deficit_coordinates
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {a t : ℝ}
    (hunit : a ^ 2 + t ^ 2 = 1)
    (hform : ∀ p, e p = directCoordinates a t (e 0) p)
    (hcorner : e (corner 1) = corner 2) {p : Plane} {x y : ℝ}
    (hpoint : e p = !₂[1 - x, 1 - y]) :
    1 - p 0 = a * x + t * y ∧ p 1 = t * x - a * y := by
  have hx0 := congrArg (fun q : Plane => q 0) (hform (corner 1))
  have hy0 := congrArg (fun q : Plane => q 1) (hform (corner 1))
  rw [hcorner] at hx0 hy0
  norm_num [directCoordinates, corner, Fin.ext_iff] at hx0 hy0
  have hxp := congrArg (fun q : Plane => q 0) (hform p)
  have hyp := congrArg (fun q : Plane => q 1) (hform p)
  rw [hpoint] at hxp hyp
  simp only [directCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one] at hxp hyp
  have hx : a * (1 - p 0) + t * p 1 = x := by
    nlinarith only [hx0, hxp]
  have hy : t * (1 - p 0) - a * p 1 = y := by
    nlinarith only [hy0, hyp]
  constructor
  · linear_combination a * hx + t * hy - (1 - p 0) * hunit
  · linear_combination t * hx - a * hy - p 1 * hunit

private theorem reversing_deficit_coordinates
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {a t : ℝ}
    (hunit : a ^ 2 + t ^ 2 = 1)
    (hform : ∀ p, e p = reversingCoordinates a t (e 0) p)
    (hcorner : e (corner 1) = corner 2) {p : Plane} {x y : ℝ}
    (hpoint : e p = !₂[1 - x, 1 - y]) :
    1 - p 0 = a * x + t * y ∧ p 1 = a * y - t * x := by
  have hx0 := congrArg (fun q : Plane => q 0) (hform (corner 1))
  have hy0 := congrArg (fun q : Plane => q 1) (hform (corner 1))
  rw [hcorner] at hx0 hy0
  norm_num [reversingCoordinates, corner, Fin.ext_iff] at hx0 hy0
  have hxp := congrArg (fun q : Plane => q 0) (hform p)
  have hyp := congrArg (fun q : Plane => q 1) (hform p)
  rw [hpoint] at hxp hyp
  simp only [reversingCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one] at hxp hyp
  have hx : a * (1 - p 0) - t * p 1 = x := by
    nlinarith only [hx0, hxp]
  have hy : t * (1 - p 0) + a * p 1 = y := by
    nlinarith only [hy0, hyp]
  constructor
  · linear_combination a * hx + t * hy - (1 - p 0) * hunit
  · linear_combination -t * hx + a * hy - p 1 * hunit

/-- The two actual gap endpoints determine the whole singleton placement,
including its orientation and translation. -/
theorem singleton_placement_formula {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hP : P ⊆ unitSquare)
    (hsupport : ∀ p ∈ P, N7Geometry.c * p 1 ≤ (1 / 2 : ℝ) * (1 - p 0))
    (hcorner : e (corner 1) = corner 2)
    (hleft : gapLeft N7Geometry.c (1 / 2) ∈ e '' P)
    (hright : gapRight N7Geometry.c (1 / 2) ∈ e '' P) :
    (∀ p, e p = N7Geometry.Uplus p) ∨
      (∀ p, e p = N7Geometry.Uminus p) := by
  obtain ⟨pL, hpL, hLp⟩ := hleft
  obtain ⟨pR, hpR, hRp⟩ := hright
  obtain ⟨a, t, hat, hform | hform⟩ := affine_coordinate_classification e
  · have hL := direct_deficit_coordinates e hat hform hcorner hLp
    have hR := direct_deficit_coordinates e hat hform hcorner hRp
    have hxL : 0 ≤ a * N7Geometry.c + t / 2 := by
      have h := sub_nonneg.mpr (hP hpL).1.2
      rw [hL.1] at h
      nlinarith only [h]
    have hyR : 0 ≤ t / 2 - a * N7Geometry.c := by
      have h := (hP hpR).2.1
      rw [hR.2] at h
      nlinarith only [h]
    have hwL : N7Geometry.c * (t * N7Geometry.c - a / 2) ≤
        (a * N7Geometry.c + t / 2) / 2 := by
      have h := hsupport pL hpL
      rw [hL.1, hL.2] at h
      nlinarith only [h]
    obtain ⟨ha, ht⟩ := SingletonPlacement.direct_parameters hat hxL hyR hwL
    have hx0 := congrArg (fun q : Plane => q 0) (hform (corner 1))
    have hy0 := congrArg (fun q : Plane => q 1) (hform (corner 1))
    rw [hcorner, ha, ht] at hx0 hy0
    norm_num [directCoordinates, corner, Fin.ext_iff] at hx0 hy0
    have hex : e 0 0 = (1 / 2 : ℝ) := by linarith only [hx0]
    have hey : e 0 1 = N7Geometry.u := by
      dsimp [N7Geometry.u]
      linarith only [hy0]
    refine Or.inl ?_
    intro p
    rw [hform, ha, ht]
    ext k
    fin_cases k <;>
      simp [directCoordinates, N7Geometry.Uplus, hex, hey] <;> ring
  · have hL := reversing_deficit_coordinates e hat hform hcorner hLp
    have hR := reversing_deficit_coordinates e hat hform hcorner hRp
    have hxR : 0 ≤ a / 2 + t * N7Geometry.c := by
      have h := sub_nonneg.mpr (hP hpR).1.2
      rw [hR.1] at h
      nlinarith only [h]
    have hyL : 0 ≤ a / 2 - t * N7Geometry.c := by
      have h := (hP hpL).2.1
      rw [hL.2] at h
      nlinarith only [h]
    have hwR : N7Geometry.c * (a * N7Geometry.c - t / 2) ≤
        (a / 2 + t * N7Geometry.c) / 2 := by
      have h := hsupport pR hpR
      rw [hR.1, hR.2] at h
      nlinarith only [h]
    obtain ⟨ha, ht⟩ := SingletonPlacement.reversing_parameters hat hxR hyL hwR
    have hx0 := congrArg (fun q : Plane => q 0) (hform (corner 1))
    have hy0 := congrArg (fun q : Plane => q 1) (hform (corner 1))
    rw [hcorner, ha, ht] at hx0 hy0
    norm_num [reversingCoordinates, corner, Fin.ext_iff] at hx0 hy0
    have hex : e 0 0 = N7Geometry.u := by
      dsimp [N7Geometry.u]
      linarith only [hx0]
    have hey : e 0 1 = (1 / 2 : ℝ) := by linarith only [hy0]
    refine Or.inr ?_
    intro p
    rw [hform, ha, ht]
    ext k
    fin_cases k <;>
      simp [reversingCoordinates, N7Geometry.Uminus, hex, hey] <;> ring

/-- The corresponding actual image is one of the two normalized images. -/
theorem singleton_placement_image {P : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hP : P ⊆ unitSquare)
    (hsupport : ∀ p ∈ P, N7Geometry.c * p 1 ≤ (1 / 2 : ℝ) * (1 - p 0))
    (hcorner : e (corner 1) = corner 2)
    (hleft : gapLeft N7Geometry.c (1 / 2) ∈ e '' P)
    (hright : gapRight N7Geometry.c (1 / 2) ∈ e '' P) :
    e '' P = N7Geometry.Uplus '' P ∨ e '' P = N7Geometry.Uminus '' P := by
  rcases singleton_placement_formula e hP hsupport hcorner hleft hright with h | h
  · exact Or.inl (by simp only [h])
  · exact Or.inr (by simp only [h])

end Puzzling139335.N7
