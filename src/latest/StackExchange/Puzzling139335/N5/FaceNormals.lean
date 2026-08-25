import StackExchange.Puzzling139335.N5.FaceNormals.Support
import StackExchange.Puzzling139335.N5.FaceNormals.Algebra
import StackExchange.Puzzling139335.N5.CornerFrame

/-!
# Allowed support-face normals from the actual corner placement

The frame formula is the one supplied by `cornerFrame_of_placement`.
Square containment of that actual placement supplies both supporting
inequalities at the third point.  The three geometric exclusions then give
an exhaustive classification of normals whose support level is attained at
two distinct points.
-/

open Set

namespace Puzzling139335.N5

/-- The two exact formulas proved by `cornerFrame_of_placement`, bundled
for reuse in support-face arguments. -/
def CornerFrameFormula (e : Plane ≃ᵃⁱ[ℝ] Plane) (C : Plane) (c s : ℝ) : Prop :=
  (∀ p, e p =
    !₂[1 - c * C 0 - s * C 1 + c * p 0 + s * p 1,
       1 + s * C 0 - c * C 1 - s * p 0 + c * p 1]) ∨
  (∀ p, e p =
    !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
       1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])

/-- The upper coordinate bounds of the actual square placement yield the
two supporting half-planes at `C`, in either orientation. -/
theorem corner_support_inequalities_of_frame {P : Set Plane} {C : Plane} {c s : ℝ}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (hform : CornerFrameFormula e C c s) :
    ∀ p ∈ P,
      c * (p 0 - C 0) + s * (p 1 - C 1) ≤ 0 ∧
      (-s) * (p 0 - C 0) + c * (p 1 - C 1) ≤ 0 := by
  intro p hp
  have hfit := he ⟨p, hp, rfl⟩
  rcases hform with hform | hform
  · rw [hform p] at hfit
    norm_num [unitSquare] at hfit
    constructor
    · nlinarith only [hfit.1.2]
    · nlinarith only [hfit.2.2]
  · rw [hform p] at hfit
    norm_num [unitSquare] at hfit
    constructor
    · nlinarith only [hfit.2.2]
    · nlinarith only [hfit.1.2]

/-- The half-plane consequences of the source geometry exclude all three
open cones for a two-point support level. -/
theorem allowedNormal_of_support_inequalities {P : Set Plane} {C : Plane}
    {c s nx ny : ℝ}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P) (hC : C ∈ P)
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hsc : s < c)
    (hcorner : ∀ p ∈ P,
      c * (p 0 - C 0) + s * (p 1 - C 1) ≤ 0 ∧
      (-s) * (p 0 - C 0) + c * (p 1 - C 1) ≤ 0)
    (hnorm : nx ^ 2 + ny ^ 2 = 1) (hface : HasTwoPointSupport P nx ny) :
    AllowedNormal c s nx ny := by
  exact allowedNormal_of_excluded_cones hcs hs hsc hnorm
    (support_normal_not_in_origin_cone hP hbelow hA hface)
    (support_normal_not_in_bottom_right_cone hP hB hface)
    (support_normal_not_in_corner_cone hcs hC hcorner hface)

/-- An actual square placement with a strict corner frame forces every
unit normal of a two-point support level into the three allowed families.
No classification of a boundary or of its normals is assumed. -/
theorem allowedNormal_of_corner_frame {P : Set Plane} {C : Plane}
    {c s nx ny : ℝ}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P) (hC : C ∈ P)
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hsc : s < c)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (hform : CornerFrameFormula e C c s)
    (hnorm : nx ^ 2 + ny ^ 2 = 1) (hface : HasTwoPointSupport P nx ny) :
    AllowedNormal c s nx ny := by
  exact allowedNormal_of_support_inequalities hP hbelow hA hB hC hcs hs hsc
    (corner_support_inequalities_of_frame e he hform) hnorm hface

/-- An explicit-endpoint version of the actual-placement wrapper. -/
theorem allowedNormal_of_corner_frame_support_points {P : Set Plane} {C X Y : Plane}
    {c s nx ny m : ℝ}
    (hP : P ⊆ unitSquare) (hbelow : P ⊆ {p | p 1 ≤ p 0})
    (hA : corner 0 ∈ P) (hB : corner 1 ∈ P) (hC : C ∈ P)
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hsc : s < c)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P ⊆ unitSquare)
    (hform : CornerFrameFormula e C c s)
    (hnorm : nx ^ 2 + ny ^ 2 = 1)
    (hX : X ∈ P) (hY : Y ∈ P) (hXY : X ≠ Y)
    (hbound : ∀ p ∈ P, nx * p 0 + ny * p 1 ≤ m)
    (hXm : nx * X 0 + ny * X 1 = m) (hYm : nx * Y 0 + ny * Y 1 = m) :
    AllowedNormal c s nx ny := by
  apply allowedNormal_of_corner_frame hP hbelow hA hB hC hcs hs hsc e he hform hnorm
  exact ⟨m, X, Y, hX, hY, hXY, hbound, hXm, hYm⟩

end Puzzling139335.N5
