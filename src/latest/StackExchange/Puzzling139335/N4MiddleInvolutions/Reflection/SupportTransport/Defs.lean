import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Normals.Defs
import StackExchange.Puzzling139335.PlaneIsometries

/-! Complex coordinates for actual supporting-segment normals. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open FaceBounds PlaneIsometries

/-- The outward unit normals of actual supporting segments of length at least
`δ`, written as complex numbers. -/
def complexSupportingNormalsAtLeast (K : Set Plane) (δ : ℝ) : Set ℂ :=
  {z | (z.re, z.im) ∈ supportingNormalsAtLeast K δ}

/-- Complex outward unit normals carrying actual unit supporting segments. -/
abbrev complexUnitSupportingNormals (K : Set Plane) : Set ℂ :=
  complexSupportingNormalsAtLeast K 1

@[simp] theorem mem_complexSupportingNormalsAtLeast {K : Set Plane} {δ : ℝ} {z : ℂ} :
    z ∈ complexSupportingNormalsAtLeast K δ ↔
      (z.re, z.im) ∈ supportingNormalsAtLeast K δ := Iff.rfl

@[simp] theorem complexEquiv_mem_complexSupportingNormalsAtLeast
    {K : Set Plane} {δ : ℝ} {ν : Plane} :
    complexEquiv ν ∈ complexSupportingNormalsAtLeast K δ ↔
      (ν 0, ν 1) ∈ supportingNormalsAtLeast K δ := by
  simp only [mem_complexSupportingNormalsAtLeast, complexEquiv_re, complexEquiv_im]

@[simp] theorem complexEquiv_coordinate_normal (z : ℂ) :
    complexEquiv (!₂[z.re, z.im] : Plane) = z := by
  apply Complex.ext <;> simp

end Puzzling139335.N4MiddleInvolutions.Reflection
