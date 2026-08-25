import StackExchange.Puzzling139335.N5.AlignedFace.RowClassification.Matrix
import StackExchange.Puzzling139335.N5.AlignedFace.RowClassification.VerticalAlignment

/-!
# Actual affine placements sharing the vertical coordinate row

The second row fixes an isometry's first row up to orientation. When both
actual images fit the unit square and each reaches its top side, their
vertical translations agree. Relative to the reference placement, the
second placement is therefore either a horizontal translation or a
horizontal coordinate reflection.
-/

open Set

namespace Puzzling139335.N5.AlignedFace

open PlaneIsometries

/-- The placement formulas have explicit constants determined by the
translation of `eD` and the given reference offset `u`. -/
theorem aligned_affine_forms_of_top_contacts
    {P : Set Plane} (eR eD : Plane ≃ᵃⁱ[ℝ] Plane) {u v c s : ℝ}
    (hRform : ∀ p : Plane, eR p =
      !₂[u - s * p 0 + c * p 1, v + c * p 0 + s * p 1])
    (hD10 : linearMatrix eD 1 0 = c) (hD11 : linearMatrix eD 1 1 = s)
    (hRfit : eR '' P ⊆ unitSquare) (hDfit : eD '' P ⊆ unitSquare)
    (hRtop : ∃ p ∈ P, (eR p) 1 = 1) (hDtop : ∃ p ∈ P, (eD p) 1 = 1) :
    (∀ p : Plane, eD p = !₂[(eR p) 0 + ((eD 0) 0 - u), (eR p) 1]) ∨
      (∀ p : Plane, eD p = !₂[((eD 0) 0 + u) - (eR p) 0, (eR p) 1]) := by
  have hRheight (p : Plane) : (eR p) 1 = v + c * p 0 + s * p 1 := by
    rw [hRform p]
    rfl
  have hvertical : (eD 0) 1 = v := vertical_offset_eq_of_top_contacts eR eD
    hRheight (second_coordinate_of_second_row eD hD10 hD11)
    hRfit hDfit hRtop hDtop
  rcases affine_forms_of_second_row eD hD10 hD11 with hDform | hDform
  · left
    intro p
    apply plane_ext
    · simp [hDform p, hRform p, hvertical]
      ring
    · simp [hDform p, hRform p, hvertical]
  · right
    intro p
    apply plane_ext
    · simp [hDform p, hRform p, hvertical]
      ring
    · simp [hDform p, hRform p, hvertical]

/-- Existential-constant form for subsequent translated/reflected cases. -/
theorem exists_aligned_affine_form_of_top_contacts
    {P : Set Plane} (eR eD : Plane ≃ᵃⁱ[ℝ] Plane) {u v c s : ℝ}
    (hRform : ∀ p : Plane, eR p =
      !₂[u - s * p 0 + c * p 1, v + c * p 0 + s * p 1])
    (hD10 : linearMatrix eD 1 0 = c) (hD11 : linearMatrix eD 1 1 = s)
    (hRfit : eR '' P ⊆ unitSquare) (hDfit : eD '' P ⊆ unitSquare)
    (hRtop : ∃ p ∈ P, (eR p) 1 = 1) (hDtop : ∃ p ∈ P, (eD p) 1 = 1) :
    (∃ δ : ℝ, ∀ p : Plane, eD p = !₂[(eR p) 0 + δ, (eR p) 1]) ∨
      (∃ κ : ℝ, ∀ p : Plane, eD p = !₂[κ - (eR p) 0, (eR p) 1]) := by
  rcases aligned_affine_forms_of_top_contacts eR eD hRform hD10 hD11
    hRfit hDfit hRtop hDtop with htranslation | hreflection
  · exact Or.inl ⟨(eD 0) 0 - u, htranslation⟩
  · exact Or.inr ⟨(eD 0) 0 + u, hreflection⟩

end Puzzling139335.N5.AlignedFace
