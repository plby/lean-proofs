import StackExchange.Puzzling139335.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Supporting right corners

A supporting right corner is a point of a planar set at which the whole set
lies in a right-angle wedge.  Its two outward normals are orthonormal.  This
definition does not require convexity or any boundary regularity.
-/

open Set

namespace Puzzling139335

noncomputable section

/-- A witness that a point is a supporting right corner of a planar set. -/
structure SupportCorner (P : Set Plane) (v : Plane) where
  mem : v ∈ P
  firstNormal : Plane
  secondNormal : Plane
  norm_firstNormal : ‖firstNormal‖ = 1
  norm_secondNormal : ‖secondNormal‖ = 1
  orthogonal : inner ℝ firstNormal secondNormal = 0
  first_support : ∀ x ∈ P, inner ℝ firstNormal (x - v) ≤ 0
  second_support : ∀ x ∈ P, inner ℝ secondNormal (x - v) ≤ 0

/-- The geometric property, without a chosen pair of outward normals. -/
def IsSupportCorner (P : Set Plane) (v : Plane) : Prop := Nonempty (SupportCorner P v)

namespace SupportCorner

variable {P Q : Set Plane} {v : Plane}

/-- The outward bisector, whose norm is the square root of two. -/
def bisector (h : SupportCorner P v) : Plane := h.firstNormal + h.secondNormal

theorem bisector_norm_sq (h : SupportCorner P v) : ‖h.bisector‖ ^ 2 = (2 : ℝ) := by
  norm_num [bisector, norm_add_sq_real, h.norm_firstNormal, h.norm_secondNormal, h.orthogonal]

theorem normals_orthonormal (h : SupportCorner P v) :
    Orthonormal ℝ (![h.firstNormal, h.secondNormal] : Fin 2 → Plane) := by
  simp [orthonormal_vecCons_iff, h.norm_firstNormal, h.norm_secondNormal, h.orthogonal]

/-- In the plane the two orthonormal normals form an orthonormal basis. -/
def normalBasis (h : SupportCorner P v) : OrthonormalBasis (Fin 2) ℝ Plane :=
  OrthonormalBasis.mk h.normals_orthonormal
    (h.normals_orthonormal.linearIndependent.span_eq_top_of_card_eq_finrank
      (by simp [Plane])).ge

@[simp] theorem normalBasis_zero (h : SupportCorner P v) :
    h.normalBasis 0 = h.firstNormal := by
  simp [normalBasis, OrthonormalBasis.coe_mk]

@[simp] theorem normalBasis_one (h : SupportCorner P v) :
    h.normalBasis 1 = h.secondNormal := by
  simp [normalBasis, OrthonormalBasis.coe_mk]

theorem normal_projections_sq (h : SupportCorner P v) (u : Plane) :
    (inner ℝ h.firstNormal u) ^ 2 + (inner ℝ h.secondNormal u) ^ 2 = ‖u‖ ^ 2 := by
  simpa [Fin.sum_univ_two] using h.normalBasis.sum_sq_inner_right u

/-- The support inequalities make the outward bisector project at most
minus the displacement's norm in every direction toward the set. -/
theorem bisector_projection (h : SupportCorner P v) {x : Plane} (hx : x ∈ P) :
    inner ℝ h.bisector (x - v) ≤ -‖x - v‖ := by
  have ha := h.first_support x hx
  have hb := h.second_support x hx
  have hp := h.normal_projections_sq (x - v)
  have hab : 0 ≤ inner ℝ h.firstNormal (x - v) * inner ℝ h.secondNormal (x - v) :=
    mul_nonneg_of_nonpos_of_nonpos ha hb
  have hsum : 0 ≤ -(inner ℝ h.firstNormal (x - v) +
      inner ℝ h.secondNormal (x - v)) := by linarith
  have hsq : ‖x - v‖ ^ 2 ≤
      (-(inner ℝ h.firstNormal (x - v) + inner ℝ h.secondNormal (x - v))) ^ 2 := by
    nlinarith
  have hnorm := (sq_le_sq₀ (norm_nonneg (x - v)) hsum).mp hsq
  rw [bisector, inner_add_left]
  linarith

/-- Restricting a supporting wedge to a smaller set preserves its corner
when the corner itself remains in the smaller set. -/
def mono (h : SupportCorner P v) (hQP : Q ⊆ P) (hvQ : v ∈ Q) : SupportCorner Q v where
  mem := hvQ
  firstNormal := h.firstNormal
  secondNormal := h.secondNormal
  norm_firstNormal := h.norm_firstNormal
  norm_secondNormal := h.norm_secondNormal
  orthogonal := h.orthogonal
  first_support := fun x hx => h.first_support x (hQP hx)
  second_support := fun x hx => h.second_support x (hQP hx)

/-- Supporting right corners are transported by every affine isometry,
including reflections. -/
def map (h : SupportCorner P v) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    SupportCorner (e '' P) (e v) where
  mem := mem_image_of_mem e h.mem
  firstNormal := e.linearIsometryEquiv h.firstNormal
  secondNormal := e.linearIsometryEquiv h.secondNormal
  norm_firstNormal := by simpa using h.norm_firstNormal
  norm_secondNormal := by simpa using h.norm_secondNormal
  orthogonal := by simpa using h.orthogonal
  first_support := by
    rintro y ⟨x, hx, rfl⟩
    have hsub : e x - e v = e.linearIsometryEquiv (x - v) := (e.map_vsub x v).symm
    rw [hsub, e.linearIsometryEquiv.inner_map_map]
    exact h.first_support x hx
  second_support := by
    rintro y ⟨x, hx, rfl⟩
    have hsub : e x - e v = e.linearIsometryEquiv (x - v) := (e.map_vsub x v).symm
    rw [hsub, e.linearIsometryEquiv.inner_map_map]
    exact h.second_support x hx

end SupportCorner

/-- Each vertex of the unit square has the two evident outward coordinate
normals. -/
def squareSupportCorner (j : Fin 4) : SupportCorner unitSquare (corner j) where
  mem := corner_mem_unitSquare j
  firstNormal := !₂[if j = 1 ∨ j = 2 then 1 else -1, 0]
  secondNormal := !₂[0, if j = 2 ∨ j = 3 then 1 else -1]
  norm_firstNormal := by
    by_cases hj : j = 1 ∨ j = 2 <;>
      norm_num [hj, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  norm_secondNormal := by
    by_cases hj : j = 2 ∨ j = 3 <;>
      norm_num [hj, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  orthogonal := by simp [Schoenflies.Plane.inner_eq]
  first_support := by
    intro x hx
    by_cases hj : j = 1 ∨ j = 2
    · simpa [Schoenflies.Plane.inner_eq, corner, hj] using sub_nonpos.mpr hx.1.2
    · simpa [Schoenflies.Plane.inner_eq, corner, hj] using neg_nonpos.mpr hx.1.1
  second_support := by
    intro x hx
    by_cases hj : j = 2 ∨ j = 3
    · simpa [Schoenflies.Plane.inner_eq, corner, hj] using sub_nonpos.mpr hx.2.2
    · simpa [Schoenflies.Plane.inner_eq, corner, hj] using neg_nonpos.mpr hx.2.1

/-- A corner reached by an isometric copy of a set pulls back to a supporting
right corner of the original set. -/
theorem isSupportCorner_preimage {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hSubset : e '' P ⊆ unitSquare) (j : Fin 4) (hj : corner j ∈ e '' P) :
    IsSupportCorner P (e.symm (corner j)) := by
  have hFrame := ((squareSupportCorner j).mono hSubset hj).map e.symm
  have hImage : e.symm '' (e '' P) = P := by
    rw [Set.image_image]
    simp
  rw [hImage] at hFrame
  exact ⟨hFrame⟩

end

end Puzzling139335
