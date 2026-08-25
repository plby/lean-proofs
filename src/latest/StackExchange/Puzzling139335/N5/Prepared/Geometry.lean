import StackExchange.Puzzling139335.N5.Prepared
import StackExchange.Puzzling139335.N5.RightArm
import StackExchange.Puzzling139335.N5.TopContacts.Bounds
import StackExchange.Puzzling139335.N5.FourthSide.Contacts
import StackExchange.Puzzling139335.N5Facet.Trigonometry

/-!
# Geometric consequences of the actual prepared configuration

The prepared data contain actual placements and exact side contacts.
Their inverse endpoints are therefore points of the source piece, and
square containment supplies the supporting inequalities used below.
-/

open Set

namespace Puzzling139335.N5.Prepared

open PlaneIsometries

variable {d : SquareDissection} (q : Prepared d)

theorem unit : Real.cos q.θ ^ 2 + Real.sin q.θ ^ 2 = 1 := by
  nlinarith only [Real.sin_sq_add_cos_sq q.θ]

theorem cos_pos : 0 < Real.cos q.θ :=
  (N5Facet.acute_trig_pos q.angle.1 q.angle.2).1

theorem sin_pos : 0 < Real.sin q.θ :=
  (N5Facet.acute_trig_pos q.angle.1 q.angle.2).2

theorem sin_lt_cos : Real.sin q.θ < Real.cos q.θ :=
  N5Facet.sin_lt_cos q.angle.1 q.angle.2

theorem C_height_lt_cos : q.C 1 < Real.cos q.θ :=
  q.C_height_lt_first.trans q.C_first_lt_cos

theorem b_lt_one : q.b < 1 := by
  linarith only [q.b_lt_half]

theorem m_pos : 0 < q.m := q.b_pos.trans q.b_lt_m

theorem fit_R : q.eR '' d.piece 0 ⊆ unitSquare := by
  rw [q.image_R]
  exact d.piece_subset 2

theorem fit_D : q.eD '' d.piece 0 ⊆ unitSquare := by
  rw [q.image_D]
  exact d.piece_subset 3

private theorem inverse_mem {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q) {x : Plane} (hx : x ∈ Q) :
    e.symm x ∈ P := by
  have hximage : x ∈ e '' P := by rw [he]; exact hx
  obtain ⟨p, hp, hpx⟩ := hximage
  rw [← hpx, e.symm_apply_apply]
  exact hp

theorem C_mem : q.C ∈ d.piece 0 := by
  rw [q.C_eq]
  exact inverse_mem q.eR q.image_R q.normalized.top_right

theorem right_contact_mem : Schoenflies.Plane.mk 1 q.b ∈ d.piece 0 :=
  (q.right_source q.b).mpr ⟨q.b_pos.le, le_rfl⟩

/-- The preimage of the lower endpoint of the singleton's right-side
interval is an actual source point on the outgoing arm. -/
theorem right_arm_endpoint_mem :
    !₂[q.C 0 - (1 - q.b) * Real.cos q.θ,
       q.C 1 - (1 - q.b) * Real.sin q.θ] ∈ d.piece 0 := by
  have hpre := inverse_mem q.eR q.image_R
    ((q.right_singleton q.b).mpr ⟨le_rfl, q.b_lt_one.le⟩)
  rwa [swapped_inverse_right_point q.unit q.R_form] at hpre

/-- The preimage of the left endpoint of the singleton's top interval
is an actual source point on the incoming arm. -/
theorem incoming_arm_endpoint_mem :
    !₂[q.C 0 + (1 - q.m) * Real.sin q.θ,
       q.C 1 - (1 - q.m) * Real.cos q.θ] ∈ d.piece 0 := by
  have hpre := inverse_mem q.eR q.image_R
    ((q.top_singleton q.m).mpr ⟨le_rfl, q.m_lt_one.le⟩)
  rwa [swapped_inverse_top_point q.unit q.R_form] at hpre

/-- Both endpoints of the fourth piece's top interval pull back to
actual points of the prototype. -/
theorem D_left_mem : q.eD.symm (Schoenflies.Plane.mk q.b 1) ∈ d.piece 0 :=
  inverse_mem q.eD q.image_D ((q.top_fourth q.b).mpr ⟨le_rfl, q.b_lt_m.le⟩)

theorem D_right_mem : q.eD.symm (Schoenflies.Plane.mk q.m 1) ∈ d.piece 0 :=
  inverse_mem q.eD q.image_D ((q.top_fourth q.m).mpr ⟨q.b_lt_m.le, le_rfl⟩)

/-- The two shifted corner-support inequalities follow from the actual
singleton placement and containment of its image in the square. -/
theorem corner_support (p : Plane) (hp : p ∈ d.piece 0) :
    Real.cos q.θ * (p 0 - q.C 0) + Real.sin q.θ * (p 1 - q.C 1) ≤ 0 ∧
      (-Real.sin q.θ) * (p 0 - q.C 0) + Real.cos q.θ * (p 1 - q.C 1) ≤ 0 := by
  have hform : CornerPlacementForm q.eR q.C (Real.cos q.θ) (Real.sin q.θ) :=
    Or.inr q.R_form
  have hs := hform.support q.fit_R hp
  constructor <;> nlinarith only [hs.1, hs.2]

/-- A source point which maps onto the fourth piece's top supporting line
maximizes the second matrix row over every actual source point. -/
theorem fourth_top_support {X : Plane} (_hX : X ∈ d.piece 0)
    (hXtop : q.eD X 1 = 1) (p : Plane) (hp : p ∈ d.piece 0) :
    linearMatrix q.eD 1 0 * (p 0 - X 0) +
      linearMatrix q.eD 1 1 * (p 1 - X 1) ≤ 0 := by
  have hfit := (q.fit_D (mem_image_of_mem q.eD hp)).2.2
  rw [FourthSide.affine_coordinate q.eD p 1] at hfit
  rw [FourthSide.affine_coordinate q.eD X 1] at hXtop
  nlinarith only [hfit, hXtop]

end Puzzling139335.N5.Prepared
