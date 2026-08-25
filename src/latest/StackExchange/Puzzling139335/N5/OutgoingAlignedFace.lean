import StackExchange.Puzzling139335.N5.Prepared
import StackExchange.Puzzling139335.N5.FourthSide.Contacts
import StackExchange.Puzzling139335.N5.OutgoingAlignedFace.Metric

/-!
# The outgoing aligned top normal is impossible

The actual right-side endpoints of the singleton piece pull back to two
source points a distance `1 - b` apart. If the fourth placement has that
right-side normal as its top row, both points must map to its actual top
contact interval `[b,m]`. That interval is strictly shorter.

Only actual endpoint membership, containment, and isometry are used; no
assumption that a source supporting face is a whole segment is needed.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

namespace OutgoingAlignedFace

private theorem inverse_mem {P Q : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' P = Q) {x : Plane} (hx : x ∈ Q) : e.symm x ∈ P := by
  obtain ⟨p, hp, hpx⟩ := he.symm ▸ hx
  rw [← hpx, e.symm_apply_apply]
  exact hp

/-- The actual source points of the singleton's right-side contacts all
map onto the fourth piece's top side in the outgoing aligned case. -/
theorem top_of_right_contact {d : SquareDissection} (q : Prepared d)
    (h10 : linearMatrix q.eD 1 0 = -Real.sin q.θ)
    (h11 : linearMatrix q.eD 1 1 = Real.cos q.θ)
    {p : Plane} (hp : p ∈ d.piece 0) (hright : q.eR p 0 = 1) :
    q.eD p 1 = 1 := by
  have hDfit : q.eD '' d.piece 0 ⊆ unitSquare := by
    rw [q.image_D]
    exact d.piece_subset 3
  have hcontact :
      (q.eD '' d.piece 0 ∩ {x : Plane | x 1 = 1}).Nonempty := by
    refine ⟨Schoenflies.Plane.mk q.b 1, ?_, rfl⟩
    rw [q.image_D]
    exact (q.top_fourth q.b).mpr ⟨le_rfl, q.b_lt_m.le⟩
  apply FourthSide.coordinate_eq_one_of_maximizer q.eD hDfit hp hcontact
  intro x hx
  rw [h10, h11]
  have hbound : q.eR x 0 ≤ 1 := by
    exact (d.piece_subset 2 (q.image_R ▸ mem_image_of_mem q.eR hx)).1.2
  have hxform := congrArg (fun z : Plane => z 0) (q.R_form x)
  have hpform := congrArg (fun z : Plane => z 0) (q.R_form p)
  change q.eR x 0 = 1 + Real.sin q.θ * q.C 0 - Real.cos q.θ * q.C 1 -
    Real.sin q.θ * x 0 + Real.cos q.θ * x 1 at hxform
  change q.eR p 0 = 1 + Real.sin q.θ * q.C 0 - Real.cos q.θ * q.C 1 -
    Real.sin q.θ * p 0 + Real.cos q.θ * p 1 at hpform
  linarith only [hbound, hxform, hpform, hright]

end OutgoingAlignedFace

/-- The fourth piece cannot put the singleton's outgoing supporting normal
along the square's top side. -/
theorem Prepared.outgoing_aligned_impossible {d : SquareDissection} (q : Prepared d)
    (h10 : linearMatrix q.eD 1 0 = -Real.sin q.θ)
    (h11 : linearMatrix q.eD 1 1 = Real.cos q.θ) : False := by
  let E : Plane := q.eR.symm (Schoenflies.Plane.mk 1 q.b)
  have hC : q.C ∈ d.piece 0 := by
    rw [q.C_eq]
    exact OutgoingAlignedFace.inverse_mem q.eR q.image_R q.normalized.top_right
  have hE : E ∈ d.piece 0 := by
    exact OutgoingAlignedFace.inverse_mem q.eR q.image_R
      ((q.right_singleton q.b).mpr ⟨le_rfl, q.b_lt_m.le.trans q.m_lt_one.le⟩)
  have hRC : q.eR q.C = corner 2 := by
    rw [q.C_eq, q.eR.apply_symm_apply]
  have hRE : q.eR E = Schoenflies.Plane.mk 1 q.b := q.eR.apply_symm_apply _
  have hRCright : q.eR q.C 0 = 1 := by
    rw [hRC]
    norm_num [corner, Fin.ext_iff]
  have hREright : q.eR E 0 = 1 := by rw [hRE]; rfl
  have hDCtop := OutgoingAlignedFace.top_of_right_contact q h10 h11 hC hRCright
  have hDEtop := OutgoingAlignedFace.top_of_right_contact q h10 h11 hE hREright
  have hbounds (p : Plane) (hp : p ∈ d.piece 0) (htop : q.eD p 1 = 1) :
      q.b ≤ q.eD p 0 ∧ q.eD p 0 ≤ q.m := by
    apply (q.top_fourth (q.eD p 0)).mp
    have heq : Schoenflies.Plane.mk (q.eD p 0) 1 = q.eD p := by
      apply plane_ext
      · rfl
      · exact htop.symm
    rw [heq]
    exact q.image_D ▸ mem_image_of_mem q.eD hp
  have hDCbounds := hbounds q.C hC hDCtop
  have hDEbounds := hbounds E hE hDEtop
  have hdist : dist (q.eD q.C) (q.eD E) ^ 2 = (1 - q.b) ^ 2 := by
    rw [q.eD.isometry.dist_eq, ← q.eR.isometry.dist_eq q.C E, hRC, hRE]
    norm_num [plane_dist_sq, corner, Schoenflies.Plane.mk, Fin.ext_iff]
  have hle := OutgoingAlignedFace.top_interval_dist_sq_le
    hDCtop hDEtop hDCbounds.1 hDCbounds.2 hDEbounds.1 hDEbounds.2
  have hlt := OutgoingAlignedFace.interval_length_sq_lt q.b_lt_m q.m_lt_one
  rw [hdist] at hle
  exact (not_lt_of_ge hle) hlt

end Puzzling139335.N5
