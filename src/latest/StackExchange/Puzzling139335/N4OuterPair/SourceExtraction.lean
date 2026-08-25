import StackExchange.Puzzling139335.N4OuterPair.UpperNormals
import StackExchange.Puzzling139335.N4OuterPair.UpperAngle
import StackExchange.Puzzling139335.N4OuterPair.SourceEndpoints
import StackExchange.Puzzling139335.N4OuterPair.PlacementFrames
import StackExchange.Puzzling139335.N4OuterPair.GapOwnership
import StackExchange.Puzzling139335.SourceFaceBridge

/-!
# Extracting supported-source data from actual side-gap owners

The angles are obtained from the actual isometries' outward normal rows.
The two source face centers are preimages of the physical gap midpoints.
A common horizontal reflection normalizes the right placement's parity.
All four source face endpoints are then recovered from actual gap contacts.
No interface property or angle distinctness is needed for this construction.
-/

open Set Puzzling139335.PlaneIsometries

namespace Puzzling139335.N4OuterPair

private theorem side_contact_nontrivial_of_gap {d : SquareDissection} {i : Fin 4}
    {x c : ℝ} (hc : c < 1 / 2)
    (hgap : ∀ y ∈ Icc c (1 - c), Schoenflies.Plane.mk x y ∈ d.piece i) :
    (d.piece i ∩ {p : Plane | p 0 = x}).Nontrivial := by
  have hlt : c < 1 - c := by linarith only [hc]
  refine ⟨Schoenflies.Plane.mk x c, ⟨hgap c ⟨le_rfl, hlt.le⟩, rfl⟩,
    Schoenflies.Plane.mk x (1 - c), ⟨hgap (1 - c) ⟨hlt.le, le_rfl⟩, rfl⟩, ?_⟩
  intro heq
  exact hlt.ne (congrArg (fun p : Plane => p 1) heq)

private theorem postReflect_gap_image (σ : Bool) {P : Set Plane} {x c : ℝ}
    (hgap : ∀ y ∈ Icc c (1 - c), Schoenflies.Plane.mk x y ∈ P) :
    ∀ y ∈ Icc c (1 - c), Schoenflies.Plane.mk x y ∈ postReflect σ '' P := by
  intro y hy
  refine ⟨postReflect σ (Schoenflies.Plane.mk x y), ?_, postReflect_involutive σ _⟩
  rw [postReflect_side_point]
  cases σ
  · exact hgap y hy
  · exact hgap (1 - y) ⟨by linarith only [hy.2], by linarith only [hy.1]⟩

namespace Configuration

variable {d : SquareDissection}

/-- Actual congruences owning the full side gaps supply the complete
`UpperSupportedSource` model, up to a common horizontal reflection. -/
theorem source_of_owned_gaps (h : Configuration d) (hc : d.HasProtectedCenter)
    {iR iL : Fin 4} (hiR : iR = 2 ∨ iR = 3) (hiL : iL = 2 ∨ iL = 3)
    (eR eL : Plane ≃ᵃⁱ[ℝ] Plane)
    (heR : eR '' d.piece 0 = d.piece iR) (heL : eL '' d.piece 0 = d.piece iL)
    {a b : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hleft : Schoenflies.Plane.mk 0 a ∈ d.piece 0)
    (hright : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hRgap : ∀ y ∈ Icc b (1 - b), Schoenflies.Plane.mk 1 y ∈ d.piece iR)
    (hLgap : ∀ y ∈ Icc a (1 - a), Schoenflies.Plane.mk 0 y ∈ d.piece iL) :
    ∃ g : SourceFaceBridge.UpperFaceData, ∃ rev σ : Bool,
      SourceFaceBridge.UpperSupportedSource g rev (d.piece 0) ∧
      g.a = a ∧ g.b = b ∧ g.φ ≠ Real.pi / 2 ∧ g.ψ ≠ Real.pi / 2 ∧
      g.right '' d.piece 0 = postReflect σ '' d.piece iR ∧
      g.left rev '' d.piece 0 = postReflect σ '' d.piece iL := by
  have hRnontriv := side_contact_nontrivial_of_gap hb hRgap
  have hLnontriv := side_contact_nontrivial_of_gap ha hLgap
  have hRy := h.right_contact_normal_up hc hiR eR heR hRnontriv
  have hLy := h.left_contact_normal_up hc hiL eL heL hLnontriv
  have hRn := h.middle_normal_nonaxis hc hiR eR heR
  have hLn := h.middle_normal_nonaxis hc hiL eL heL
  have hRcircle : linearMatrix eR 0 0 ^ 2 + linearMatrix eR 0 1 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot eR 0 0
  have hLcircle : (-linearMatrix eL 0 0) ^ 2 + (-linearMatrix eL 0 1) ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot eL 0 0
  obtain ⟨φ, hφ0, hφπ, hφaxis, hφc, hφs⟩ :=
    exists_upper_angle (linearMatrix eR 0 0) (linearMatrix eR 0 1) hRy hRcircle hRn.1
  obtain ⟨ψ, hψ0, hψπ, hψaxis, hψc, hψs⟩ :=
    exists_upper_angle (-linearMatrix eL 0 0) (-linearMatrix eL 0 1)
      (neg_pos.mpr hLy) hLcircle (neg_ne_zero.mpr hLn.1)
  let g : SourceFaceBridge.UpperFaceData :=
    ⟨φ, ψ, a, b, eR.symm (Schoenflies.Plane.mk 1 (1 / 2)),
      eL.symm (Schoenflies.Plane.mk 0 (1 / 2))⟩
  have hRM : eR g.M₁ = Schoenflies.Plane.mk 1 (1 / 2) := eR.apply_symm_apply _
  have hLM : eL g.M₂ = Schoenflies.Plane.mk 0 (1 / 2) := eL.apply_symm_apply _
  obtain ⟨σ, rev, hRfun, hLfun⟩ := exists_normalized_placements g eR eL hRM hLM
    hφc.symm hφs.symm (by change _ = -Real.cos ψ; linarith only [hψc])
    (by change _ = -Real.sin ψ; linarith only [hψs])
  have hRimage : g.right '' d.piece 0 = postReflect σ '' d.piece iR := by
    rw [← hRfun, Set.image_comp (postReflect σ) eR (d.piece 0), heR]
  have hLimage : g.left rev '' d.piece 0 = postReflect σ '' d.piece iL := by
    rw [← hLfun, Set.image_comp (postReflect σ) eL (d.piece 0), heL]
  have hRg : ∀ y ∈ Icc b (1 - b), Schoenflies.Plane.mk 1 y ∈ g.right '' d.piece 0 := by
    rw [hRimage]
    exact postReflect_gap_image σ hRgap
  have hLg : ∀ y ∈ Icc a (1 - a), Schoenflies.Plane.mk 0 y ∈ g.left rev '' d.piece 0 := by
    rw [hLimage]
    exact postReflect_gap_image σ hLgap
  have hba : b ≤ 1 - b := by linarith only [hb]
  have haa : a ≤ 1 - a := by linarith only [ha]
  have hRends : Schoenflies.Plane.mk 1 g.b ∈ g.right '' d.piece 0 ∧
      Schoenflies.Plane.mk 1 (1 - g.b) ∈ g.right '' d.piece 0 :=
    ⟨hRg b ⟨le_rfl, hba⟩, hRg (1 - b) ⟨hba, le_rfl⟩⟩
  have hLends : Schoenflies.Plane.mk 0 g.a ∈ g.left rev '' d.piece 0 ∧
      Schoenflies.Plane.mk 0 (1 - g.a) ∈ g.left rev '' d.piece 0 :=
    ⟨hLg a ⟨le_rfl, haa⟩, hLg (1 - a) ⟨haa, le_rfl⟩⟩
  obtain ⟨hF₁m, hF₁p, hF₂m, hF₂p⟩ :=
    g.face_endpoints_mem_of_gap_contacts rev hRends hLends
  refine ⟨g, rev, σ, ?_, rfl, rfl, hφaxis, hψaxis, hRimage, hLimage⟩
  exact
    { phi_pos := hφ0
      phi_lt_pi := hφπ
      psi_pos := hψ0
      psi_lt_pi := hψπ
      a_pos := ha0
      a_lt_half := ha
      b_pos := hb0
      b_lt_half := hb
      source_subset := h.outer_halves.1
      base_mem := fun _ ht => h.bottom_point_mem hc ht
      left_top_mem := hleft
      right_top_mem := hright
      face₁minus_mem := hF₁m
      face₁plus_mem := hF₁p
      face₂minus_mem := hF₂m
      face₂plus_mem := hF₂p
      right_fits := by
        intro p hp
        have hm : g.right p ∈ postReflect σ '' d.piece iR :=
          hRimage ▸ mem_image_of_mem g.right hp
        obtain ⟨q, hq, heq⟩ := hm
        rw [← heq]
        simpa only [postReflect_mem_unitSquare] using d.piece_subset iR hq
      left_fits := by
        intro p hp
        have hm : g.left rev p ∈ postReflect σ '' d.piece iL :=
          hLimage ▸ mem_image_of_mem (g.left rev) hp
        obtain ⟨q, hq, heq⟩ := hm
        rw [← heq]
        simpa only [postReflect_mem_unitSquare] using d.piece_subset iL hq }

/-- Strict actual side-contact heights determine distinct middle gap owners
and a supported-source model for their actual congruence images. -/
theorem exists_source_of_strict_contact_heights (h : Configuration d)
    (hc : d.HasProtectedCenter) {a b : ℝ}
    (ha0 : 0 < a) (ha : a < 1 / 2) (hb0 : 0 < b) (hb : b < 1 / 2)
    (hleft : ∀ y : ℝ, Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b) :
    ∃ iR iL : Fin 4, ((iR = 2 ∧ iL = 3) ∨ (iR = 3 ∧ iL = 2)) ∧
      ∃ g : SourceFaceBridge.UpperFaceData, ∃ rev σ : Bool,
        SourceFaceBridge.UpperSupportedSource g rev (d.piece 0) ∧
        g.a = a ∧ g.b = b ∧ g.φ ≠ Real.pi / 2 ∧ g.ψ ≠ Real.pi / 2 ∧
        g.right '' d.piece 0 = postReflect σ '' d.piece iR ∧
        g.left rev '' d.piece 0 = postReflect σ '' d.piece iL := by
  have hleftPoint := (hleft a).mpr ⟨ha0.le, le_rfl⟩
  have hrightPoint := (hright b).mpr ⟨hb0.le, le_rfl⟩
  rcases h.side_gap_owners hc ha0.le ha hb0.le hb hleft hright with
    ⟨hL2, hR3⟩ | ⟨hL3, hR2⟩
  · obtain ⟨eR, heR⟩ := d.congruent 0 3
    obtain ⟨eL, heL⟩ := d.congruent 0 2
    refine ⟨3, 2, Or.inr ⟨rfl, rfl⟩, ?_⟩
    exact h.source_of_owned_gaps hc (Or.inr rfl) (Or.inl rfl) eR eL heR heL
      ha0 ha hb0 hb hleftPoint hrightPoint hR3 hL2
  · obtain ⟨eR, heR⟩ := d.congruent 0 2
    obtain ⟨eL, heL⟩ := d.congruent 0 3
    refine ⟨2, 3, Or.inl ⟨rfl, rfl⟩, ?_⟩
    exact h.source_of_owned_gaps hc (Or.inl rfl) (Or.inr rfl) eR eL heR heL
      ha0 ha hb0 hb hleftPoint hrightPoint hR2 hL3

end Configuration

/-- Once an actual nontrivial middle interface has been derived, the
extracted source normals must coincide.  All distinct-angle cases contradict
the actual disjoint Jordan interiors via the complete source-face theorem. -/
theorem normal_angles_eq_of_actual_interface (d : SquareDissection)
    {g : SourceFaceBridge.UpperFaceData} {rev σ : Bool} {iR iL : Fin 4}
    (hi : iR ≠ iL)
    (hsource : SourceFaceBridge.UpperSupportedSource g rev (d.piece 0))
    (hφaxis : g.φ ≠ Real.pi / 2) (hψaxis : g.ψ ≠ Real.pi / 2)
    (hRimage : g.right '' d.piece 0 = postReflect σ '' d.piece iR)
    (hLimage : g.left rev '' d.piece 0 = postReflect σ '' d.piece iL)
    (hcommon : (d.piece iR ∩ d.piece iL).Nontrivial) : g.φ = g.ψ := by
  have hcommon' : ((g.right '' d.piece 0) ∩ (g.left rev '' d.piece 0)).Nontrivial := by
    rw [hRimage, hLimage, ← image_inter (postReflect σ).injective]
    exact hcommon.image (postReflect σ).injective
  have hdis : Disjoint (interior (g.right '' d.piece 0))
      (interior (g.left rev '' d.piece 0)) := by
    rw [hRimage, hLimage, interior_image_affineIsometry, interior_image_affineIsometry]
    exact Set.disjoint_image_of_injective (postReflect σ).injective (d.disjoint_interiors hi)
  by_contra hne
  exact hsource.not_disjoint_interiors (d.jordan 0) hcommon' hφaxis hψaxis hne hdis

end Puzzling139335.N4OuterPair
