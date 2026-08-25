import StackExchange.Puzzling139335.ThreeCorners.Rays
import StackExchange.Puzzling139335.SquareSymmetry.CornerRigidity

/-!
# Actual square placements in an inward corner frame

An isometry taking a frame vertex to a square corner and its diagonal
half-step to the square center takes the two inward coordinates to the
two square coordinates, possibly interchanging them. This translates
actual bottom-side contacts into level-one supporting-face contacts.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners SquareSymmetry PlaneIsometries

noncomputable section

/-- Euclidean coordinates in the positively oriented inward frame. -/
def frameCoordinates (v : Plane) (θ : ℝ) (p : Plane) : Plane :=
  (rayBasis θ).repr (p - v)

@[simp] theorem frameCoordinates_zero (v p : Plane) (θ : ℝ) :
    frameCoordinates v θ p 0 = inner ℝ (ray θ) (p - v) := by
  simp only [frameCoordinates, OrthonormalBasis.repr_apply_apply, rayBasis_zero]

@[simp] theorem frameCoordinates_one (v p : Plane) (θ : ℝ) :
    frameCoordinates v θ p 1 = inner ℝ (perpRay θ) (p - v) := by
  simp only [frameCoordinates, OrthonormalBasis.repr_apply_apply, rayBasis_one]

/-- The placement from inward coordinates into the source plane. -/
def framePlacement (v : Plane) (θ : ℝ) : Plane ≃ᵃⁱ[ℝ] Plane :=
  (rayBasis θ).repr.symm.toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.vaddConst ℝ v)

theorem framePlacement_apply (v : Plane) (θ : ℝ) (p : Plane) :
    framePlacement v θ p = v + p 0 • ray θ + p 1 • perpRay θ := by
  have h := (rayBasis θ).sum_repr_symm p
  simp only [Fin.sum_univ_two, rayBasis_zero, rayBasis_one] at h
  change (rayBasis θ).repr.symm p + v = _
  rw [← h]
  abel

@[simp] theorem framePlacement_zero (v : Plane) (θ : ℝ) :
    framePlacement v θ 0 = v := by
  simp [framePlacement_apply]

theorem framePlacement_center (v : Plane) (θ : ℝ) :
    framePlacement v θ squareCenter = v + (1 / 2 : ℝ) • (ray θ + perpRay θ) := by
  rw [framePlacement_apply]
  simp only [squareCenter_apply_zero, squareCenter_apply_one, smul_add, add_assoc]

theorem framePlacement_frameCoordinates (v p : Plane) (θ : ℝ) :
    framePlacement v θ (frameCoordinates v θ p) = p := by
  change (rayBasis θ).repr.symm ((rayBasis θ).repr (p - v)) + v = p
  rw [(rayBasis θ).repr.symm_apply_apply]
  abel

/-- The diagonal through the origin leaves only identity or interchange
as possibilities for a normalized affine isometry. -/
theorem coordinate_form_of_origin_and_center
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hzero : e 0 = 0)
    (hcenter : e squareCenter = squareCenter) :
    (∀ p, e p = p) ∨ (∀ p, e p = !₂[p 1, p 0]) := by
  obtain ⟨c, s, _, hform | hform⟩ := affine_coordinate_classification e
  · have hc₀ := congrArg (fun p : Plane => p 0) ((hform squareCenter).symm.trans hcenter)
    have hc₁ := congrArg (fun p : Plane => p 1) ((hform squareCenter).symm.trans hcenter)
    norm_num [directCoordinates, squareCenter, hzero] at hc₀ hc₁
    have hc : c = 1 := by linarith
    have hs : s = 0 := by linarith
    refine Or.inl fun p => ?_
    rw [hform]
    ext i
    fin_cases i <;> simp [directCoordinates, hzero, hc, hs]
  · have hc₀ := congrArg (fun p : Plane => p 0) ((hform squareCenter).symm.trans hcenter)
    have hc₁ := congrArg (fun p : Plane => p 1) ((hform squareCenter).symm.trans hcenter)
    norm_num [reversingCoordinates, squareCenter, hzero] at hc₀ hc₁
    have hc : c = 0 := by linarith
    have hs : s = 1 := by linarith
    refine Or.inr fun p => ?_
    rw [hform]
    ext i
    fin_cases i <;> simp [reversingCoordinates, hzero, hc, hs]

/-- An actual corner placement is exactly the inward coordinate frame,
possibly with its two coordinates interchanged. -/
theorem corner_frame_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (v : Plane) (θ : ℝ) (j : Fin 4) (hv : e v = corner j)
    (hc : e (v + (1 / 2 : ℝ) • (ray θ + perpRay θ)) = squareCenter) :
    (∀ p, cornerFlip j (e p) = frameCoordinates v θ p) ∨
      (∀ p, cornerFlip j (e p) =
        !₂[frameCoordinates v θ p 1, frameCoordinates v θ p 0]) := by
  let g := ((framePlacement v θ).trans e).trans (cornerFlip j)
  have hg (p : Plane) : g p = cornerFlip j (e (framePlacement v θ p)) := rfl
  have hgzero : g 0 = 0 := by
    rw [hg, framePlacement_zero, hv, cornerFlip_corner]
  have hgcenter : g squareCenter = squareCenter := by
    rw [hg, framePlacement_center, hc, cornerFlip_center]
  rcases coordinate_form_of_origin_and_center g hgzero hgcenter with hid | hswap
  · refine Or.inl fun p => ?_
    have h := hid (frameCoordinates v θ p)
    simpa only [hg, framePlacement_frameCoordinates] using h
  · refine Or.inr fun p => ?_
    have h := hswap (frameCoordinates v θ p)
    simpa only [hg, framePlacement_frameCoordinates] using h

/-- Both inward frame coordinates are between zero and one whenever the
actual placed point lies in the square. -/
theorem inward_coordinates_mem_Icc (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (v : Plane) (θ : ℝ) (j : Fin 4) (hv : e v = corner j)
    (hc : e (v + (1 / 2 : ℝ) • (ray θ + perpRay θ)) = squareCenter)
    {p : Plane} (hp : e p ∈ unitSquare) :
    inner ℝ (ray θ) (p - v) ∈ Icc (0 : ℝ) 1 ∧
      inner ℝ (perpRay θ) (p - v) ∈ Icc (0 : ℝ) 1 := by
  have hflip := (cornerFlip_mem_unitSquare j).mpr hp
  rcases corner_frame_coordinates e v θ j hv hc with hform | hform
  · rw [hform] at hflip
    simpa only [unitSquare, mem_ofPred_eq, frameCoordinates_zero,
      frameCoordinates_one] using hflip
  · rw [hform] at hflip
    change frameCoordinates v θ p 1 ∈ Icc (0 : ℝ) 1 ∧
      frameCoordinates v θ p 0 ∈ Icc (0 : ℝ) 1 at hflip
    simpa only [frameCoordinates_zero, frameCoordinates_one] using
      And.intro hflip.2 hflip.1

/-- Bottom contact of a tile placed at an upper square corner forces one
of its inward coordinates to equal one. -/
theorem bottom_contact_inward_coordinate_one (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (v : Plane) (θ : ℝ) (j : Fin 4) (hj : j = 2 ∨ j = 3)
    (hv : e v = corner j)
    (hc : e (v + (1 / 2 : ℝ) • (ray θ + perpRay θ)) = squareCenter)
    {p : Plane} (hbottom : e p 1 = 0) :
    inner ℝ (ray θ) (p - v) = 1 ∨ inner ℝ (perpRay θ) (p - v) = 1 := by
  have hdown : cornerFlip j (e p) 1 = 1 := by
    rcases hj with rfl | rfl <;>
      norm_num [cornerFlipPoint, corner, Fin.ext_iff, hbottom]
  rcases corner_frame_coordinates e v θ j hv hc with hform | hform
  · right
    rw [hform] at hdown
    simpa only [frameCoordinates_one] using hdown
  · left
    rw [hform] at hdown
    change frameCoordinates v θ p 0 = 1 at hdown
    simpa only [frameCoordinates_zero] using hdown

/-- Finite inward level-one faces imply finite actual contact with the
opposite bottom side of an upper-corner placement. -/
theorem bottom_contact_finite_of_coordinate_faces
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (v : Plane) (θ : ℝ) (j : Fin 4)
    (hj : j = 2 ∨ j = 3) (hv : e v = corner j)
    (hc : e (v + (1 / 2 : ℝ) • (ray θ + perpRay θ)) = squareCenter)
    {P : Set Plane}
    (hfirst : {p | p ∈ P ∧ inner ℝ (ray θ) (p - v) = 1}.Finite)
    (hsecond : {p | p ∈ P ∧ inner ℝ (perpRay θ) (p - v) = 1}.Finite) :
    (e '' P ∩ {p : Plane | p 1 = 0}).Finite := by
  apply ((hfirst.union hsecond).image e).subset
  rintro p ⟨⟨q, hq, rfl⟩, hbottom⟩
  refine ⟨q, ?_, rfl⟩
  rcases bottom_contact_inward_coordinate_one e v θ j hj hv hc hbottom with h | h
  · exact Or.inl ⟨hq, h⟩
  · exact Or.inr ⟨hq, h⟩

end

end Puzzling139335.N4Midline
