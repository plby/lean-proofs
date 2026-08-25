import StackExchange.Puzzling139335.SourceFaceBridge.UpperDefs
import StackExchange.Puzzling139335.PlaneIsometries.Matrix
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Normalizing two actual placement frames by one square reflection

The first matrix row and the image of a distinguished side midpoint fix an
affine isometry up to the sign of its second row.  A single common horizontal
reflection selects the prescribed right placement.  The remaining choice
on the left is exactly the proper/glide parity of `UpperFaceData.left`.
Only actual matrix entries and midpoint images are assumed here.
-/

open Set

namespace Puzzling139335.N4OuterPair

open PlaneIsometries SourceFaceBridge

noncomputable section

/-- The common postcomposition is either the identity or reflection in
the horizontal midline of the square. -/
def postReflect (σ : Bool) : Plane ≃ᵃⁱ[ℝ] Plane :=
  if σ then ReflectionSeparation.horizontal else AffineIsometryEquiv.refl ℝ Plane

@[simp] theorem postReflect_apply_zero (σ : Bool) (p : Plane) :
    postReflect σ p 0 = p 0 := by
  cases σ <;> simp [postReflect]

@[simp] theorem postReflect_apply_one (σ : Bool) (p : Plane) :
    postReflect σ p 1 = if σ then 1 - p 1 else p 1 := by
  cases σ <;> simp [postReflect]

@[simp] theorem postReflect_involutive (σ : Bool) (p : Plane) :
    postReflect σ (postReflect σ p) = p := by
  cases σ <;> simp [postReflect]

@[simp] theorem postReflect_mem_unitSquare (σ : Bool) {p : Plane} :
    postReflect σ p ∈ unitSquare ↔ p ∈ unitSquare := by
  cases σ <;> simp [postReflect]

theorem postReflect_image_unitSquare (σ : Bool) :
    postReflect σ '' unitSquare = unitSquare := by
  cases σ
  · simp [postReflect]
  · exact ReflectionSeparation.horizontal_image_unitSquare

theorem postReflect_injective (σ : Bool) : Function.Injective (postReflect σ) :=
  (postReflect σ).isometry.injective

theorem postReflect_image_interior (σ : Bool) (P : Set Plane) :
    postReflect σ '' interior P = interior (postReflect σ '' P) :=
  (postReflect σ).toHomeomorph.image_interior P

@[simp] theorem postReflect_side_point (σ : Bool) (x y : ℝ) :
    postReflect σ (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk x (if σ then 1 - y else y) := by
  apply plane_ext <;> simp [Schoenflies.Plane.mk]

@[simp] theorem postReflect_midline_point (σ : Bool) (x : ℝ) :
    postReflect σ (Schoenflies.Plane.mk x (1 / 2)) =
      Schoenflies.Plane.mk x (1 / 2) := by
  rw [postReflect_side_point]
  cases σ <;> norm_num

@[simp] theorem postReflect_center (σ : Bool) :
    postReflect σ squareCenter = squareCenter := by
  cases σ <;> simp [postReflect]

/-- An orthogonal plane matrix has exactly two possible second rows
once its first row is specified. -/
theorem matrix_second_row_of_first (e : Plane ≃ᵃⁱ[ℝ] Plane) {c s : ℝ}
    (h00 : linearMatrix e 0 0 = c) (h01 : linearMatrix e 0 1 = s) :
    (linearMatrix e 1 0 = -s ∧ linearMatrix e 1 1 = c) ∨
      (linearMatrix e 1 0 = s ∧ linearMatrix e 1 1 = -c) := by
  obtain ⟨c', s', _hcs, he | he⟩ := linearMatrix_classification e
  · left
    have hc : c' = c := by simpa [he] using h00
    have hs : -s' = s := by simpa [he] using h01
    constructor
    · simpa [he] using (show s' = -s by linarith only [hs])
    · simpa [he] using hc
  · right
    have hc : c' = c := by simpa [he] using h00
    have hs : s' = s := by simpa [he] using h01
    constructor
    · simpa [he] using hs
    · simpa [he] using (show -c' = -c from congrArg Neg.neg hc)

/-- Evaluate an affine map using displacements from a chosen source point. -/
theorem affine_apply_coord_centered (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (M p : Plane) (i : Fin 2) :
    (e p) i = linearMatrix e i 0 * (p 0 - M 0) +
      linearMatrix e i 1 * (p 1 - M 1) + (e M) i := by
  rw [affine_apply_eq_matrix_coordinates e p, affine_apply_eq_matrix_coordinates e M]
  fin_cases i <;> simp <;> ring

private theorem right_placement_cases (D : UpperFaceData) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hM : e D.M₁ = Schoenflies.Plane.mk 1 (1 / 2))
    (h00 : linearMatrix e 0 0 = Real.cos D.φ)
    (h01 : linearMatrix e 0 1 = Real.sin D.φ) :
    (e : Plane → Plane) = D.right ∨
      (ReflectionSeparation.horizontal ∘ e) = D.right := by
  have hm₀ : (e D.M₁) 0 = 1 := congrArg (fun p : Plane => p 0) hM
  have hm₁ : (e D.M₁) 1 = (1 / 2 : ℝ) := congrArg (fun p : Plane => p 1) hM
  have hx (p : Plane) : (e p) 0 = 1 + D.normal₁ p - D.normal₁ D.M₁ := by
    rw [affine_apply_coord_centered e D.M₁ p 0, h00, h01, hm₀]
    dsimp [UpperFaceData.normal₁]
    ring
  rcases matrix_second_row_of_first e h00 h01 with ⟨h10, h11⟩ | ⟨h10, h11⟩
  · left
    funext p
    apply plane_ext
    · exact hx p
    · rw [affine_apply_coord_centered e D.M₁ p 1, h10, h11, hm₁]
      simp [UpperFaceData.right, UpperFaceData.tangent₁]
      ring
  · right
    funext p
    apply plane_ext
    · simpa only [Function.comp_apply, ReflectionSeparation.horizontal_apply_zero,
        UpperFaceData.right, SourceFaceBridge.point_zero] using hx p
    · change ReflectionSeparation.horizontal (e p) 1 = (D.right p) 1
      rw [ReflectionSeparation.horizontal_apply_one,
        affine_apply_coord_centered e D.M₁ p 1, h10, h11, hm₁]
      simp [UpperFaceData.right, UpperFaceData.tangent₁]
      ring

private theorem left_placement_cases (D : UpperFaceData) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hM : e D.M₂ = Schoenflies.Plane.mk 0 (1 / 2))
    (h00 : linearMatrix e 0 0 = -Real.cos D.ψ)
    (h01 : linearMatrix e 0 1 = -Real.sin D.ψ) :
    (e : Plane → Plane) = D.leftProper ∨ (e : Plane → Plane) = D.leftGlide := by
  have hm₀ : (e D.M₂) 0 = 0 := congrArg (fun p : Plane => p 0) hM
  have hm₁ : (e D.M₂) 1 = (1 / 2 : ℝ) := congrArg (fun p : Plane => p 1) hM
  have hx (p : Plane) : (e p) 0 = D.normal₂ D.M₂ - D.normal₂ p := by
    rw [affine_apply_coord_centered e D.M₂ p 0, h00, h01, hm₀]
    dsimp [UpperFaceData.normal₂]
    ring
  rcases matrix_second_row_of_first e h00 h01 with ⟨h10, h11⟩ | ⟨h10, h11⟩
  · left
    funext p
    apply plane_ext
    · exact hx p
    · rw [affine_apply_coord_centered e D.M₂ p 1, h10, h11, hm₁]
      simp [UpperFaceData.leftProper, UpperFaceData.tangent₂]
      ring
  · right
    funext p
    apply plane_ext
    · exact hx p
    · rw [affine_apply_coord_centered e D.M₂ p 1, h10, h11, hm₁]
      simp [UpperFaceData.leftGlide, UpperFaceData.tangent₂]
      ring

theorem horizontal_upper_leftProper (D : UpperFaceData) (p : Plane) :
    ReflectionSeparation.horizontal (D.leftProper p) = D.leftGlide p := by
  apply plane_ext
  · simp [UpperFaceData.leftProper, UpperFaceData.leftGlide]
  · simp [UpperFaceData.leftProper, UpperFaceData.leftGlide]
    ring

theorem horizontal_upper_leftGlide (D : UpperFaceData) (p : Plane) :
    ReflectionSeparation.horizontal (D.leftGlide p) = D.leftProper p := by
  apply plane_ext
  · simp [UpperFaceData.leftProper, UpperFaceData.leftGlide]
  · simp [UpperFaceData.leftProper, UpperFaceData.leftGlide]
    ring

/-- One common square reflection normalizes the right placement, while
the left placement has exactly the two parities recorded by the model.
The source set, interface, and angle ranges are not assumptions. -/
theorem exists_normalized_placements (D : UpperFaceData)
    (eR eL : Plane ≃ᵃⁱ[ℝ] Plane)
    (hRM : eR D.M₁ = Schoenflies.Plane.mk 1 (1 / 2))
    (hLM : eL D.M₂ = Schoenflies.Plane.mk 0 (1 / 2))
    (hR00 : linearMatrix eR 0 0 = Real.cos D.φ)
    (hR01 : linearMatrix eR 0 1 = Real.sin D.φ)
    (hL00 : linearMatrix eL 0 0 = -Real.cos D.ψ)
    (hL01 : linearMatrix eL 0 1 = -Real.sin D.ψ) :
    ∃ σ rev : Bool, (postReflect σ ∘ eR) = D.right ∧
      (postReflect σ ∘ eL) = D.left rev := by
  rcases right_placement_cases D eR hRM hR00 hR01 with hR | hR
  · rcases left_placement_cases D eL hLM hL00 hL01 with hL | hL
    · refine ⟨false, false, ?_, ?_⟩
      · simpa [postReflect] using hR
      · simpa [postReflect, UpperFaceData.left] using hL
    · refine ⟨false, true, ?_, ?_⟩
      · simpa [postReflect] using hR
      · simpa [postReflect, UpperFaceData.left] using hL
  · rcases left_placement_cases D eL hLM hL00 hL01 with hL | hL
    · refine ⟨true, true, ?_, ?_⟩
      · simpa [postReflect] using hR
      · funext p
        change ReflectionSeparation.horizontal (eL p) = D.leftGlide p
        rw [congrFun hL p]
        exact horizontal_upper_leftProper D p
    · refine ⟨true, false, ?_, ?_⟩
      · simpa [postReflect] using hR
      · funext p
        change ReflectionSeparation.horizontal (eL p) = D.leftProper p
        rw [congrFun hL p]
        exact horizontal_upper_leftGlide D p

end

end Puzzling139335.N4OuterPair
