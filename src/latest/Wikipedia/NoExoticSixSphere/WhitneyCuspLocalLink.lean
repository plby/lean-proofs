import Wikipedia.NoExoticSixSphere.WhitneyCuspParity

/-!
# The cusp frame obstruction on every positive-radius local link

The normalized actual derivative on a radius-`ρ` parameter sphere has
parity one for every `ρ > 0`. The comparison changes the radius through
positive radii, so all operators stay injective. In particular this link
cannot be filled by a continuous family of three-frames on the four-ball.
-/

noncomputable section

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization Stiefel
open Wikipedia.HopfProblem.DegreeCollapse

theorem continuous_radial_deformation (ρ : ℝ) :
    Continuous (fun q : Sphere 3 ↦ deformation 1 (ρ • q.val)) := by
  apply continuous_clm_apply.mpr
  intro v
  have hs : Continuous (fun q : Sphere 3 ↦ ρ • q.val) :=
    continuous_subtype_val.const_smul ρ
  have hc : Continuous (fun q : Sphere 3 ↦ ((1 : ℝ), ρ • q.val)) :=
    continuous_const.prodMk hs
  have h := (contDiff_deformation_apply v).continuous.comp hc
  simpa only [Function.comp_def] using h

def gaussMapRadius (ρ : ℝ) (hρ : 0 < ρ) : C(Sphere 3, Space 6 3) :=
  Orthonormalization.map (fun q : Sphere 3 ↦ deformation 1 (ρ • q.val))
    (fun q ↦ injective_deformation 1 zero_le_one (ρ • q.val)
      (smul_ne_zero hρ.ne' (ne_zero_of_mem_unit_sphere q)))
    (continuous_radial_deformation ρ)

theorem gaussMapRadius_operator (ρ : ℝ) (hρ : 0 < ρ) (q : Sphere 3) :
    (gaussMapRadius ρ hρ q).val = Orthonormalization.operator
      (fun p : Vector 4 ↦ fderiv ℝ (map (p 0)) (source p)) (ρ • q.val) := by
  change Orthonormalization.operator (fun p : Vector 4 ↦ deformation 1 p) (ρ • q.val) = _
  have he : (fun p : Vector 4 ↦ deformation 1 p) =
      fun p ↦ fderiv ℝ (map (p 0)) (source p) := funext deformation_one
  rw [he]

def linkRadius (ρ : ℝ) (s : unitInterval) : ℝ := 1 - (s : ℝ) + (s : ℝ) * ρ

theorem linkRadius_pos (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) :
    0 < linkRadius ρ s := by
  dsimp [linkRadius]
  have hs₀ := s.property.1
  have hs₁ := s.property.2
  by_cases hs : (s : ℝ) = 0
  · simp [hs]
  · have hp : 0 < (s : ℝ) * ρ := mul_pos (lt_of_le_of_ne hs₀ (Ne.symm hs)) hρ
    linarith

theorem continuous_link_deformation (ρ : ℝ) :
    Continuous (fun z : unitInterval × Sphere 3 ↦
      deformation 1 (linkRadius ρ z.1 • z.2.val)) := by
  have hr : Continuous (fun z : unitInterval × Sphere 3 ↦ linkRadius ρ z.1) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
  have hc : Continuous (fun z : unitInterval × Sphere 3 ↦
      ((1 : ℝ), linkRadius ρ z.1 • z.2.val)) :=
    continuous_const.prodMk (hr.smul (continuous_subtype_val.comp continuous_snd))
  apply continuous_clm_apply.mpr
  intro v
  have h := (contDiff_deformation_apply v).continuous.comp hc
  simpa only [Function.comp_def] using h

def linkFrameMap (ρ : ℝ) (hρ : 0 < ρ) : C(unitInterval × Sphere 3, Space 6 3) :=
  Orthonormalization.map
    (fun z : unitInterval × Sphere 3 ↦ deformation 1 (linkRadius ρ z.1 • z.2.val))
    (fun z ↦ injective_deformation 1 zero_le_one _
      (smul_ne_zero (linkRadius_pos ρ hρ z.1).ne' (ne_zero_of_mem_unit_sphere z.2)))
    (continuous_link_deformation ρ)

theorem linkFrameMap_zero (ρ : ℝ) (hρ : 0 < ρ) (q : Sphere 3) :
    linkFrameMap ρ hρ (0, q) = gaussMap q := by
  apply Subtype.ext
  change Orthonormalization.operator (fun p : Vector 4 ↦ deformation 1 p)
    (linkRadius ρ 0 • q.val) = _
  have hr : linkRadius ρ 0 = 1 := by simp [linkRadius]
  rw [hr, one_smul]
  rfl

theorem linkFrameMap_one (ρ : ℝ) (hρ : 0 < ρ) (q : Sphere 3) :
    linkFrameMap ρ hρ (1, q) = gaussMapRadius ρ hρ q := by
  apply Subtype.ext
  change Orthonormalization.operator (fun p : Vector 4 ↦ deformation 1 p)
    (linkRadius ρ 1 • q.val) = _
  have hr : linkRadius ρ 1 = ρ := by simp [linkRadius]
  rw [hr]
  rfl

def linkHomotopy (ρ : ℝ) (hρ : 0 < ρ) : gaussMap.Homotopy (gaussMapRadius ρ hρ) where
  toFun := linkFrameMap ρ hρ
  continuous_toFun := (linkFrameMap ρ hρ).continuous
  map_zero_left := linkFrameMap_zero ρ hρ
  map_one_left := linkFrameMap_one ρ hρ

theorem gaussMapRadius_parity (ρ : ℝ) (hρ : 0 < ρ) :
    sphereThirdObstruction 1 (gaussMapRadius ρ hρ) = 1 := by
  rw [← sphereThirdObstruction_homotopic 1 ⟨linkHomotopy ρ hρ⟩, gauss_parity]

theorem gaussMapRadius_no_extension (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ ∃ F : C(DiskCylinder.Disk (E := Vector 4), Space 6 3),
      ∀ q, F (DiskCylinder.boundaryToDisk q) = gaussMapRadius ρ hρ q := by
  rw [← sphereThirdObstruction_zero_iff_extension, gaussMapRadius_parity]
  exact one_ne_zero

end NoExoticSixSphere.WhitneyCusp
