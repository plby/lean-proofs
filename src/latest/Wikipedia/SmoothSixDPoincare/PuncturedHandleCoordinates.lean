import Wikipedia.SmoothSixDPoincare.RadialExtension

/-!
# The actual coordinate homeomorphism between punctured surgery pieces

Polar coordinates identify a punctured closed disk with its unit sphere
times a positive radius at most one. Moving this radius from the second
disk factor to the first gives the handle core/belt complement coordinate
change. It agrees with the identity on the common sphere-times-sphere face.
-/

noncomputable section

open Set Metric

namespace Wikipedia.SmoothSixDPoincare.PuncturedHandle

abbrev Radius := Ioc (0 : ℝ) 1

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := sphere (0 : E) 1

abbrev PuncturedBall (E : Type*) [NormedAddCommGroup E] := {x : E // x ≠ 0 ∧ ‖x‖ ≤ 1}

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def point (u : UnitSphere E) (r : Radius) : PuncturedBall E := by
  have hn : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  have hnorm : ‖(r : ℝ) • (u : E)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1, hn, mul_one]
  refine ⟨(r : ℝ) • (u : E), ?_, ?_⟩
  · exact norm_pos_iff.mp (by rw [hnorm]; exact r.property.1)
  · rw [hnorm]
    exact r.property.2

theorem norm_point (u : UnitSphere E) (r : Radius) : ‖(point u r : E)‖ = (r : ℝ) := by
  change ‖(r : ℝ) • (u : E)‖ = (r : ℝ)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos r.property.1,
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

/-- Polar coordinates include the actual closed outer face and exclude only the disk center. -/
def polar (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    PuncturedBall E ≃ₜ (UnitSphere E × Radius) where
  toFun x := (RadialExtension.direction (x : E) x.property.1,
    ⟨‖(x : E)‖, norm_pos_iff.mpr x.property.1, x.property.2⟩)
  invFun p := point p.1 p.2
  left_inv := by
    intro x
    apply Subtype.ext
    change ‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    exact smul_inv_smul₀ (norm_ne_zero_iff.mpr x.property.1) (x : E)
  right_inv := by
    rintro ⟨u, r⟩
    apply Prod.ext
    · apply Subtype.ext
      change ‖(point u r : E)‖⁻¹ • ((r : ℝ) • (u : E)) = (u : E)
      rw [norm_point, inv_smul_smul₀ r.property.1.ne']
    · apply Subtype.ext
      exact norm_point u r
  continuous_toFun := by
    have hdir : Continuous (fun x : PuncturedBall E =>
        RadialExtension.direction (x : E) x.property.1) :=
      ((continuous_subtype_val.norm.inv₀
        (fun x => norm_ne_zero_iff.mpr x.property.1)).smul continuous_subtype_val).subtype_mk _
    exact hdir.prodMk (continuous_subtype_val.norm.subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _

/-- Exchange the radial coordinate between the actual punctured disk factors. -/
def exchange (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (UnitSphere E × PuncturedBall F) ≃ₜ (PuncturedBall E × UnitSphere F) :=
  ((Homeomorph.refl (UnitSphere E)).prodCongr (polar F)).trans
    (((Homeomorph.refl (UnitSphere E)).prodCongr
      (Homeomorph.prodComm (UnitSphere F) Radius)).trans
        ((Homeomorph.prodAssoc (UnitSphere E) Radius (UnitSphere F)).symm.trans
          ((polar E).symm.prodCongr (Homeomorph.refl (UnitSphere F)))))

theorem exchange_apply (u : UnitSphere E) (v : PuncturedBall F) :
    exchange E F (u, v) =
      (point u ⟨‖(v : F)‖, norm_pos_iff.mpr v.property.1, v.property.2⟩,
        RadialExtension.direction (v : F) v.property.1) := rfl

def boundaryPoint (u : UnitSphere E) : PuncturedBall E :=
  ⟨u, ne_of_mem_sphere u.property one_ne_zero,
    (mem_sphere_zero_iff_norm.mp u.property).le⟩

/-- The exchange is exactly the prescribed common-boundary identification. -/
theorem exchange_boundary (u : UnitSphere E) (v : UnitSphere F) :
    exchange E F (u, boundaryPoint v) = (boundaryPoint u, v) := by
  rw [exchange_apply]
  have hv : ‖(v : F)‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  apply Prod.ext
  · apply Subtype.ext
    change ‖(v : F)‖ • (u : E) = (u : E)
    rw [hv, one_smul]
  · apply Subtype.ext
    change ‖(v : F)‖⁻¹ • (v : F) = (v : F)
    rw [hv, inv_one, one_smul]

end Wikipedia.SmoothSixDPoincare.PuncturedHandle
