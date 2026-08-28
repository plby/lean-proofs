import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Explicit radial extension of a sphere homeomorphism

A homeomorphism of the unit sphere extends by preserving the radius and
applying the given map to the direction.  The exact norm identity proves
continuity at zero; the extension of the inverse is the actual inverse.
No extension theorem or finite-dimensional hypothesis is assumed.
-/

noncomputable section

open Set Metric Topology Filter

namespace Wikipedia.HopfProblem.CuspHoneycombRadial

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := sphere (0 : E) (1 : ℝ)

variable {E : Type*} [NormedAddCommGroup E]

@[simp] theorem unitSphere_norm (x : UnitSphere E) : ‖(x : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

theorem unitSphere_ne_zero (x : UnitSphere E) : (x : E) ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [unitSphere_norm]; exact one_ne_zero)

variable [NormedSpace ℝ E]

/-- The direction of a nonzero vector, as an actual point of the unit sphere. -/
def direction (x : {x : E // x ≠ 0}) : UnitSphere E :=
  ⟨NormedSpace.normalize x.1,
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize x.2)⟩

@[simp] theorem direction_coe (x : {x : E // x ≠ 0}) :
    (direction x : E) = ‖x.1‖⁻¹ • x.1 := rfl

theorem direction_continuous : Continuous (direction (E := E)) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.norm.inv₀
    (fun x : {x : E // x ≠ 0} => norm_ne_zero_iff.mpr x.2)).smul continuous_subtype_val

theorem norm_smul_direction (x : {x : E // x ≠ 0}) : ‖x.1‖ • (direction x : E) = x.1 :=
  NormedSpace.norm_smul_normalize x.1

theorem direction_sphere (x : UnitSphere E) (hx : (x : E) ≠ 0) :
    direction ⟨(x : E), hx⟩ = x :=
  Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (unitSphere_norm x))

variable (e : UnitSphere E ≃ₜ UnitSphere E)

private def radialOffZero (x : {x : E // x ≠ 0}) : E :=
  ‖x.1‖ • (e (direction x) : E)

private theorem radialOffZero_continuous : Continuous (radialOffZero e) :=
  continuous_subtype_val.norm.smul
    (continuous_subtype_val.comp (e.continuous.comp direction_continuous))

/-- Preserve the norm and transform the direction; zero is fixed explicitly. -/
def radialMap (x : E) : E := by
  classical
  exact if hx : x = 0 then 0 else radialOffZero e ⟨x, hx⟩

@[simp] theorem radialMap_zero : radialMap e (0 : E) = 0 := by
  simp [radialMap]

theorem radialMap_apply_of_ne_zero {x : E} (hx : x ≠ 0) :
    radialMap e x = ‖x‖ • (e (direction ⟨x, hx⟩) : E) := by
  simp only [radialMap, dif_neg hx, radialOffZero]

@[simp] theorem radialMap_norm (x : E) : ‖radialMap e x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp only [hx, radialMap_zero]
  · rw [radialMap_apply_of_ne_zero e hx, norm_smul, norm_norm, unitSphere_norm, mul_one]

@[simp] theorem radialMap_eq_zero_iff (x : E) : radialMap e x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← radialMap_norm e x, h, norm_zero]
  · rintro rfl
    exact radialMap_zero e

theorem radialMap_ne_zero {x : E} (hx : x ≠ 0) : radialMap e x ≠ 0 :=
  fun h => hx ((radialMap_eq_zero_iff e x).mp h)

theorem direction_radialMap {x : E} (hx : x ≠ 0) :
    direction ⟨radialMap e x, radialMap_ne_zero e hx⟩ = e (direction ⟨x, hx⟩) := by
  apply Subtype.ext
  change ‖radialMap e x‖⁻¹ • radialMap e x = (e (direction ⟨x, hx⟩) : E)
  rw [radialMap_norm, radialMap_apply_of_ne_zero e hx, smul_smul,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem radialMap_sphere (x : UnitSphere E) : radialMap e (x : E) = (e x : E) := by
  rw [radialMap_apply_of_ne_zero e (unitSphere_ne_zero x), unitSphere_norm,
    direction_sphere, one_smul]

theorem radialMap_symm (x : E) : radialMap e.symm (radialMap e x) = x := by
  by_cases hx : x = 0
  · simp only [hx, radialMap_zero]
  · rw [radialMap_apply_of_ne_zero e.symm (radialMap_ne_zero e hx), radialMap_norm,
      direction_radialMap e hx, e.symm_apply_apply]
    exact norm_smul_direction ⟨x, hx⟩

theorem radialMap_continuousAt_zero : ContinuousAt (radialMap e) (0 : E) := by
  change Tendsto (radialMap e) (𝓝 (0 : E)) (𝓝 (radialMap e 0))
  rw [radialMap_zero]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h : Tendsto (fun x : E => ‖x‖) (𝓝 (0 : E)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : E))
  simpa only [radialMap_norm] using h

theorem radialMap_continuousOn_nonzero : ContinuousOn (radialMap e) {x : E | x ≠ 0} := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact (radialOffZero_continuous e).congr
    (fun x : {x : E // x ≠ 0} => (radialMap_apply_of_ne_zero e x.2).symm)

theorem radialMap_continuous : Continuous (radialMap e) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact radialMap_continuousAt_zero e
  · exact (radialMap_continuousOn_nonzero e).continuousAt
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)

/-- The explicit norm-preserving extension to the entire real normed space. -/
def radialHomeomorph : E ≃ₜ E where
  toFun := radialMap e
  invFun := radialMap e.symm
  left_inv := radialMap_symm e
  right_inv := radialMap_symm e.symm
  continuous_toFun := radialMap_continuous e
  continuous_invFun := radialMap_continuous e.symm

@[simp] theorem radialHomeomorph_apply (x : E) : radialHomeomorph e x = radialMap e x := rfl

@[simp] theorem radialHomeomorph_symm_apply (x : E) :
    (radialHomeomorph e).symm x = radialMap e.symm x := rfl

@[simp] theorem radialHomeomorph_zero : radialHomeomorph e (0 : E) = 0 := radialMap_zero e

@[simp] theorem radialHomeomorph_norm (x : E) : ‖radialHomeomorph e x‖ = ‖x‖ := radialMap_norm e x

/-- The restriction to the given unit sphere is exactly the supplied homeomorphism. -/
theorem radialHomeomorph_sphere (x : UnitSphere E) :
    radialHomeomorph e (x : E) = (e x : E) := radialMap_sphere e x

/-- Norm preservation restricts the explicit extension to every closed ball. -/
def radialClosedBallHomeomorph (R : ℝ) : closedBall (0 : E) R ≃ₜ closedBall (0 : E) R :=
  (radialHomeomorph e).subtype
    (fun x => by simp only [mem_closedBall, dist_zero_right, radialHomeomorph_norm])

@[simp] theorem radialClosedBallHomeomorph_coe (R : ℝ) (x : closedBall (0 : E) R) :
    (radialClosedBallHomeomorph e R x : E) = radialHomeomorph e (x : E) := rfl

end Wikipedia.HopfProblem.CuspHoneycombRadial
