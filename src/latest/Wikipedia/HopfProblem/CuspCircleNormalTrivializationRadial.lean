import Wikipedia.HopfProblem.CuspCircleNormalTrivializationOpenRestriction
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Literal positive radial changes of the standard ball

Positive scalar multiplication identifies unit balls and spheres with
balls and spheres of the specified radius. The open-ball identification
is real analytic for the original open-submanifold atlases.
-/

noncomputable section

open Set Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual positive scalar multiplication and its actual inverse. -/
def diffeomorph (r : ℝ) (hr : 0 < r) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ω where
  toEquiv := (LinearEquiv.smulOfNeZero ℝ E r hr.ne').toEquiv
  contMDiff_toFun := (contDiff_const.smul contDiff_id).contMDiff
  contMDiff_invFun := (contDiff_const.smul contDiff_id).contMDiff

@[simp] theorem diffeomorph_apply (r : ℝ) (hr : 0 < r) (x : E) :
    diffeomorph r hr x = r • x := rfl

@[simp] theorem diffeomorph_symm_apply (r : ℝ) (hr : 0 < r) (x : E) :
    (diffeomorph r hr).symm x = r⁻¹ • x := rfl

theorem smul_mem_ball_iff (r : ℝ) (hr : 0 < r) (x : E) :
    r • x ∈ ball (0 : E) r ↔ x ∈ ball (0 : E) 1 := by
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
  constructor <;> intro h <;> nlinarith only [hr, h]

theorem smul_mem_closedBall_iff (r : ℝ) (hr : 0 < r) (x : E) :
    r • x ∈ closedBall (0 : E) r ↔ x ∈ closedBall (0 : E) 1 := by
  simp only [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
  constructor <;> intro h <;> nlinarith only [hr, h]

theorem smul_mem_sphere_iff (r : ℝ) (hr : 0 < r) (x : E) :
    r • x ∈ sphere (0 : E) r ↔ x ∈ sphere (0 : E) 1 := by
  simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_of_nonneg hr.le]
  constructor <;> intro h <;> nlinarith only [hr, h]

/-- The actual open ball with its inherited native atlas. -/
def ballOpen (r : ℝ) : TopologicalSpace.Opens E := ⟨ball 0 r, isOpen_ball⟩

/-- Literal positive scaling identifies the unit open ball with the radius-`r` ball. -/
def ballHomeomorph (r : ℝ) (hr : 0 < r) : ballOpen (E := E) 1 ≃ₜ ballOpen (E := E) r :=
  (diffeomorph (E := E) r hr).toHomeomorph.subtype
    (fun x => (smul_mem_ball_iff r hr x).symm)

/-- The same open-ball map is real analytic for the unchanged native open-subtype atlases. -/
def ballDiffeomorph (r : ℝ) (hr : 0 < r) :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (ballOpen (E := E) 1) (ballOpen (E := E) r) ω where
  toEquiv := (ballHomeomorph r hr).toEquiv
  contMDiff_toFun := by
    intro p
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact ((diffeomorph r hr).contMDiff.comp contMDiff_subtype_val) p
  contMDiff_invFun := by
    intro p
    apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp
    exact ((diffeomorph r hr).symm.contMDiff.comp contMDiff_subtype_val) p

@[simp] theorem ballDiffeomorph_coe (r : ℝ) (hr : 0 < r) (x : ballOpen (E := E) 1) :
    (ballDiffeomorph r hr x : E) = r • (x : E) := rfl

@[simp] theorem ballDiffeomorph_symm_coe (r : ℝ) (hr : 0 < r) (x : ballOpen (E := E) r) :
    ((ballDiffeomorph r hr).symm x : E) = r⁻¹ • (x : E) := rfl

/-- The closed-ball identification is the restriction of the same ambient analytic scaling. -/
def closedBallHomeomorph (r : ℝ) (hr : 0 < r) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) r :=
  (diffeomorph (E := E) r hr).toHomeomorph.subtype
    (fun x => (smul_mem_closedBall_iff r hr x).symm)

@[simp] theorem closedBallHomeomorph_coe (r : ℝ) (hr : 0 < r) (x : closedBall (0 : E) 1) :
    (closedBallHomeomorph r hr x : E) = r • (x : E) := rfl

@[simp] theorem closedBallHomeomorph_symm_coe (r : ℝ) (hr : 0 < r)
    (x : closedBall (0 : E) r) :
    ((closedBallHomeomorph r hr).symm x : E) = r⁻¹ • (x : E) := rfl

/-- Positive radial scaling restricts to the literal round sphere identification. -/
def sphereHomeomorph (r : ℝ) (hr : 0 < r) : sphere (0 : E) 1 ≃ₜ sphere (0 : E) r :=
  (diffeomorph (E := E) r hr).toHomeomorph.subtype
    (fun x => (smul_mem_sphere_iff r hr x).symm)

@[simp] theorem sphereHomeomorph_coe (r : ℝ) (hr : 0 < r) (x : sphere (0 : E) 1) :
    (sphereHomeomorph r hr x : E) = r • (x : E) := rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.Radial
