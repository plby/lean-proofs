import Wikipedia.SmoothSixDPoincare.RadialExtension
import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Contractible

/-!
# The open disk and annulus in the actual cell cover

The open disk is contractible. The half-to-unit annulus is homotopy
equivalent to the original unit sphere by radial normalization and the
radius-three-quarters inclusion. All maps retain their actual vector formulas.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.DiskAnnulus

open MorseHandle

abbrev OpenDisk (E : Type*) [NormedAddCommGroup E] :=
  {z : UnitDisk E // ‖(z : E)‖ < 1}

abbrev Annulus (E : Type*) [NormedAddCommGroup E] :=
  {z : UnitDisk E // 1 / 2 < ‖(z : E)‖ ∧ ‖(z : E)‖ < 1}

variable {E : Type*} [NormedAddCommGroup E]

theorem norm_pos (z : Annulus E) : 0 < ‖(z.val : E)‖ := by linarith [z.property.1]

def openDiskHomeomorph : OpenDisk E ≃ₜ ball (0 : E) 1 where
  toFun z := ⟨z.val.val, mem_ball_zero_iff.mpr z.property⟩
  invFun z := ⟨⟨z.val, mem_closedBall_zero_iff.mpr (mem_ball_zero_iff.mp z.property).le⟩,
    mem_ball_zero_iff.mp z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [NormedSpace ℝ E]

theorem openDisk_contractible : ContractibleSpace (OpenDisk E) := by
  let : ContractibleSpace (ball (0 : E) 1) :=
    (convex_ball (0 : E) 1).contractibleSpace ⟨0, by simp⟩
  exact openDiskHomeomorph.contractibleSpace

def toSphere : C(Annulus E, sphere (0 : E) 1) :=
  ⟨fun z => RadialExtension.direction (z.val : E)
      (norm_ne_zero_iff.mp (norm_pos z).ne'),
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
      (fun z => (norm_pos z).ne')).smul
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

theorem norm_middle (u : sphere (0 : E) 1) : ‖(3 / 4 : ℝ) • (u : E)‖ = 3 / 4 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

def middleDisk (u : sphere (0 : E) 1) : UnitDisk E :=
  ⟨(3 / 4 : ℝ) • (u : E), by
    rw [mem_closedBall_zero_iff, norm_middle]
    norm_num⟩

theorem middleDisk_mem (u : sphere (0 : E) 1) :
    1 / 2 < ‖(middleDisk u : E)‖ ∧ ‖(middleDisk u : E)‖ < 1 := by
  change 1 / 2 < ‖(3 / 4 : ℝ) • (u : E)‖ ∧ ‖(3 / 4 : ℝ) • (u : E)‖ < 1
  rw [norm_middle]
  norm_num

def fromSphere : C(sphere (0 : E) 1, Annulus E) :=
  ⟨fun u => ⟨middleDisk u, middleDisk_mem u⟩,
    ((continuous_const.smul continuous_subtype_val).subtype_mk _).subtype_mk _⟩

theorem toSphere_fromSphere (u : sphere (0 : E) 1) : toSphere (fromSphere u) = u := by
  apply Subtype.ext
  change ‖(3 / 4 : ℝ) • (u : E)‖⁻¹ • ((3 / 4 : ℝ) • (u : E)) = (u : E)
  rw [norm_middle, inv_smul_smul₀ (by norm_num : (3 / 4 : ℝ) ≠ 0)]

def blendVector (q : I × Annulus E) : E :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * ((3 / 4 : ℝ) / ‖(q.2.val : E)‖)) • (q.2.val : E)

theorem continuous_blendVector : Continuous (blendVector (E := E)) := by
  have ht : Continuous (fun q : I × Annulus E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun q : I × Annulus E => (q.2.val : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub ht).add
    (ht.mul (continuous_const.div hz.norm (fun q => (norm_pos q.2).ne')))).smul hz

theorem norm_blendVector (t : I) (z : Annulus E) :
    ‖blendVector (t, z)‖ = (1 - (t : ℝ)) * ‖(z.val : E)‖ + (t : ℝ) * (3 / 4) := by
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) * ((3 / 4 : ℝ) / ‖(z.val : E)‖) :=
    add_nonneg (sub_nonneg.mpr t.property.2)
      (mul_nonneg t.property.1 (div_nonneg (by norm_num) (norm_pos z).le))
  rw [blendVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul,
    mul_assoc, div_mul_cancel₀ _ (norm_pos z).ne']

theorem norm_blendVector_mem (t : I) (z : Annulus E) :
    1 / 2 < ‖blendVector (t, z)‖ ∧ ‖blendVector (t, z)‖ < 1 := by
  rw [norm_blendVector]
  have h := (convex_Ioo (𝕜 := ℝ) (1 / 2 : ℝ) 1) z.property
    (by norm_num : (3 / 4 : ℝ) ∈ Ioo (1 / 2) 1)
    (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  exact h

def blend (q : I × Annulus E) : Annulus E :=
  ⟨⟨blendVector q, mem_closedBall_zero_iff.mpr (norm_blendVector_mem q.1 q.2).2.le⟩,
    norm_blendVector_mem q.1 q.2⟩

theorem continuous_blend : Continuous (blend (E := E)) :=
  (continuous_blendVector.subtype_mk _).subtype_mk _

/-- Radially move the whole annulus to its middle sphere without leaving the annulus. -/
def deformation : (ContinuousMap.id (Annulus E)).Homotopy (fromSphere.comp toSphere) where
  toFun := blend
  continuous_toFun := continuous_blend
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector]
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector, fromSphere, middleDisk, toSphere, RadialExtension.direction,
      div_eq_mul_inv, smul_smul]

def sphereHomotopyEquiv : sphere (0 : E) 1 ≃ₕ Annulus E where
  toFun := fromSphere
  invFun := toSphere
  left_inv := by
    have heq : toSphere.comp fromSphere = ContinuousMap.id (sphere (0 : E) 1) :=
      ContinuousMap.ext toSphere_fromSphere
    rw [heq]
  right_inv := ⟨deformation.symm⟩

theorem sphereHomotopyEquiv_apply (u : sphere (0 : E) 1) :
    ((sphereHomotopyEquiv u).val : E) = (3 / 4 : ℝ) • (u : E) := rfl

end Wikipedia.SmoothSixDPoincare.DiskAnnulus
