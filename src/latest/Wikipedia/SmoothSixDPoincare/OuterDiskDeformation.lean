import Wikipedia.SmoothSixDPoincare.RadialExtension
import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Homotopy.Equiv

/-! # Radial deformation of the outer half of a disk onto its boundary -/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.OuterDisk

open MorseHandle

abbrev Space (E : Type*) [NormedAddCommGroup E] :=
  {z : UnitDisk E // 1 / 2 < ‖(z : E)‖}

variable {E : Type*} [NormedAddCommGroup E]

theorem norm_pos (z : Space E) : 0 < ‖(z.val : E)‖ := by linarith [z.property]

def sphereDisk : C(sphere (0 : E) 1, UnitDisk E) :=
  ⟨Set.inclusion sphere_subset_closedBall, continuous_inclusion _⟩

theorem sphereDisk_mem (u : sphere (0 : E) 1) : 1 / 2 < ‖(sphereDisk u : E)‖ := by
  change 1 / 2 < ‖(u : E)‖
  rw [mem_sphere_zero_iff_norm.mp u.property]
  norm_num

def fromSphere : C(sphere (0 : E) 1, Space E) :=
  ⟨fun u => ⟨sphereDisk u, sphereDisk_mem u⟩, sphereDisk.continuous.subtype_mk _⟩

variable [NormedSpace ℝ E]

def toSphere : C(Space E, sphere (0 : E) 1) :=
  ⟨fun z => RadialExtension.direction (z.val : E)
      (norm_ne_zero_iff.mp (norm_pos z).ne'),
    (((continuous_subtype_val.comp continuous_subtype_val).norm.inv₀
      (fun z => (norm_pos z).ne')).smul
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩

theorem toSphere_fromSphere (u : sphere (0 : E) 1) : toSphere (fromSphere u) = u := by
  apply Subtype.ext
  change ‖(u : E)‖⁻¹ • (u : E) = (u : E)
  rw [mem_sphere_zero_iff_norm.mp u.property, inv_one, one_smul]

theorem fromSphere_toSphere_boundary (z : Space E) (hz : ‖(z.val : E)‖ = 1) :
    fromSphere (toSphere z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  change ‖(z.val : E)‖⁻¹ • (z.val : E) = (z.val : E)
  rw [hz, inv_one, one_smul]

def blendVector (q : I × Space E) : E :=
  ((1 - (q.1 : ℝ)) + (q.1 : ℝ) / ‖(q.2.val : E)‖) • (q.2.val : E)

theorem continuous_blendVector : Continuous (blendVector (E := E)) := by
  have ht : Continuous (fun q : I × Space E => (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun q : I × Space E => (q.2.val : E)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_const.sub ht).add
    (ht.div hz.norm (fun q => (norm_pos q.2).ne'))).smul hz

theorem norm_blendVector (t : I) (z : Space E) :
    ‖blendVector (t, z)‖ = (1 - (t : ℝ)) * ‖(z.val : E)‖ + (t : ℝ) := by
  have hscale : 0 ≤ (1 - (t : ℝ)) + (t : ℝ) / ‖(z.val : E)‖ :=
    add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_pos z).le)
  rw [blendVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale, add_mul,
    div_mul_cancel₀ _ (norm_pos z).ne']

theorem norm_blendVector_mem (t : I) (z : Space E) :
    1 / 2 < ‖blendVector (t, z)‖ ∧ ‖blendVector (t, z)‖ ≤ 1 := by
  rw [norm_blendVector]
  have hz : ‖(z.val : E)‖ ∈ Ioc (1 / 2 : ℝ) 1 :=
    ⟨z.property, mem_closedBall_zero_iff.mp z.val.property⟩
  have h := (convex_Ioc (𝕜 := ℝ) (1 / 2 : ℝ) 1) hz
    (by norm_num : (1 : ℝ) ∈ Ioc (1 / 2) 1)
    (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
  simpa only [mem_Ioc, smul_eq_mul, mul_one] using h

def blend (q : I × Space E) : Space E :=
  ⟨⟨blendVector q, mem_closedBall_zero_iff.mpr (norm_blendVector_mem q.1 q.2).2⟩,
    (norm_blendVector_mem q.1 q.2).1⟩

theorem continuous_blend : Continuous (blend (E := E)) :=
  (continuous_blendVector.subtype_mk _).subtype_mk _

/-- Expand radially to the boundary, fixing the entire boundary throughout. -/
def deformation : (ContinuousMap.id (Space E)).HomotopyRel (fromSphere.comp toSphere)
    {z | ‖(z.val : E)‖ = 1} where
  toFun := blend
  continuous_toFun := continuous_blend
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector]
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    simp [blend, blendVector, fromSphere, sphereDisk, toSphere, RadialExtension.direction]
  prop' t z hz := by
    apply Subtype.ext
    apply Subtype.ext
    change ((1 - (t : ℝ)) + (t : ℝ) / ‖(z.val : E)‖) • (z.val : E) = (z.val : E)
    rw [hz, div_one, sub_add_cancel, one_smul]

end Wikipedia.SmoothSixDPoincare.OuterDisk
