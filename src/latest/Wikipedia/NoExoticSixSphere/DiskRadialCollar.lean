import Wikipedia.NoExoticSixSphere.DiskRadialFlattening
import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Radial flattening and a boundary-vanishing collar clock on the actual disk

The previously constructed smooth radial flattening is used on the literal
closed ball. It is homotopic to the identity while fixing every boundary
point, and is exactly radial projection on the outer half-annulus. The
clock `1 - ‖x‖²` vanishes precisely on the boundary and is positive inside.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.DiskRadialCollar

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder

def flatten (n : ℕ) : C(Disk (E := Vector (n + 1)), Disk (E := Vector (n + 1))) :=
  ⟨fun x ↦ ⟨DiskRadialFlattening.map n x.val,
    DiskRadialFlattening.map_mem_closedBall n x.val⟩,
    ((DiskRadialFlattening.contDiff_map n).continuous.comp
      continuous_subtype_val).subtype_mk _⟩

theorem flatten_boundary (n : ℕ) (s : NoExoticSixSphere.Sphere n) :
    flatten n (boundaryToDisk s) = boundaryToDisk s :=
  Subtype.ext (DiskRadialFlattening.map_coe n s)

theorem flatten_radial (n : ℕ) (u : unitInterval) (hu : 1 / 2 ≤ (u : ℝ))
    (s : NoExoticSixSphere.Sphere n) :
    flatten n (DiskCone.radial (u, s)) = boundaryToDisk s := by
  apply Subtype.ext
  change DiskRadialFlattening.map n (DiskCone.radial (u, s)).val = s.val
  rw [DiskRadialFlattening.map_eq_normalize n ((DiskCone.radial_norm (u, s)) ▸ hu)]
  change NormedSpace.normalize ((u : ℝ) • s.val) = s.val
  rw [NormedSpace.normalize_smul_of_pos (by linarith : 0 < (u : ℝ))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm s)

def flattenHomotopy (n : ℕ) :
    (ContinuousMap.id (Disk (E := Vector (n + 1)))).HomotopyRel (flatten n)
      {x | ‖x.val‖ = 1} where
  toFun p := DiskBoundary.segment (flatten n p.2) (p.1, p.2)
  continuous_toFun := by
    have h : Continuous (fun p : unitInterval × Disk (E := Vector (n + 1)) ↦
        (1 - (p.1 : ℝ)) • p.2.val + (p.1 : ℝ) • (flatten n p.2).val) :=
      ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).add
          ((continuous_subtype_val.comp continuous_fst).smul
            (continuous_subtype_val.comp ((flatten n).continuous.comp continuous_snd)))
    exact h.subtype_mk _
  map_zero_left x := DiskBoundary.segment_zero _ x
  map_one_left x := DiskBoundary.segment_one _ x
  prop' u x hx := by
    let s : NoExoticSixSphere.Sphere n := ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩
    have hx' : boundaryToDisk s = x := Subtype.ext rfl
    have he : flatten n x = x := hx' ▸ flatten_boundary n s
    change DiskBoundary.segment (flatten n x) (u, x) = x
    rw [he, DiskBoundary.segment_fixed]

def clock (n : ℕ) : C(Disk (E := Vector (n + 1)), unitInterval) where
  toFun x := ⟨1 - ‖x.val‖ ^ 2, by
    have h := mem_closedBall_zero_iff.mp x.property
    have hn := norm_nonneg x.val
    constructor <;> nlinarith [sq_nonneg ‖x.val‖]⟩
  continuous_toFun :=
    (continuous_const.sub (continuous_subtype_val.norm.pow 2)).subtype_mk _

theorem clock_eq_zero_iff (n : ℕ) (x : Disk (E := Vector (n + 1))) :
    clock n x = 0 ↔ ‖x.val‖ = 1 := by
  constructor
  · intro h
    have he : 1 - ‖x.val‖ ^ 2 = 0 := congrArg Subtype.val h
    nlinarith [norm_nonneg x.val]
  · intro h
    apply Subtype.ext
    change 1 - ‖x.val‖ ^ 2 = 0
    rw [h]
    norm_num

theorem clock_boundary (n : ℕ) (s : NoExoticSixSphere.Sphere n) :
    clock n (boundaryToDisk s) = 0 :=
  (clock_eq_zero_iff n _).mpr (ClosedHemisphere.unit_norm s)

theorem clock_pos (n : ℕ) (x : Disk (E := Vector (n + 1))) (hx : ‖x.val‖ < 1) :
    0 < (clock n x : ℝ) := by
  change 0 < 1 - ‖x.val‖ ^ 2
  nlinarith [norm_nonneg x.val]

theorem clock_radial (n : ℕ) (u : unitInterval) (s : NoExoticSixSphere.Sphere n) :
    (clock n (DiskCone.radial (u, s)) : ℝ) = 1 - (u : ℝ) ^ 2 := by
  change 1 - ‖(DiskCone.radial (u, s)).val‖ ^ 2 = _
  rw [DiskCone.radial_norm]

end NoExoticSixSphere.DiskRadialCollar
