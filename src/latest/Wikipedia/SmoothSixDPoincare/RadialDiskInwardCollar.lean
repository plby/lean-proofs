import Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
import Wikipedia.SmoothSixDPoincare.CollaredDiskAttachment
import Wikipedia.SmoothSixDPoincare.OuterDiskDeformation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The actual radial inward collar of a finite-dimensional closed disk -/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.RadialDiskInwardCollar

open CollaredDiskAttachment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def point (q : Sphere E × I) : Disk E := collarPoint q.1 (unitInterval.symm q.2)

theorem norm_point (q : Sphere E × I) :
    ‖(point q : E)‖ = (1 + (1 - (q.2 : ℝ))) / 2 :=
  norm_collarPoint q.1 (unitInterval.symm q.2)

theorem continuous_point : Continuous (point (E := E)) := by
  have ht : Continuous (fun q : Sphere E × I => collarRadius (unitInterval.symm q.2)) :=
    (continuous_const.add
      (continuous_subtype_val.comp (unitInterval.continuous_symm.comp continuous_snd))).div_const 2
  exact (ht.smul (continuous_subtype_val.comp continuous_fst)).subtype_mk _

theorem point_injective : Injective (point (E := E)) := by
  rintro ⟨u, t⟩ ⟨v, s⟩ h
  have hn := congrArg (fun x : Disk E => ‖(x : E)‖) h
  rw [norm_point, norm_point] at hn
  have hts : t = s := Subtype.ext (by dsimp only at hn; linarith)
  subst s
  have hu := congrArg (fun x : Disk E => (collarRadius (unitInterval.symm t))⁻¹ • (x : E)) h
  have huv : (u : E) = (v : E) := by
    simpa only [point, collarPoint,
      inv_smul_smul₀ (collarRadius_pos (unitInterval.symm t)).ne'] using hu
  exact Prod.ext (Subtype.ext huv) rfl

theorem point_zero (u : Sphere E) : point (u, 0) = OuterDisk.sphereDisk u := by
  apply Subtype.ext
  change collarRadius (unitInterval.symm 0) • (u : E) = (u : E)
  rw [unitInterval.symm_zero, collarRadius_one, one_smul]

theorem inner_image : point '' {q : Sphere E × I | q.2 < 1} =
    {x : Disk E | (1 / 2 : ℝ) < ‖(x : E)‖} := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change (1 / 2 : ℝ) < ‖(point q : E)‖
    rw [norm_point]
    have ht : (q.2 : ℝ) < 1 := hq
    linarith
  · intro hx
    change (1 / 2 : ℝ) < ‖(x : E)‖ at hx
    have hxpos : 0 < ‖(x : E)‖ := by linarith [hx]
    have hxne : (x : E) ≠ 0 := norm_ne_zero_iff.mp hxpos.ne'
    let t : I := ⟨2 * (1 - ‖(x : E)‖), by
      constructor
      · linarith [mem_closedBall_zero_iff.mp x.property]
      · linarith [hx]⟩
    refine ⟨(RadialExtension.direction (x : E) hxne, t), ?_, ?_⟩
    · change 2 * (1 - ‖(x : E)‖) < 1
      linarith [hx]
    · apply Subtype.ext
      change collarRadius (unitInterval.symm t) • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
      have hr : collarRadius (unitInterval.symm t) = ‖(x : E)‖ := by
        dsimp [collarRadius, unitInterval.symm, t]
        ring
      rw [hr, smul_inv_smul₀ hxpos.ne']

variable [FiniteDimensional ℝ E]

def collar : InwardBoundaryCollar (OuterDisk.sphereDisk (E := E)) where
  map := ⟨point, continuous_point⟩
  closedEmbedding := continuous_point.isClosedEmbedding point_injective
  zero := point_zero
  inner_open := by
    change IsOpen (point '' {q : Sphere E × I | q.2 < 1})
    rw [inner_image]
    exact isOpen_lt continuous_const continuous_subtype_val.norm

end Wikipedia.SmoothSixDPoincare.RadialDiskInwardCollar
