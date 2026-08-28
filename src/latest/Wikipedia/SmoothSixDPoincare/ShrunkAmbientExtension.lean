import Wikipedia.SmoothSixDPoincare.ShrunkMorseSurgery
import Wikipedia.SmoothSixDPoincare.MorseSurgerySmoothExterior

/-!
# Retaining the smooth ambient extension of a shrunk surgery

The extension records the exact postcomposition on the whole attachment,
not just its boundary. This gives exact forward and backward exterior
formulas in terms of the original recorded maps and the same boundary map.
-/

noncomputable section

open Set Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {a : ℝ}

namespace ShrunkSurgeryRealization

variable (R : d.ShrunkSurgeryRealization a)

def exteriorForward (x : d.LowerLevel) : M :=
  (R.attachmentHomeomorph ⟨x.val, Or.inl x.property.le⟩).val

def exteriorBackward (x : d.UpperLevel) : M :=
  (R.attachmentHomeomorph.symm ⟨x.val, x.property.le⟩).val

structure AmbientExtension where
  ambient : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞
  preserves_height : ∀ x, f (ambient x) = f x
  attachment_eq : ∀ x, (R.attachmentHomeomorph x).val =
    ambient (d.attachmentHomeomorph x).val
  boundary_eq : ∀ x : d.UpperLevel, (R.boundaryHomeomorph x).val = ambient x.val

namespace AmbientExtension

variable {R} (H : R.AmbientExtension)

theorem exteriorForward_eq (x : d.LowerLevel) :
    R.exteriorForward x = H.ambient (d.exteriorForward x) :=
  H.attachment_eq _

theorem boundary_symm_eq (x : d.UpperLevel) :
    (R.boundaryHomeomorph.symm x).val = H.ambient.symm x.val := by
  apply H.ambient.injective
  change H.ambient (R.boundaryHomeomorph.symm x).val = H.ambient (H.ambient.symm x.val)
  rw [H.ambient.apply_symm_apply]
  exact (H.boundary_eq (R.boundaryHomeomorph.symm x)).symm.trans
    (congrArg Subtype.val (R.boundaryHomeomorph.apply_symm_apply x))

include H in
theorem exteriorBackward_eq (x : d.UpperLevel) :
    R.exteriorBackward x = d.exteriorBackward (R.boundaryHomeomorph.symm x) := by
  let y := R.boundaryHomeomorph.symm x
  let q := d.attachmentHomeomorph.symm ⟨y.val, y.property.le⟩
  have hq : R.attachmentHomeomorph q = ⟨x.val, x.property.le⟩ := by
    apply Subtype.ext
    rw [H.attachment_eq]
    change H.ambient (d.attachmentHomeomorph
      (d.attachmentHomeomorph.symm ⟨y.val, y.property.le⟩)).val = x.val
    rw [d.attachmentHomeomorph.apply_symm_apply]
    exact (H.boundary_eq y).symm.trans
      (congrArg Subtype.val (R.boundaryHomeomorph.apply_symm_apply x))
  have h := congrArg R.attachmentHomeomorph.symm hq
  rw [R.attachmentHomeomorph.symm_apply_apply] at h
  exact (congrArg Subtype.val h).symm

end AmbientExtension

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

structure HasSmoothExterior : Prop where
  forward :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ R.exteriorForward
      {x | x.val ∉ range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)}
  backward :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, E) ∞ R.exteriorBackward
      {x | R.exteriorBackward x ∉
        range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)}

end ShrunkSurgeryRealization

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
