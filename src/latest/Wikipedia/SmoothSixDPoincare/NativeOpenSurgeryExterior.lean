import Wikipedia.SmoothSixDPoincare.OpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.MorseLowerHandleRange

/-!
# The recorded unshrunk native exterior is a diffeomorphism

Both directions of the exact common-exterior homeomorphism are the
recorded whole-sublevel realization maps. Their constructed exterior
smoothness therefore holds in the original regular-level atlases.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem exteriorForward_openExterior (x : d.surgery.oldOpenExterior) :
    d.exteriorForward x.val = (d.surgery.openExteriorHomeomorph x).val.val := by
  let r := d.surgery.oldOpenCoordinates x
  have hr : (⟨r.val, r.property.1⟩ : d.LowerLevel) = x.val :=
    (Subtype.ext (d.oldExterior_eq r)).symm.trans (d.surgery.oldExterior_oldOpenCoordinates x)
  exact (congrArg d.exteriorForward hr.symm).trans (d.exteriorForward_newExterior r)

theorem exteriorBackward_openExterior (y : d.surgery.newOpenExterior) :
    d.exteriorBackward y.val = (d.surgery.openExteriorHomeomorph.symm y).val.val := by
  let r := d.surgery.newOpenCoordinates y
  have h : d.attachmentHomeomorph ⟨r.val, Or.inl r.property.1.le⟩ =
      (⟨y.val.val, y.val.property.le⟩ : {x : M // f x ≤ f p + d.radius ^ 2}) :=
    Subtype.ext ((d.newExterior_eq r).symm.trans
      (congrArg (fun x : d.UpperLevel => x.val) (d.surgery.newExterior_newOpenCoordinates y)))
  have hi := congrArg (fun x => (d.attachmentHomeomorph.symm x).val) h
  rw [Homeomorph.symm_apply_apply] at hi
  exact hi.symm.trans (d.oldExterior_eq r).symm

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hd : d.HasSmoothExterior hf)

include hd in
theorem contMDiff_openExteriorHomeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      d.surgery.openExteriorHomeomorph := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply (ContMDiff.subtypeVal_comp_iff d.surgery.newOpenExterior _).mp
  apply (RegularLevel.contMDiff_iff_inclusion hf d.upper_regular
    𝓘(ℝ, RegularLevel.Model E) _).mpr
  have hmaps (x : d.surgery.oldOpenExterior) : x.val.val ∉
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block) := by
    intro hx
    exact x.property ((d.mem_handleRange_iff_mem_oldPiece x.val).mp hx)
  exact (hd.forward.comp_contMDiff contMDiff_subtype_val hmaps).congr
    (fun x => (d.exteriorForward_openExterior x).symm)

include hd in
theorem contMDiff_openExteriorHomeomorph_symm :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      d.surgery.openExteriorHomeomorph.symm := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply (ContMDiff.subtypeVal_comp_iff d.surgery.oldOpenExterior _).mp
  apply (RegularLevel.contMDiff_iff_inclusion hf d.lower_regular
    𝓘(ℝ, RegularLevel.Model E) _).mpr
  have hmaps (y : d.surgery.newOpenExterior) : d.exteriorBackward y.val ∉
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block) := by
    rw [d.exteriorBackward_openExterior y]
    intro hy
    exact (d.surgery.openExteriorHomeomorph.symm y).property
      ((d.mem_handleRange_iff_mem_oldPiece _).mp hy)
  exact (hd.backward.comp_contMDiff contMDiff_subtype_val hmaps).congr
    (fun y => (d.exteriorBackward_openExterior y).symm)

def openExteriorDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      d.surgery.oldOpenExterior d.surgery.newOpenExterior ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact {
    toEquiv := d.surgery.openExteriorHomeomorph.toEquiv
    contMDiff_toFun := d.contMDiff_openExteriorHomeomorph hf hd
    contMDiff_invFun := d.contMDiff_openExteriorHomeomorph_symm hf hd }

theorem openExteriorDiffeomorph_toHomeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (d.openExteriorDiffeomorph hf hd).toHomeomorph = d.surgery.openExteriorHomeomorph := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
