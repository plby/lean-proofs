import Wikipedia.SmoothSixDPoincare.OpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.SmoothShrunkExteriorTransport
import Wikipedia.SmoothSixDPoincare.ShrunkSurgeryBoundary

/-!
# The exact open exterior map is a native diffeomorphism

The two directions of the common-exterior homeomorphism are identified with
the original whole-sublevel realization and its inverse. Their previously
proved smoothness therefore gives a diffeomorphism of open regular-level
submanifolds, without changing any point map or normal coordinate.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
namespace ShrunkSurgeryRealization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {s : ℝ} (R : d.ShrunkSurgeryRealization s)

theorem exteriorForward_openExterior (x : R.surgery.oldOpenExterior) :
    R.exteriorForward x.val = (R.surgery.openExteriorHomeomorph x).val.val := by
  have h := R.attachmentHomeomorph_exterior (R.surgery.oldOpenCoordinates x)
  rw [R.surgery.oldExterior_oldOpenCoordinates x] at h
  exact h

theorem exteriorBackward_openExterior (y : R.surgery.newOpenExterior) :
    R.exteriorBackward y.val = (R.surgery.openExteriorHomeomorph.symm y).val.val := by
  apply R.exteriorBackward_eq_of_attachment
  have h := R.attachmentHomeomorph_exterior (R.surgery.newOpenCoordinates y)
  rw [R.surgery.newExterior_newOpenCoordinates y] at h
  exact h

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hR : R.HasSmoothExterior hf)

include hR in
theorem contMDiff_openExteriorHomeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      R.surgery.openExteriorHomeomorph := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply (ContMDiff.subtypeVal_comp_iff R.surgery.newOpenExterior _).mp
  apply (RegularLevel.contMDiff_iff_inclusion hf d.upper_regular
    𝓘(ℝ, RegularLevel.Model E) _).mpr
  have hmaps (x : R.surgery.oldOpenExterior) : x.val.val ∉
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block) := by
    intro hx
    exact x.property ((d.mem_handleRange_iff_mem_oldPiece x.val).mp hx)
  exact (hR.forward.comp_contMDiff contMDiff_subtype_val hmaps).congr
    (fun x => (R.exteriorForward_openExterior x).symm)

include hR in
theorem contMDiff_openExteriorHomeomorph_symm :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
      R.surgery.openExteriorHomeomorph.symm := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply (ContMDiff.subtypeVal_comp_iff R.surgery.oldOpenExterior _).mp
  apply (RegularLevel.contMDiff_iff_inclusion hf d.lower_regular
    𝓘(ℝ, RegularLevel.Model E) _).mpr
  have hmaps (y : R.surgery.newOpenExterior) : R.exteriorBackward y.val ∉
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block) := by
    rw [R.exteriorBackward_openExterior y]
    intro hy
    exact (R.surgery.openExteriorHomeomorph.symm y).property
      ((d.mem_handleRange_iff_mem_oldPiece _).mp hy)
  exact (hR.backward.comp_contMDiff contMDiff_subtype_val hmaps).congr
    (fun y => (R.exteriorBackward_openExterior y).symm)

def openExteriorDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      R.surgery.oldOpenExterior R.surgery.newOpenExterior ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact {
    toEquiv := R.surgery.openExteriorHomeomorph.toEquiv
    contMDiff_toFun := R.contMDiff_openExteriorHomeomorph hf hR
    contMDiff_invFun := R.contMDiff_openExteriorHomeomorph_symm hf hR }

theorem openExteriorDiffeomorph_toHomeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (R.openExteriorDiffeomorph hf hR).toHomeomorph = R.surgery.openExteriorHomeomorph := rfl

end ShrunkSurgeryRealization
end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
