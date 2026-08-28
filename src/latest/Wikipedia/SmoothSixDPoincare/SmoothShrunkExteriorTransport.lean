import Wikipedia.SmoothSixDPoincare.ShrunkExteriorSmoothness
import Wikipedia.SmoothSixDPoincare.MorseLowerHandleRange
import Wikipedia.SmoothSixDPoincare.RegularLevelSmoothMapsWithin

/-!
# Smooth transport through the original shrunk exterior

The exact whole-sublevel identity identifies the transported point with
the original shrunk inverse map. Avoiding the whole old surgery piece is
exactly the native handle-range avoidance needed for its smoothness domain.
The conclusion retains the given lower map and its original level atlas.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
namespace ShrunkSurgeryRealization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {a : ℝ} (R : d.ShrunkSurgeryRealization a)

theorem exteriorBackward_eq_of_attachment (x : d.LowerLevel) (y : d.UpperLevel)
    (hmap : (R.attachmentHomeomorph ⟨x.val, Or.inl x.property.le⟩).val = y.val) :
    R.exteriorBackward y = x.val := by
  have h : R.attachmentHomeomorph ⟨x.val, Or.inl x.property.le⟩ =
      ⟨y.val, y.property.le⟩ := Subtype.ext hmap
  have hi := congrArg R.attachmentHomeomorph.symm h
  rw [R.attachmentHomeomorph.symm_apply_apply] at hi
  exact (congrArg Subtype.val hi).symm

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hR : R.HasSmoothExterior hf)
  {G H X : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] (I : ModelWithCorners ℝ G H)
  [TopologicalSpace X] [ChartedSpace H X]

include hR in
theorem contMDiffOn_lowerTransport (L : X → d.LowerLevel) (g : X → d.UpperLevel) (S : Set X)
    (havoid : ∀ x ∈ S, L x ∉ range d.surgery.oldPiece)
    (hmap : ∀ x ∈ S,
      (R.attachmentHomeomorph ⟨(L x).val, Or.inl (L x).property.le⟩).val = (g x).val) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffOn I 𝓘(ℝ, RegularLevel.Model E) ∞ g S →
      ContMDiffOn I 𝓘(ℝ, RegularLevel.Model E) ∞ L S := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  intro hg
  have hlink (x : X) (hx : x ∈ S) : R.exteriorBackward (g x) = (L x).val :=
    R.exteriorBackward_eq_of_attachment (L x) (g x) (hmap x hx)
  have hmaps : MapsTo g S {y | R.exteriorBackward y ∉
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)} := by
    intro x hx
    change R.exteriorBackward (g x) ∉ _
    rw [hlink x hx]
    exact fun h => havoid x hx ((d.mem_handleRange_iff_mem_oldPiece (L x)).mp h)
  apply (RegularLevel.contMDiffOn_iff_inclusion hf d.lower_regular I L S).mpr
  exact (hR.backward.comp hg hmaps).congr (fun x hx => (hlink x hx).symm)

end ShrunkSurgeryRealization
end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
