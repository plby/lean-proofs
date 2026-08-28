import Wikipedia.SmoothSixDPoincare.NativeAttachingPatchMembership
import Wikipedia.SmoothSixDPoincare.MorseAnnularModelFlow
import Wikipedia.SmoothSixDPoincare.MorseBeltNeighborhood

/-!
# Native lower and upper coordinates on an annulus crossing the surgery corner

The positive normal radius lies strictly between `1/2` and `3/2`. Both
native neighborhoods contain these coordinates. The lower map avoids the
removed core, and the upper map has the exact quadratic-orbit coordinates.
-/

noncomputable section

open Set Function Topology TopologicalSpace Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

namespace MorseHandle

variable (V : Type*) [NormedAddCommGroup V]

def openSurgeryAnnulus : Opens V :=
  ⟨{v | (1 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < (3 / 2 : ℝ)},
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)⟩

variable {V}

theorem surgeryAnnulus_norm_pos (v : openSurgeryAnnulus V) : 0 < ‖v.val‖ := by
  have h := v.property.1
  linarith

theorem surgeryAnnulus_ne_zero (v : openSurgeryAnnulus V) : v.val ≠ 0 :=
  norm_pos_iff.mp (surgeryAnnulus_norm_pos v)

variable [NormedSpace ℝ V]

def annularDirection : C(openSurgeryAnnulus V, PuncturedHandle.UnitSphere V) :=
  ⟨fun v => ⟨‖v.val‖⁻¹ • v.val,
    mem_sphere_zero_iff_norm.mpr (norm_annularDirection (surgeryAnnulus_ne_zero v))⟩,
    (((continuous_norm.comp continuous_subtype_val).inv₀
      (fun v => (surgeryAnnulus_norm_pos v).ne')).smul continuous_subtype_val).subtype_mk _⟩

abbrev AnnularParameters (N P : Type*) [NormedAddCommGroup N] [NormedAddCommGroup P] :=
  PuncturedHandle.UnitSphere N × openSurgeryAnnulus P

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def annularBeltCoordinates : C(AnnularParameters N P, PuncturedHandle.UnitSphere P × N) :=
  ⟨fun z => (annularDirection (V := P) z.2, ‖z.2.val‖ • z.1.val),
    ((annularDirection (V := P)).continuous.comp continuous_snd).prodMk
      ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).smul
        (continuous_subtype_val.comp continuous_fst))⟩

theorem norm_annularBeltCoordinates_snd (z : AnnularParameters N P) :
    ‖(annularBeltCoordinates z).2‖ = ‖z.2.val‖ := by
  change ‖‖z.2.val‖ • z.1.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z.2.val),
    mem_sphere_zero_iff_norm.mp z.1.property, mul_one]

end MorseHandle

namespace ManifoldMorse.MorseSurgeryData

open PuncturedHandle FramedSurgery MorseHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def annularAttachingPoint :
    C(AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.chart.attachingSource d.radius d.radius_pos) :=
  ⟨fun z => ⟨(z.1, z.2.val),
    d.chart.enlarged_closed_attachingFace_subset_source d.radius d.radius_pos d.block
      ⟨mem_univ _, mem_closedBall_zero_iff.mpr z.2.property.2.le⟩⟩,
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

open Classical in
theorem annularBeltCoordinates_mem
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    annularBeltCoordinates z ∈ d.chart.beltSource d.radius d.radius_pos := by
  apply d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
  refine ⟨mem_univ _, mem_closedBall_zero_iff.mpr ?_⟩
  rw [norm_annularBeltCoordinates_snd]
  exact z.2.property.2.le

open Classical in
def annularBeltPoint :
    C(AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.chart.beltSource d.radius d.radius_pos) :=
  ⟨fun z => ⟨annularBeltCoordinates z, d.annularBeltCoordinates_mem z⟩,
    (annularBeltCoordinates (N := d.chart.NegativeCoordinates)
      (P := d.chart.PositiveCoordinates)).continuous.subtype_mk _⟩

open Classical in
def annularLowerPoint :
    C(AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates, d.LowerLevel) :=
  ⟨fun z => (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos
    (d.annularAttachingPoint z)).val,
    continuous_subtype_val.comp ((d.chart.attachingNeighborhoodHomeomorph
      d.radius d.radius_pos).continuous.comp d.annularAttachingPoint.continuous)⟩

open Classical in
def annularUpperPoint :
    C(AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates, d.UpperLevel) :=
  ⟨fun z => (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (d.annularBeltPoint z)).val,
    continuous_subtype_val.comp ((d.chart.beltNeighborhoodHomeomorph
      d.radius d.radius_pos).continuous.comp d.annularBeltPoint.continuous)⟩

open Classical in
theorem annularLowerPoint_coordinates
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.chart.splitChart (d.annularLowerPoint z).val =
      ambientMap d.radius (z.1.val, z.2.val) :=
  d.chart.splitChart.right_inv' (d.annularAttachingPoint z).property

open Classical in
theorem annularUpperPoint_model
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    (d.annularUpperPoint z).val =
      d.chart.splitChart.symm (annularUpperModel d.radius z.1.val z.2.val) := rfl

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
theorem annularLowerPoint_mem_oldPatch :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.annularLowerPoint z ∈ oldPatch (d.attachingSmoothFace hf m) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  exact (d.attachingNeighborhood_mem_oldPatch_iff hf m (d.annularAttachingPoint z)).mpr
    (surgeryAnnulus_ne_zero z.2)

open Classical in
theorem annularLowerPoint_mem_faceInterior_iff :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.annularLowerPoint z ∈ faceInterior (d.attachingSmoothFace hf m) ↔ ‖z.2.val‖ < 1 := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  exact d.attachingNeighborhood_mem_faceInterior_iff hf m (d.annularAttachingPoint z)

open Classical in
def annularOldPoint :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    C(AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      oldPatch (d.attachingSmoothFace hf m)) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  exact ⟨fun z => ⟨d.annularLowerPoint z, d.annularLowerPoint_mem_oldPatch hf m z⟩,
    d.annularLowerPoint.continuous.subtype_mk _⟩

end ManifoldMorse.MorseSurgeryData

end Wikipedia.SmoothSixDPoincare
