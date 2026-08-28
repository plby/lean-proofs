import Wikipedia.SmoothSixDPoincare.SmoothMorseHandleAmbient
import Wikipedia.SmoothSixDPoincare.MorseAttachingSphereSmooth

/-!
# The interior of the actual thickened attaching face

The original sphere-times-disk attaching map restricts to a homeomorphism
from sphere times open disk onto an explicitly described open subset of the
original lower level. Both inverse coordinates come from the inverse of the
original curved handle map; no replacement framing or sphere map is chosen.
-/

noncomputable section

open Set Metric Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (c : SignedMorseChart (E := E) f p)

open Classical in
def positiveOpenBall : Opens c.PositiveCoordinates := ⟨ball 0 1, isOpen_ball⟩

open Classical in
def attachingInterior (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    C(PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall,
      {y : M // f y = f p - ρ ^ 2}) :=
  (c.attachingBoundaryMap ρ hρ hblock).comp
    ⟨fun z => (z.1, ⟨(z.2 : c.PositiveCoordinates), ball_subset_closedBall z.2.property⟩),
      continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)⟩

open Classical in
theorem attachingInterior_coe (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall) :
    (c.attachingInterior ρ hρ hblock z : M) = c.splitChart.symm
      (MorseHandle.ambientMap ρ
        ((z.1 : c.NegativeCoordinates), (z.2 : c.PositiveCoordinates))) := rfl

open Classical in
theorem attachingInterior_coordinates_mem (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall) :
    MorseHandle.ambientMap ρ ((z.1 : c.NegativeCoordinates), (z.2 : c.PositiveCoordinates)) ∈
      c.splitChart.target :=
  hblock (MorseHandle.modelMap_mem_product
    (N := c.NegativeCoordinates) (P := c.PositiveCoordinates) hρ
    (⟨(z.1 : c.NegativeCoordinates), sphere_subset_closedBall z.1.property⟩,
      ⟨(z.2 : c.PositiveCoordinates), ball_subset_closedBall z.2.property⟩))

open Classical in
def attachingInverseCoordinates (ρ : ℝ) (y : M) :
    c.NegativeCoordinates × c.PositiveCoordinates :=
  MorseHandle.ambientInverse ρ (c.splitChart y)

open Classical in
theorem continuousOn_attachingInverseCoordinates (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn (c.attachingInverseCoordinates ρ) c.splitChart.source :=
  (MorseHandle.ambientHomeomorph ρ hρ).symm.continuous.comp_continuousOn
    c.splitChart.contMDiffOn_toFun.continuousOn

open Classical in
/-- The actual open attaching region in the original lower level. -/
def attachingImage (ρ : ℝ) (hρ : 0 < ρ) : Opens {y : M // f y = f p - ρ ^ 2} where
  carrier := (Subtype.val ⁻¹' c.splitChart.source) ∩
    (fun y => (c.attachingInverseCoordinates ρ (y : M)).2) ⁻¹' ball 0 1
  is_open' := by
    have hc : ContinuousOn
        (fun y : {y : M // f y = f p - ρ ^ 2} => (c.attachingInverseCoordinates ρ y).2)
        (Subtype.val ⁻¹' c.splitChart.source) :=
      (c.continuousOn_attachingInverseCoordinates ρ hρ).snd.comp
        continuous_subtype_val.continuousOn (fun _ hy => hy)
    exact hc.isOpen_inter_preimage (c.splitChart.open_source.preimage continuous_subtype_val)
      isOpen_ball

open Classical in
theorem attachingInverseCoordinates_attachingInterior (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall) :
    c.attachingInverseCoordinates ρ (c.attachingInterior ρ hρ hblock z : M) =
      ((z.1 : c.NegativeCoordinates), (z.2 : c.PositiveCoordinates)) := by
  change MorseHandle.ambientInverse ρ
    (c.splitChart (c.splitChart.symm (MorseHandle.ambientMap ρ
      ((z.1 : c.NegativeCoordinates), (z.2 : c.PositiveCoordinates))))) = _
  have hr : c.splitChart (c.splitChart.symm (MorseHandle.ambientMap ρ
      ((z.1 : c.NegativeCoordinates), (z.2 : c.PositiveCoordinates)))) =
        MorseHandle.ambientMap ρ
          ((z.1 : c.NegativeCoordinates), (z.2 : c.PositiveCoordinates)) :=
    c.splitChart.right_inv' (c.attachingInterior_coordinates_mem ρ hρ hblock z)
  rw [hr]
  exact MorseHandle.ambientInverse_ambientMap hρ _

open Classical in
theorem attachingInterior_mem_image (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (z : PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall) :
    c.attachingInterior ρ hρ hblock z ∈ c.attachingImage ρ hρ := by
  constructor
  · change (c.attachingInterior ρ hρ hblock z : M) ∈ c.splitChart.source
    rw [c.attachingInterior_coe]
    exact c.splitChart.map_target' (c.attachingInterior_coordinates_mem ρ hρ hblock z)
  · change (c.attachingInverseCoordinates ρ (c.attachingInterior ρ hρ hblock z : M)).2 ∈ ball 0 1
    rw [c.attachingInverseCoordinates_attachingInterior]
    exact z.2.property

open Classical in
theorem norm_attachingInverseCoordinates_fst (ρ : ℝ) (hρ : 0 < ρ)
    (y : {y : M // f y = f p - ρ ^ 2}) (hy : (y : M) ∈ c.splitChart.source) :
    ‖(c.attachingInverseCoordinates ρ y).1‖ = 1 := by
  apply MorseHandle.norm_ambientInverse_fst_of_lower hρ
  have hh := c.splitChart_equation hy
  rw [y.property] at hh
  linarith

open Classical in
def attachingInteriorInverse (ρ : ℝ) (hρ : 0 < ρ) (y : c.attachingImage ρ hρ) :
    PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall :=
  (⟨(c.attachingInverseCoordinates ρ y.val).1, mem_sphere_zero_iff_norm.mpr
      (c.norm_attachingInverseCoordinates_fst ρ hρ y.val y.property.1)⟩,
    ⟨(c.attachingInverseCoordinates ρ y.val).2, y.property.2⟩)

open Classical in
theorem continuous_attachingInteriorInverse (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.attachingInteriorInverse ρ hρ) := by
  have hc : Continuous (fun y : c.attachingImage ρ hρ =>
      c.attachingInverseCoordinates ρ (y.val : M)) :=
    (c.continuousOn_attachingInverseCoordinates ρ hρ).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property.1)
  exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)

open Classical in
/-- The full open attaching face is homeomorphic to an actual open subset of the lower level. -/
def attachingInteriorHomeomorph (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    (PuncturedHandle.UnitSphere c.NegativeCoordinates × c.positiveOpenBall) ≃ₜ
      c.attachingImage ρ hρ where
  toFun z := ⟨c.attachingInterior ρ hρ hblock z, c.attachingInterior_mem_image ρ hρ hblock z⟩
  invFun := c.attachingInteriorInverse ρ hρ
  left_inv z := by
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst (c.attachingInverseCoordinates_attachingInterior
        ρ hρ hblock z))
    · exact Subtype.ext (congrArg Prod.snd (c.attachingInverseCoordinates_attachingInterior
        ρ hρ hblock z))
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change c.splitChart.symm
      (MorseHandle.ambientMap ρ (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)))) =
        (y.val : M)
    rw [MorseHandle.ambientMap_ambientInverse hρ]
    exact c.splitChart.left_inv' y.property.1
  continuous_toFun := (c.attachingInterior ρ hρ hblock).continuous.subtype_mk _
  continuous_invFun := c.continuous_attachingInteriorInverse ρ hρ

open Classical in
/-- The entire original core is the zero section of these exact attaching coordinates. -/
theorem attachingInterior_zero (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates) :
    c.attachingInterior ρ hρ hblock (u, ⟨0, by simp [positiveOpenBall]⟩) =
      c.attachingCoreMap ρ hρ hblock u := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
