import Wikipedia.SmoothSixDPoincare.OpenMorseAttachingFace

/-!
# An open coordinate neighborhood of the entire closed attaching face

Use every sphere-times-vector coordinate whose curved image lies in the
original Morse chart. This open domain contains the entire closed
sphere-times-unit-disk face. Its image is exactly the original lower level
inside the original Morse chart, with the original coordinates as inverse.
-/

noncomputable section

open Set Metric Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (c : SignedMorseChart (E := E) f p)

open Classical in
def attachingRawCoordinates (ρ : ℝ)
    (z : PuncturedHandle.UnitSphere c.NegativeCoordinates × c.PositiveCoordinates) :
    c.NegativeCoordinates × c.PositiveCoordinates :=
  MorseHandle.ambientMap ρ ((z.1 : c.NegativeCoordinates), z.2)

open Classical in
theorem continuous_attachingRawCoordinates (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.attachingRawCoordinates ρ) :=
  (MorseHandle.ambientHomeomorph ρ hρ).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

open Classical in
def attachingSource (ρ : ℝ) (hρ : 0 < ρ) :
    Opens (PuncturedHandle.UnitSphere c.NegativeCoordinates × c.PositiveCoordinates) :=
  ⟨c.attachingRawCoordinates ρ ⁻¹' c.splitChart.target,
    c.splitChart.open_target.preimage (c.continuous_attachingRawCoordinates ρ hρ)⟩

open Classical in
def attachingTarget (ρ : ℝ) : Opens {y : M // f y = f p - ρ ^ 2} :=
  ⟨Subtype.val ⁻¹' c.splitChart.source,
    c.splitChart.open_source.preimage continuous_subtype_val⟩

open Classical in
def attachingNeighborhoodMap (ρ : ℝ) (hρ : 0 < ρ) (z : c.attachingSource ρ hρ) :
    c.attachingTarget ρ :=
  ⟨⟨c.splitChart.symm (c.attachingRawCoordinates ρ z.val), by
      rw [c.splitChart_inverse_equation z.property]
      have hh := MorseHandle.ambientMap_lower_sphere hρ z.val.1 z.val.2
      change -‖(c.attachingRawCoordinates ρ z.val).1‖ ^ 2 +
        ‖(c.attachingRawCoordinates ρ z.val).2‖ ^ 2 = -(ρ ^ 2) at hh
      linarith⟩,
    c.splitChart.map_target' z.property⟩

open Classical in
theorem continuous_attachingNeighborhoodMap (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.attachingNeighborhoodMap ρ hρ) := by
  have hc : Continuous (fun z : c.attachingSource ρ hρ =>
      c.splitChart.symm (c.attachingRawCoordinates ρ z.val)) :=
    c.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      ((c.continuous_attachingRawCoordinates ρ hρ).comp continuous_subtype_val)
      (fun z => z.property)
  exact (hc.subtype_mk _).subtype_mk _

open Classical in
theorem attachingInverseCoordinates_neighborhoodMap (ρ : ℝ) (hρ : 0 < ρ)
    (z : c.attachingSource ρ hρ) :
    c.attachingInverseCoordinates ρ ((c.attachingNeighborhoodMap ρ hρ z).val : M) =
      ((z.val.1 : c.NegativeCoordinates), z.val.2) := by
  have hr : c.splitChart (c.splitChart.symm (c.attachingRawCoordinates ρ z.val)) =
      c.attachingRawCoordinates ρ z.val := c.splitChart.right_inv' z.property
  change MorseHandle.ambientInverse ρ
    (c.splitChart (c.splitChart.symm (c.attachingRawCoordinates ρ z.val))) = _
  rw [hr]
  exact MorseHandle.ambientInverse_ambientMap hρ _

open Classical in
def attachingNeighborhoodInverse (ρ : ℝ) (hρ : 0 < ρ) (y : c.attachingTarget ρ) :
    c.attachingSource ρ hρ := by
  let u : PuncturedHandle.UnitSphere c.NegativeCoordinates :=
    ⟨(c.attachingInverseCoordinates ρ (y.val : M)).1, mem_sphere_zero_iff_norm.mpr
      (c.norm_attachingInverseCoordinates_fst ρ hρ y.val y.property)⟩
  refine ⟨(u, (c.attachingInverseCoordinates ρ (y.val : M)).2), ?_⟩
  change MorseHandle.ambientMap ρ
    (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M))) ∈ c.splitChart.target
  rw [MorseHandle.ambientMap_ambientInverse hρ]
  exact c.splitChart.map_source' y.property

open Classical in
theorem continuous_attachingNeighborhoodInverse (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (c.attachingNeighborhoodInverse ρ hρ) := by
  have hc : Continuous (fun y : c.attachingTarget ρ =>
      c.attachingInverseCoordinates ρ (y.val : M)) :=
    (c.continuousOn_attachingInverseCoordinates ρ hρ).comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val) (fun y => y.property)
  exact ((hc.fst.subtype_mk _).prodMk hc.snd).subtype_mk _

open Classical in
/-- The entire valid attaching neighborhood, extending past the closed transverse disk. -/
def attachingNeighborhoodHomeomorph (ρ : ℝ) (hρ : 0 < ρ) :
    c.attachingSource ρ hρ ≃ₜ c.attachingTarget ρ where
  toFun := c.attachingNeighborhoodMap ρ hρ
  invFun := c.attachingNeighborhoodInverse ρ hρ
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst
        (c.attachingInverseCoordinates_neighborhoodMap ρ hρ z))
    · exact congrArg (fun w : c.NegativeCoordinates × c.PositiveCoordinates => w.2)
        (c.attachingInverseCoordinates_neighborhoodMap ρ hρ z)
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change c.splitChart.symm
      (MorseHandle.ambientMap ρ (MorseHandle.ambientInverse ρ (c.splitChart (y.val : M)))) =
        (y.val : M)
    rw [MorseHandle.ambientMap_ambientInverse hρ]
    exact c.splitChart.left_inv' y.property
  continuous_toFun := c.continuous_attachingNeighborhoodMap ρ hρ
  continuous_invFun := c.continuous_attachingNeighborhoodInverse ρ hρ

open Classical in
/-- A fixed positive margin is available around the entire closed attaching face. -/
theorem enlarged_closed_attachingFace_subset_source (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    (univ : Set (PuncturedHandle.UnitSphere c.NegativeCoordinates)) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (3 / 2 : ℝ) ⊆ c.attachingSource ρ hρ := by
  rintro ⟨u, v⟩ ⟨_, hv⟩
  exact hblock (MorseHandle.ambientMap_sphere_mem_product hρ u v
    (mem_closedBall_zero_iff.mp hv))

open Classical in
/-- The open coordinate domain contains the whole closed attaching face, including its edge. -/
theorem closed_attachingFace_subset_source (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    (univ : Set (PuncturedHandle.UnitSphere c.NegativeCoordinates)) ×ˢ
      closedBall (0 : c.PositiveCoordinates) 1 ⊆ c.attachingSource ρ hρ := by
  rintro ⟨u, v⟩ ⟨_, hv⟩
  exact hblock (MorseHandle.modelMap_mem_product
    (N := c.NegativeCoordinates) (P := c.PositiveCoordinates) hρ
    (⟨(u : c.NegativeCoordinates), sphere_subset_closedBall u.property⟩, ⟨v, hv⟩))

open Classical in
def closedAttachingPoint (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates)
    (v : MorseHandle.UnitDisk c.PositiveCoordinates) : c.attachingSource ρ hρ :=
  ⟨(u, (v : c.PositiveCoordinates)), c.closed_attachingFace_subset_source ρ hρ hblock
    ⟨mem_univ u, v.property⟩⟩

open Classical in
/-- On every closed-face point the neighborhood map is exactly the original attaching map. -/
theorem attachingNeighborhoodHomeomorph_face (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (u : PuncturedHandle.UnitSphere c.NegativeCoordinates)
    (v : MorseHandle.UnitDisk c.PositiveCoordinates) :
    ((c.attachingNeighborhoodHomeomorph ρ hρ (c.closedAttachingPoint ρ hρ hblock u v)).val : M) =
      (c.attachingBoundaryMap ρ hρ hblock (u, v) : M) := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
