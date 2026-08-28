import Wikipedia.SmoothSixDPoincare.BeltSurgeryNeighborhood

/-!
# Closed belt tubes in the original surgery neighborhood

The tube is specified intrinsically by the actual surgery-coordinate target
and the fixed original Morse normal projection. Its coordinates are exactly
the positive sphere times a closed normal disk. Whenever that disk fits the
coordinate source, the tube is a compact embedded product in the actual level.
-/

noncomputable section

open Set Metric Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def closedBeltTube (ε : ℝ) : Set d.UpperLevel :=
  {y | y ∈ d.beltSurgeryTarget ∧ ‖d.radius⁻¹ • d.beltNormal y‖ ≤ ε}

open Classical in
theorem closedBeltTube_mono {ε δ : ℝ} (h : ε ≤ δ) :
    d.closedBeltTube ε ⊆ d.closedBeltTube δ := fun _ hy => ⟨hy.1, hy.2.trans h⟩

open Classical in
theorem beltSurgeryHomeomorph_mem_closedBeltTube_iff (ε : ℝ) (z : d.beltSurgerySource) :
    (d.beltSurgeryHomeomorph z).val ∈ d.closedBeltTube ε ↔ ‖z.val.2‖ ≤ ε := by
  change ((d.beltSurgeryHomeomorph z).val ∈ d.beltSurgeryTarget ∧
    ‖d.radius⁻¹ • d.beltNormal (d.beltSurgeryHomeomorph z).val‖ ≤ ε) ↔ _
  rw [d.beltNormal_beltSurgeryHomeomorph, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  exact and_iff_right (d.beltSurgeryHomeomorph z).property

open Classical in
/-- Intrinsic tube membership is precisely membership in the original bounded product chart. -/
theorem mem_closedBeltTube_iff_exists (ε : ℝ) (y : d.UpperLevel) :
    y ∈ d.closedBeltTube ε ↔ ∃ z : d.beltSurgerySource,
      ‖z.val.2‖ ≤ ε ∧ (d.beltSurgeryHomeomorph z).val = y := by
  constructor
  · intro hy
    let z := d.beltSurgeryHomeomorph.symm ⟨y, hy.1⟩
    refine ⟨z, ?_, ?_⟩
    · change ‖(d.beltSurgeryHomeomorph.symm ⟨y, hy.1⟩).val.2‖ ≤ ε
      rw [d.beltSurgeryHomeomorph_inverse_normal]
      exact hy.2
    · exact congrArg (fun w : d.beltSurgeryTarget => w.val)
        (d.beltSurgeryHomeomorph.apply_symm_apply ⟨y, hy.1⟩)
  · rintro ⟨z, hz, rfl⟩
    exact (d.beltSurgeryHomeomorph_mem_closedBeltTube_iff ε z).mpr hz

open Classical in
def closedBeltTubeMap (ε : ℝ)
    (hsource : (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
      closedBall (0 : d.chart.NegativeCoordinates) ε ⊆ d.beltSurgerySource) :
    ContinuousMap (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates ×
      closedBall (0 : d.chart.NegativeCoordinates) ε) d.UpperLevel where
  toFun z := (d.beltSurgeryHomeomorph
    ⟨(z.1, z.2.val), hsource ⟨mem_univ z.1, z.2.property⟩⟩).val
  continuous_toFun := continuous_subtype_val.comp
    (d.beltSurgeryHomeomorph.continuous.comp
      ((continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _))

open Classical in
theorem closedBeltTubeMap_range (ε : ℝ)
    (hsource : (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
      closedBall (0 : d.chart.NegativeCoordinates) ε ⊆ d.beltSurgerySource) :
    range (d.closedBeltTubeMap ε hsource) = d.closedBeltTube ε := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact (d.beltSurgeryHomeomorph_mem_closedBeltTube_iff ε
      ⟨(z.1, z.2.val), hsource ⟨mem_univ z.1, z.2.property⟩⟩).mpr
        (mem_closedBall_zero_iff.mp z.2.property)
  · intro hy
    obtain ⟨z, hz, heq⟩ := (d.mem_closedBeltTube_iff_exists ε y).mp hy
    exact ⟨(z.val.1, ⟨z.val.2, mem_closedBall_zero_iff.mpr hz⟩), heq⟩

open Classical in
theorem closedBeltTubeMap_injective (ε : ℝ)
    (hsource : (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
      closedBall (0 : d.chart.NegativeCoordinates) ε ⊆ d.beltSurgerySource) :
    Injective (d.closedBeltTubeMap ε hsource) := by
  intro z w heq
  have hh : d.beltSurgeryHomeomorph
      ⟨(z.1, z.2.val), hsource ⟨mem_univ z.1, z.2.property⟩⟩ =
        d.beltSurgeryHomeomorph ⟨(w.1, w.2.val), hsource ⟨mem_univ w.1, w.2.property⟩⟩ :=
    Subtype.ext heq
  have hp := congrArg (fun u : d.beltSurgerySource => u.val)
    (d.beltSurgeryHomeomorph.injective hh)
  apply Prod.ext
  · exact congrArg
      (fun u : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates ×
        d.chart.NegativeCoordinates => u.1) hp
  · exact Subtype.ext (congrArg
      (fun u : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates ×
        d.chart.NegativeCoordinates => u.2) hp)

open Classical in
theorem isCompact_closedBeltTube (ε : ℝ)
    (hsource : (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
      closedBall (0 : d.chart.NegativeCoordinates) ε ⊆ d.beltSurgerySource) :
    IsCompact (d.closedBeltTube ε) := by
  rw [← d.closedBeltTubeMap_range ε hsource]
  exact isCompact_range (d.closedBeltTubeMap ε hsource).continuous

variable [T2Space M]

open Classical in
theorem closedBeltTubeMap_isClosedEmbedding (ε : ℝ)
    (hsource : (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
      closedBall (0 : d.chart.NegativeCoordinates) ε ⊆ d.beltSurgerySource) :
    IsClosedEmbedding (d.closedBeltTubeMap ε hsource) :=
  (d.closedBeltTubeMap ε hsource).continuous.isClosedEmbedding
    (d.closedBeltTubeMap_injective ε hsource)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
