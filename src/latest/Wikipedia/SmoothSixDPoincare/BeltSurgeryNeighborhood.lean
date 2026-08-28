import Wikipedia.SmoothSixDPoincare.SmoothBeltNeighborhood
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalCoordinates
import Wikipedia.SmoothSixDPoincare.SurgeryInteriorCoordinates
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# Native belt coordinates inside the actual surgery piece

Restrict the original smooth Morse coordinates to the open interior of the
actual new surgery piece. Compactness of the entire belt gives a uniform
positive normal radius in this restricted domain. The zero section and normal
projection retain their original parametrizations.
-/

noncomputable section

open Set Metric Function Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def beltSurgerySource :
    Opens (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates) :=
  ⟨Subtype.val '' ((fun z : d.chart.beltSource d.radius d.radius_pos =>
      (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos z).val) ⁻¹'
        d.surgery.NewInterior),
    (d.chart.beltSource d.radius d.radius_pos).isOpen.isOpenMap_subtype_val _
      (d.surgery.isOpen_newInterior.preimage (continuous_subtype_val.comp
        (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous))⟩

open Classical in
theorem mem_beltSurgerySource_iff
    (z : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates) :
    z ∈ d.beltSurgerySource ↔ ∃ hz : z ∈ d.chart.beltSource d.radius d.radius_pos,
      (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos ⟨z, hz⟩).val ∈
        d.surgery.NewInterior := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.property, hw⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, h, rfl⟩

open Classical in
theorem beltSurgerySource_subset :
    (d.beltSurgerySource :
      Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates)) ⊆
        d.chart.beltSource d.radius d.radius_pos := by
  intro z hz
  exact ((d.mem_beltSurgerySource_iff z).mp hz).choose

open Classical in
def beltSurgeryTarget : Opens d.UpperLevel :=
  ⟨d.beltNormalDomain ∩ d.surgery.NewInterior,
    d.isOpen_beltNormalDomain.inter d.surgery.isOpen_newInterior⟩

open Classical in
def beltSurgeryMap (z : d.beltSurgerySource) : d.beltSurgeryTarget :=
  ⟨(d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
    ⟨z.val, d.beltSurgerySource_subset z.property⟩).val,
    (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
      ⟨z.val, d.beltSurgerySource_subset z.property⟩).property,
    ((d.mem_beltSurgerySource_iff z.val).mp z.property).choose_spec⟩

open Classical in
def beltSurgeryInverse (y : d.beltSurgeryTarget) : d.beltSurgerySource := by
  let w := (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm
    ⟨y.val, y.property.1⟩
  refine ⟨w.val, (d.mem_beltSurgerySource_iff w.val).mpr ⟨w.property, ?_⟩⟩
  change (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
    ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm
      ⟨y.val, y.property.1⟩)).val ∈ d.surgery.NewInterior
  rw [Homeomorph.apply_symm_apply]
  exact y.property.2

open Classical in
def beltSurgeryHomeomorph : d.beltSurgerySource ≃ₜ d.beltSurgeryTarget where
  toFun := d.beltSurgeryMap
  invFun := d.beltSurgeryInverse
  left_inv z := by
    apply Subtype.ext
    exact congrArg
      (fun w : d.chart.beltSource d.radius d.radius_pos => w.val)
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).symm_apply_apply
        ⟨z.val, d.beltSurgerySource_subset z.property⟩)
  right_inv y := by
    apply Subtype.ext
    exact congrArg (fun w : d.chart.beltTarget d.radius => w.val)
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).apply_symm_apply
        ⟨y.val, y.property.1⟩)
  continuous_toFun := by
    have hi : Continuous (fun z : d.beltSurgerySource =>
        (⟨z.val, d.beltSurgerySource_subset z.property⟩ :
          d.chart.beltSource d.radius d.radius_pos)) := continuous_subtype_val.subtype_mk _
    exact (continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp hi)).subtype_mk _
  continuous_invFun := by
    have hi : Continuous (fun y : d.beltSurgeryTarget =>
        (⟨y.val, y.property.1⟩ : d.chart.beltTarget d.radius)) :=
      continuous_subtype_val.subtype_mk _
    let e := d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
    exact (continuous_subtype_val.comp (e.symm.continuous.comp hi)).subtype_mk _

open Classical in
theorem belt_zero_mem_surgerySource (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (v, (0 : d.chart.NegativeCoordinates)) ∈ d.beltSurgerySource := by
  apply (d.mem_beltSurgerySource_iff _).mpr
  refine ⟨(d.chart.beltZeroPoint d.radius d.radius_pos d.block v).property, ?_⟩
  change (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
    (d.chart.beltZeroPoint d.radius d.radius_pos d.block v)).val ∈ d.surgery.NewInterior
  rw [d.chart.beltNeighborhoodHomeomorph_zero, ← d.belt_eq]
  exact d.surgery.beltSphere_mem_newInterior v

open Classical in
/-- A uniform positive closed normal disk fits around the whole belt inside the new piece. -/
theorem exists_pos_beltSurgery_radius :
    ∃ ε : ℝ, 0 < ε ∧
      (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
        closedBall (0 : d.chart.NegativeCoordinates) ε ⊆ d.beltSurgerySource := by
  apply DiskFraming.exists_pos_prod_closedBall_subset isCompact_univ d.beltSurgerySource.isOpen
  rintro ⟨v, u⟩ ⟨_, hu⟩
  rcases mem_singleton_iff.mp hu with rfl
  exact d.belt_zero_mem_surgerySource v

open Classical in
theorem beltSurgeryHomeomorph_zero (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (d.beltSurgeryHomeomorph ⟨(v, 0), d.belt_zero_mem_surgerySource v⟩).val =
      d.surgery.beltSphere v := by
  rw [d.belt_eq]
  exact d.chart.beltNeighborhoodHomeomorph_zero d.radius d.radius_pos d.block v

open Classical in
theorem beltNormal_beltSurgeryHomeomorph (z : d.beltSurgerySource) :
    d.beltNormal (d.beltSurgeryHomeomorph z).val = d.radius • z.val.2 :=
  d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos
    ⟨z.val, d.beltSurgerySource_subset z.property⟩

open Classical in
theorem beltSurgeryHomeomorph_inverse_normal (y : d.beltSurgeryTarget) :
    (d.beltSurgeryHomeomorph.symm y).val.2 = d.radius⁻¹ • d.beltNormal y.val := rfl

open Classical in
/-- The zero normal coordinate detects exactly the actual belt, not a replacement sphere. -/
theorem beltSurgeryHomeomorph_mem_belt_iff (z : d.beltSurgerySource) :
    (d.beltSurgeryHomeomorph z).val ∈ range d.surgery.beltSphere ↔ z.val.2 = 0 := by
  rw [← d.beltNormal_eq_zero_iff (d.beltSurgeryHomeomorph z).property.1,
    d.beltNormal_beltSurgeryHomeomorph]
  exact smul_eq_zero_iff_right d.radius_pos.ne'

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- Restricting to the actual new piece retains the native smooth structure in both directions. -/
def beltSurgeryDiffeomorph (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
      𝓘(ℝ, RegularLevel.Model E) d.beltSurgerySource d.beltSurgeryTarget ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let e := d.chart.beltNeighborhoodDiffeomorph hf n d.radius d.radius_pos d.upper_regular
  refine {
    toEquiv := d.beltSurgeryHomeomorph.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · have hi : ContMDiff ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
        ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates)) ∞
        (fun z : d.beltSurgerySource =>
          (⟨z.val, d.beltSurgerySource_subset z.property⟩ :
            d.chart.beltSource d.radius d.radius_pos)) :=
      (ContMDiff.subtypeVal_comp_iff (d.chart.beltSource d.radius d.radius_pos) _).mp
        contMDiff_subtype_val
    have hout : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
        (Subtype.val : d.chart.beltTarget d.radius → d.UpperLevel) := contMDiff_subtype_val
    exact (ContMDiff.subtypeVal_comp_iff d.beltSurgeryTarget _).mp
      (hout.comp (e.contMDiff.comp hi))
  · have hi : ContMDiff 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E) ∞
        (fun y : d.beltSurgeryTarget =>
          (⟨y.val, y.property.1⟩ : d.chart.beltTarget d.radius)) :=
      (ContMDiff.subtypeVal_comp_iff (d.chart.beltTarget d.radius) _).mp contMDiff_subtype_val
    have hout : ContMDiff ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
        ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates)) ∞
        (Subtype.val : d.chart.beltSource d.radius d.radius_pos →
          PuncturedHandle.UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates) :=
      contMDiff_subtype_val
    exact (ContMDiff.subtypeVal_comp_iff d.beltSurgerySource _).mp
      (hout.comp (e.symm.contMDiff.comp hi))

open Classical in
theorem beltSurgeryDiffeomorph_zero (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates,
      (d.beltSurgeryDiffeomorph hf n ⟨(v, 0), d.belt_zero_mem_surgerySource v⟩).val =
        d.surgery.beltSphere v := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact d.beltSurgeryHomeomorph_zero

open Classical in
theorem beltNormal_beltSurgeryDiffeomorph (n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)] :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    ∀ z : d.beltSurgerySource,
      d.beltNormal (d.beltSurgeryDiffeomorph hf n z).val = d.radius • z.val.2 := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact d.beltNormal_beltSurgeryHomeomorph

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
