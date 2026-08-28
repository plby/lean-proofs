import Wikipedia.SmoothSixDPoincare.SmoothMorseSurgery
import Wikipedia.SmoothSixDPoincare.MorseBeltNeighborhood
import Wikipedia.SmoothSixDPoincare.MorseBeltFaceFlow
import Wikipedia.SmoothSixDPoincare.SurgeryInteriorCoordinates

/-!
# The actual new surgery piece in native belt coordinates

The constructed attachment follows the exact controlled Morse flow. After
the explicit radial homeomorphism of the negative disk, its entire new
piece is therefore the original smooth belt-coordinate map. This includes
the whole closed disk, not just the zero section or a germ near it.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
/-- The actual radial change of negative disk coordinates, in surgery's
norm-ball parametrization. -/
def beltFaceCoordinates :
    PuncturedHandle.UnitBall d.chart.NegativeCoordinates ≃ₜ
      PuncturedHandle.UnitBall d.chart.NegativeCoordinates :=
  (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).trans
    (MorseHandle.beltFaceDiskHomeomorph.trans
      (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates).symm)

open Classical in
theorem beltFaceCoordinates_apply (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates) :
    (d.beltFaceCoordinates u).val = MorseHandle.beltFaceMap u.val := rfl

open Classical in
theorem beltFaceCoordinates_boundary (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
    (hu : ‖u.val‖ = 1) : d.beltFaceCoordinates u = u :=
  Subtype.ext (MorseHandle.beltFaceMap_eq_self_of_norm_eq_one hu)

open Classical in
theorem beltFaceCoordinates_norm_eq_one_iff
    (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates) :
    ‖(d.beltFaceCoordinates u).val‖ = 1 ↔ ‖u.val‖ = 1 := by
  constructor
  · intro h
    have hfix := d.beltFaceCoordinates_boundary (d.beltFaceCoordinates u) h
    have heq : d.beltFaceCoordinates u = u := d.beltFaceCoordinates.injective hfix
    rwa [heq] at h
  · intro h
    rw [d.beltFaceCoordinates_boundary u h]
    exact h

open Classical in
/-- Every point of the full closed unit normal disk lies in the native belt chart. -/
def beltClosedDiskPoint
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.chart.beltSource d.radius d.radius_pos :=
  ⟨(z.2, z.1.val), d.chart.enlarged_closed_belt_subset_source
    d.radius d.radius_pos d.block
      ⟨mem_univ _, mem_closedBall_zero_iff.mpr (z.1.property.trans (by norm_num))⟩⟩

open Classical in
/-- Native smooth belt coordinates on the entire closed normal disk. -/
def beltClosedDiskMap :
    C(PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates, d.UpperLevel) where
  toFun z := (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
    (d.beltClosedDiskPoint z)).val
  continuous_toFun := by
    have hc : Continuous d.beltClosedDiskPoint :=
      (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    exact continuous_subtype_val.comp
      ((d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos).continuous.comp hc)

open Classical in
/-- The whole actual new piece agrees with the native belt map after the
constructed disk homeomorphism. -/
theorem newPiece_beltFaceCoordinates
    (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.surgery.newPiece (d.beltFaceCoordinates u, v) = d.beltClosedDiskMap (u, v) := by
  let ud := MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates u
  let vd : MorseHandle.UnitDisk d.chart.PositiveCoordinates :=
    ⟨v.val, mem_closedBall_zero_iff.mpr (mem_sphere_zero_iff_norm.mp v.property).le⟩
  have hv : ‖vd.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  let z := (MorseHandle.beltFaceDiskMap ud, vd)
  let x : ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) :=
    ⟨d.chart.attachingHandleMap d.radius d.radius_pos d.block z, Or.inr ⟨z, rfl⟩⟩
  have hnew : (d.surgery.newPiece (d.beltFaceCoordinates u, v) : M) =
      (d.attachmentHomeomorph x).val := d.newPiece_eq _
  have hfront : x.val ∈ frontier ({y | f y ≤ f p - d.radius ^ 2} ∪
      range (d.chart.attachingHandleMap d.radius d.radius_pos d.block)) := by
    apply (d.attachment_frontier x).mp
    rw [← hnew]
    exact (d.surgery.newPiece (d.beltFaceCoordinates u, v)).property
  have htgt := d.block (MorseHandle.modelMap_mem_product d.radius_pos z)
  have hsource : x.val ∈ d.chart.splitChart.source := d.chart.splitChart.map_target' htgt
  have hcoords : d.chart.splitChart x.val = MorseHandle.modelMap d.radius z :=
    d.chart.splitChart.right_inv' htgt
  have hend : MorseHandle.descentFlow (-MorseHandle.beltFaceTime ‖ud.val‖)
      (d.chart.splitChart x.val) = MorseHandle.beltLevelModel d.radius ud.val vd.val := by
    rw [hcoords]
    exact MorseHandle.descentFlow_neg_beltFaceTime d.radius ud vd hv
  have hpath : ∀ s ∈ uIcc 0 (-MorseHandle.beltFaceTime ‖ud.val‖),
      MorseHandle.descentFlow s (d.chart.splitChart x.val) ∈
        closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
          closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
    intro s hs
    rw [hcoords]
    exact MorseHandle.descentFlow_positiveFace_mem_block d.radius_pos ud vd hv hs
  have hlevel : f (d.chart.splitChart.symm (MorseHandle.descentFlow
      (-MorseHandle.beltFaceTime ‖ud.val‖) (d.chart.splitChart x.val))) =
        f p + d.radius ^ 2 := by
    rw [d.chart.splitChart_inverse_equation (d.block (hpath _ right_mem_uIcc)), hend]
    have hh := MorseHandle.beltLevelModel_height d.radius_pos ud.val hv
    change -‖(MorseHandle.beltLevelModel d.radius ud.val vd.val).1‖ ^ 2 +
      ‖(MorseHandle.beltLevelModel d.radius ud.val vd.val).2‖ ^ 2 = d.radius ^ 2 at hh
    linarith
  have horbit := d.attachment_model_orbits x hfront hsource
    (-MorseHandle.beltFaceTime ‖ud.val‖)
    (neg_nonpos.mpr (MorseHandle.beltFaceTime_nonneg _)) hpath hlevel
  apply Subtype.ext
  rw [hnew, horbit, hend]
  rfl

open Classical in
/-- The native closed belt disk is exactly the new surgery piece as a subset
of the original upper level. -/
theorem range_newPiece_eq_range_beltClosedDiskMap :
    range d.surgery.newPiece = range d.beltClosedDiskMap := by
  ext y
  constructor
  · rintro ⟨⟨u, v⟩, rfl⟩
    refine ⟨(d.beltFaceCoordinates.symm u, v), ?_⟩
    rw [← d.newPiece_beltFaceCoordinates, d.beltFaceCoordinates.apply_symm_apply]
  · rintro ⟨⟨u, v⟩, rfl⟩
    exact ⟨(d.beltFaceCoordinates u, v), d.newPiece_beltFaceCoordinates u v⟩

open Classical in
theorem beltClosedDiskMap_isClosedEmbedding : IsClosedEmbedding d.beltClosedDiskMap := by
  have heq : d.beltClosedDiskMap = d.surgery.newPiece ∘
      (d.beltFaceCoordinates.prodCongr
        (Homeomorph.refl (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates))) := by
    funext z
    exact (d.newPiece_beltFaceCoordinates z.1 z.2).symm
  rw [heq]
  exact d.surgery.newPiece_closed.comp
    (d.beltFaceCoordinates.prodCongr (Homeomorph.refl _)).isClosedEmbedding

open Classical in
/-- The homeomorphism onto the actual new piece has the native belt map as
its underlying point map. -/
def beltClosedDiskHomeomorph :
    (PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) ≃ₜ range d.surgery.newPiece :=
  (d.beltFaceCoordinates.prodCongr (Homeomorph.refl _)).trans
    d.surgery.newPiece_closed.toHomeomorph

open Classical in
theorem beltClosedDiskHomeomorph_coe
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (d.beltClosedDiskHomeomorph z).val = d.beltClosedDiskMap z :=
  d.newPiece_beltFaceCoordinates z.1 z.2

open Classical in
/-- In the original smooth coordinates, the new piece's interior is exactly
the open normal disk, with no additional restrictions inside the closed disk. -/
theorem beltClosedDiskMap_mem_newInterior_iff
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltClosedDiskMap z ∈ d.surgery.NewInterior ↔ ‖z.1.val‖ < 1 := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.surgery.newPiece_mem_newInterior_iff]
  exact MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
