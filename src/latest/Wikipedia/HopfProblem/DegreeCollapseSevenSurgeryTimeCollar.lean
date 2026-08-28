import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryRetainedTimeBand
import Wikipedia.HopfProblem.DegreeCollapseSurgeryTimeProfileBounds
import Wikipedia.HopfProblem.DegreeCollapseTimeCollar

/-!
# The actual seven-dimensional surgery preserves a smaller time collar

Every sufficiently small target time band is precisely the image of the
unchanged old band. The handle has time one and cannot meet this band.
Consequently an explicit collar transports through the original surgery
map, with its original boundary space and literal time coordinate.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def bandRetainedPoint {ε : ℝ} (hε : ε ≤ T.margin / 2) (p : TimeBand T.time ε) :
    retainedTimeBand A T := ⟨p.val, p.property.2.trans_le hε⟩

theorem isOpenEmbedding_bandRetainedPoint {ε : ℝ} (hε : ε ≤ T.margin / 2) :
    IsOpenEmbedding (bandRetainedPoint A T hε) :=
  IsOpenEmbedding.of_comp (bandRetainedPoint A T hε)
    (retainedTimeBand A T).isOpen.isOpenEmbedding_subtypeVal
    (isOpen_Ioo.preimage T.smooth.continuous).isOpenEmbedding_subtypeVal

def smallTimeBandMap {ε : ℝ} (hε : ε ≤ T.margin / 2) :
    TimeBand T.time ε → TimeBand (timeFunction A hR T) ε := fun p ↦
  ⟨retainedTimeMap A hR T (bandRetainedPoint A T hε p), by
    rw [timeFunction_retainedTimeMap]
    exact p.property⟩

theorem smallTimeBandMap_time {ε : ℝ} (hε : ε ≤ T.margin / 2)
    (p : TimeBand T.time ε) :
    timeFunction A hR T (smallTimeBandMap A hR T hε p).val = T.time p.val :=
  timeFunction_retainedTimeMap A hR T _

theorem isOpenEmbedding_smallTimeBandMap {ε : ℝ} (hε : ε ≤ T.margin / 2) :
    IsOpenEmbedding (smallTimeBandMap A hR T hε) := by
  let := targetChartedSpace A hR
  exact IsOpenEmbedding.of_comp (smallTimeBandMap A hR T hε)
    (isOpen_Ioo.preimage (contMDiff_timeFunction A hR T).continuous).isOpenEmbedding_subtypeVal
    ((isOpenEmbedding_retainedTimeMap A hR T).comp
      (isOpenEmbedding_bandRetainedPoint A T hε))

theorem smallTimeBandMap_surjective {ε : ℝ} (hε : ε ≤ T.margin / 2) (hε1 : ε ≤ 1) :
    Surjective (smallTimeBandMap A hR T hε) := by
  rintro ⟨p, hp⟩
  rcases FramedSurgery.cover (E := Vector 4) (face A hR) 3 p with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : T.time q.val ∈ Ioo (-ε) ε :=
      (SurgeryTimeProfile.profile_mem_small_band_iff T.margin_pos hε hε1 _).mp hp
    refine ⟨⟨q.val, hq⟩, ?_⟩
    exact Subtype.ext rfl
  · have hu : (1 : ℝ) < ε := hp.2
    exact (not_lt_of_ge hε1 hu).elim

def smallTimeBandHomeomorph {ε : ℝ} (hε : ε ≤ T.margin / 2) (hε1 : ε ≤ 1) :
    TimeBand T.time ε ≃ₜ TimeBand (timeFunction A hR T) ε :=
  (isOpenEmbedding_smallTimeBandMap A hR T hε).isEmbedding.toHomeomorphOfSurjective
    (smallTimeBandMap_surjective A hR T hε hε1)

theorem smallTimeBandHomeomorph_time {ε : ℝ} (hε : ε ≤ T.margin / 2) (hε1 : ε ≤ 1)
    (p : TimeBand T.time ε) :
    timeFunction A hR T (smallTimeBandHomeomorph A hR T hε hε1 p).val = T.time p.val :=
  smallTimeBandMap_time A hR T hε p

def transportedTimeCollar {B : Type*} [TopologicalSpace B] (C : TimeCollar T.time B)
    (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width)
    (hεm : ε ≤ T.margin / 2) (hε1 : ε ≤ 1) :
    TimeCollar (timeFunction A hR T) B where
  width := ε
  width_pos := hε
  continuous_time := by
    let := targetChartedSpace A hR
    exact (contMDiff_timeFunction A hR T).continuous
  coordinates := (smallTimeBandHomeomorph A hR T hεm hε1).symm.trans
    (C.restrict ε hε hεw).coordinates
  coordinate_time p := by
    change T.time ((smallTimeBandHomeomorph A hR T hεm hε1).symm p).val =
      timeFunction A hR T p.val
    have he := smallTimeBandHomeomorph_time A hR T hεm hε1
      ((smallTimeBandHomeomorph A hR T hεm hε1).symm p)
    rw [Homeomorph.apply_symm_apply] at he
    exact he.symm

theorem transportedTimeCollar_zeroPoint {B : Type*} [TopologicalSpace B]
    (C : TimeCollar T.time B) (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width)
    (hεm : ε ≤ T.margin / 2) (hε1 : ε ≤ 1) (b : B) :
    ((transportedTimeCollar A hR T C ε hε hεw hεm hε1).zeroPoint b).val =
      retainedTimeMap A hR T ⟨(C.zeroPoint b).val, by
        exact zero_mem_retainedTimeBand A T (C.zeroPoint_time b)⟩ := rfl

def preservedTimeCollar {B : Type*} [TopologicalSpace B] (C : TimeCollar T.time B) :
    TimeCollar (timeFunction A hR T) B :=
  transportedTimeCollar A hR T C (min C.width (min (T.margin / 2) 1))
    (lt_min C.width_pos (lt_min (half_pos T.margin_pos) zero_lt_one))
    (min_le_left _ _)
    ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _))

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
