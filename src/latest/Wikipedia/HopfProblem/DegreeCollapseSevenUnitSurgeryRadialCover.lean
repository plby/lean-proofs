import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryCoordinates

/-!
# Radial representatives covering canonical unit surgery

Above the smaller handle radius, a tube radius determines a point in the
actual rounded-collar window. Below that radius, the canonical radial
exchange determines a point in the actual handle window.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel SevenRoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

def collarParametersOfRadius (s : Sphere 3) (w : Sphere 3) (r : ℝ)
    (hlo : handleCoreRadius A ≤ r) (hhi : r < A.radius) : boundaryCollarParameters A :=
  ⟨(s, w, r ^ 2 - 1), (mem_boundaryCollarParameters_iff_interval A _).mpr (by
    constructor
    · change -collarHeight A < r ^ 2 - 1
      nlinarith [handleCoreRadius_sq A, twice_outer_lt_height A, handleCoreRadius_pos A]
    · change r ^ 2 - 1 < radialGap A
      rw [radialGap_eq_three A hR]
      rw [hR] at hhi
      nlinarith [handleCoreRadius_pos A])⟩

omit [T2Space M] in
theorem collarOriginalVector_ofRadius (s : Sphere 3) (w : Sphere 3) (r : ℝ)
    (hlo : handleCoreRadius A ≤ r) (hhi : r < A.radius) :
    collarOriginalVector A (collarParametersOfRadius A hR s w r hlo hhi) = r • w.val := by
  change Real.sqrt (1 + (r ^ 2 - 1)) • w.val = _
  rw [show 1 + (r ^ 2 - 1) = r ^ 2 by ring,
    Real.sqrt_sq (le_trans (handleCoreRadius_pos A).le hlo)]

theorem collarPoint_ofTube (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) A.radius) (hne : v ≠ 0)
    (hlo : handleCoreRadius A ≤ ‖v‖) (hhi : ‖v‖ < A.radius) :
    collarPoint A hR (collarParametersOfRadius A hR s
      (SphereRadialRetraction.retract (pole 3) v) ‖v‖ hlo hhi) =
        oldTubePoint A hR s hv hne := by
  apply Subtype.ext
  change A.tube (s, collarOriginalVector A _) = A.tube (s, v)
  rw [collarOriginalVector_ofRadius, SphereRadialRetraction.retract, dif_neg hne,
    NormedSpace.norm_smul_normalize]

def overlapHandleParameters (z : FramedSurgery.Overlap (Vector 4) (Vector 4))
    (hz : ‖z.2.val‖ < handleCoreRadius A) : boundaryHandleParameters A :=
  ⟨((FramedSurgery.newOverlap (E := Vector 4) (F := Vector 4) 3 3 z).1.val,
      (FramedSurgery.newOverlap (E := Vector 4) (F := Vector 4) 3 3 z).2),
    (mem_boundaryHandleParameters_iff A _).mpr (by
      rw [mem_ball, dist_zero_right, FramedSurgery.newOverlap_fst, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), ClosedHemisphere.unit_norm, mul_one]
      exact hz)⟩

omit [T2Space M] in
theorem handlePoint_overlapHandleParameters
    (z : FramedSurgery.Overlap (Vector 4) (Vector 4)) (hz : ‖z.2.val‖ < handleCoreRadius A) :
    handlePoint A (overlapHandleParameters A z hz) =
      FramedSurgery.newOverlap (E := Vector 4) (F := Vector 4) 3 3 z := rfl

theorem oldTubeMap_mem_handle (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) A.radius) (hne : v ≠ 0)
    (hlo : ‖v‖ < handleCoreRadius A) :
    FramedSurgery.oldMap (E := Vector 4) (face A hR) 3 (oldTubePoint A hR s hv hne) ∈
      range (handleMap A hR) := by
  let z : FramedSurgery.Overlap (Vector 4) (Vector 4) :=
    (s, ⟨v, hne, hlo.trans (handleCoreRadius_lt_one A)⟩)
  refine ⟨overlapHandleParameters A z hlo, ?_⟩
  change FramedSurgery.newMap (E := Vector 4) (face A hR) 3
    (handlePoint A (overlapHandleParameters A z hlo)) = _
  rw [handlePoint_overlapHandleParameters]
  exact (FramedSurgery.overlap_identification (E := Vector 4) (face A hR) 3 z).symm

theorem newPoint_mem_collar (q : FramedSurgery.NewPatch (Vector 4) (Vector 4))
    (hlo : handleCoreRadius A ≤ ‖q.1.val‖) :
    FramedSurgery.newMap (E := Vector 4) (face A hR) 3 q ∈ range (collarMap A hR) := by
  have hpos : 0 < ‖q.1.val‖ := lt_of_lt_of_le (handleCoreRadius_pos A) hlo
  have hne : q.1.val ≠ 0 := norm_pos_iff.mp hpos
  have hlt : ‖q.1.val‖ < 1 := mem_ball_zero_iff.mp q.1.property
  have hhi : ‖q.1.val‖ < A.radius := by rw [hR]; linarith
  let s := SphereRadialRetraction.retract (pole 3) q.1.val
  let p := collarParametersOfRadius A hR s q.2 ‖q.1.val‖ hlo hhi
  have hv : ‖‖q.1.val‖ • q.2.val‖ = ‖q.1.val‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      ClosedHemisphere.unit_norm, mul_one]
  let z : FramedSurgery.Overlap (Vector 4) (Vector 4) :=
    (s, ⟨‖q.1.val‖ • q.2.val, norm_pos_iff.mp (by rw [hv]; exact hpos), by rw [hv]; exact hlt⟩)
  have hold : FramedSurgery.oldOverlap (E := Vector 4) (face A hR) z = collarPoint A hR p := by
    apply Subtype.ext
    change A.tube (s, ‖q.1.val‖ • q.2.val) = A.tube (s, collarOriginalVector A p)
    rw [collarOriginalVector_ofRadius]
  have hnew : FramedSurgery.newOverlap (E := Vector 4) (F := Vector 4) 3 3 z = q := by
    apply Prod.ext
    · apply Subtype.ext
      change ‖‖q.1.val‖ • q.2.val‖ •
        (SphereRadialRetraction.retract (pole 3) q.1.val).val = q.1.val
      rw [hv, SphereRadialRetraction.retract, dif_neg hne, NormedSpace.norm_smul_normalize]
    · apply Subtype.ext
      change ‖‖q.1.val‖ • q.2.val‖⁻¹ • (‖q.1.val‖ • q.2.val) = q.2.val
      rw [hv, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  refine ⟨p, ?_⟩
  have he := FramedSurgery.overlap_identification (E := Vector 4) (face A hR) 3 z
  rw [hold, hnew] at he
  exact he

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
