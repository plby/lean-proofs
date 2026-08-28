import Wikipedia.SmoothSixDPoincare.TubularBigonArcDifferential
import Wikipedia.SmoothSixDPoincare.IntersectionBlockDeterminant
import Wikipedia.SmoothSixDPoincare.RankThreeBigonAdaptedFrame

/-!
# Opposite actual corner Jacobians give the required normal-frame sign

At each corner the two native sheet charts have the same value. Their
actual transitions into the inverse tubular chart give the two tangent maps.
One fixed coordinate rearrangement, used at both corners, splits their sum
into disk-tangent and normal blocks. The disk block changes determinant sign
between the corners. Thus opposite corner Jacobians are exactly the same-sign
condition on the normal frames, and give the constructed boundary complement.

This does not prove existence of a pair of opposite intersections from the
homotopy-sphere hypotheses or perform a handle cancellation.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
  (tube : TubularBigon (E := E) S T a b k l h 3)
  (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
  (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)

/-- The actual sheet tangent sum, with the same fixed coordinate order at both corners. -/
def rankThreeSheetPairJacobian (t : ℝ) :
    ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) →L[ℝ]
      ((ℝ × ℝ) × (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1))) :=
  IntersectionCoordinates.jointBlock rankThreePairCoordinates
    (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)

/-- At a corner this is the genuine native intersection Jacobian in the retained sheet charts. -/
def rankThreeSheetPairDet (t : ℝ) : ℝ := (tube.rankThreeSheetPairJacobian d e t).toLinearMap.det

include tube in
/-- At either endpoint the native sheet charts are based at the same actual manifold point. -/
theorem rankThree_corner_sheet_charts_coincide {t : ℝ} (ht : t = 0 ∨ t = 1) :
    d.chart (StripCoordinates.center t) = e.chart (StripCoordinates.center t) := by
  have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
  have hheight : h * (1 - (2 * t - 1) ^ 2) = 0 := by rcases ht with rfl | rfl <;> ring
  have hd := (tube.lower_germ t htI).eq_of_nhds
  have he := (tube.upper_germ t htI).eq_of_nhds
  dsimp only [Function.comp_apply] at hd he
  rw [lowerStripCoordinates_lower, d.center t] at hd
  rw [upperStripCoordinates_upper, e.center t, hheight] at he
  exact hd.symm.trans he

/-- The actual five-dimensional Jacobian has the computed disk factor and original normal frames. -/
theorem rankThreeSheetPairDet_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    tube.rankThreeSheetPairDet d e t = (8 * h * (2 * t - 1)) *
      rankThreePairDet (e.normalFrame tube.chart t) (d.normalFrame tube.chart t) := by
  rw [rankThreeSheetPairDet, rankThreeSheetPairJacobian,
    IntersectionCoordinates.det_jointBlock rankThreePairCoordinates
      (e.sheetDifferential tube.chart t) (d.sheetDifferential tube.chart t)
      (tube.upper_sheetDifferential_arc e ht) (tube.lower_sheetDifferential_arc d ht),
    e.normal_sheetDifferential tube.chart ht (tube.upper_chart_center_mem_target e ht),
    d.normal_sheetDifferential tube.chart ht (tube.lower_chart_center_mem_target d ht)]
  have hplane :
      (PlaneImmersion.linearMap ((2, -4 * h * (2 * t - 1)), (2, 0))).toLinearMap.det =
      8 * h * (2 * t - 1) := by
    rw [← PlanarFrame.determinant_eq_det, PlanarFrame.determinant_linearMap]
    dsimp [PlanarFrame.area]
    ring
  rw [hplane]
  rfl

/-- The disk block converts opposite corner signs to equal normal signs. -/
theorem opposite_rankThree_corner_determinants_iff_normal_sign :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
    (0 < rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
      rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)) := by
  let n := rankThreePairDet (e.normalFrame tube.chart 0) (d.normalFrame tube.chart 0) *
    rankThreePairDet (e.normalFrame tube.chart 1) (d.normalFrame tube.chart 1)
  have hprod : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 =
      -((8 * h) ^ 2 * n) := by
    rw [tube.rankThreeSheetPairDet_eq d e (t := 0) (by simp),
      tube.rankThreeSheetPairDet_eq d e (t := 1) (by simp)]
    dsimp only [n]
    ring
  have hscale : 0 < (8 * h) ^ 2 := sq_pos_of_pos (mul_pos (by norm_num) tube.height_pos)
  change (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔ 0 < n
  rw [hprod]
  constructor
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := by linarith
    exact (mul_pos_iff_of_pos_left hscale).mp hp
  · intro hn
    have hp : 0 < (8 * h) ^ 2 * n := mul_pos hscale hn
    linarith

end Wikipedia.SmoothSixDPoincare.TubularBigon

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  (tube : TubularBigon (E := E) S T a b k.map l.map h 3)
  (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3))
    (E := E) S k.map)
  (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))
    (E := E) T l.map)

/-- Construct the normal line and two-plane with their actual lower/upper sheet restrictions. -/
theorem exists_rankThree_adapted_frame_of_opposite_corner_signs
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ W : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ ∞ W ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        W =ᶠ[𝓝 (2 * t - 1, 0)] (d.normalFrame tube.chart ∘ arcTime)) ∧
      ∃ O : Set (ℝ × ℝ), IsOpen O ∧ bigon h ⊆ O ∧
        ∃ C : (ℝ × ℝ) → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
          ContDiffOn ℝ ∞ C O ∧
          (∀ t ∈ Icc (0 : ℝ) 1,
            C (upperBoundaryArc h t) = e.normalFrame tube.chart t) ∧
          ∀ p ∈ O, Bijective ((W p).coprod (C p)) :=
  tube.exists_rankThree_adapted_frame_of_normal_sign d e
    ((tube.opposite_rankThree_corner_determinants_iff_normal_sign d e).mp hsign)

end Wikipedia.SmoothSixDPoincare.TubularBigon
