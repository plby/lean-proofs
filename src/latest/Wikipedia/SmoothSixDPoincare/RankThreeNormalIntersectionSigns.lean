import Wikipedia.SmoothSixDPoincare.RankThreeBigonIntersectionSigns
import Wikipedia.SmoothSixDPoincare.IntersectionCoordinateOrder
import Wikipedia.SmoothSixDPoincare.NormalDetectorIntersectionSigns
import Wikipedia.SmoothSixDPoincare.StripNormalDetectorField

/-!
# The actual rank-three Whitney corner signs and a fixed sheet normal map

The retained upper strip chart constructs a smooth complement to the belt
tangent columns. A fixed native normal map vanishing on that sheet gives a
smooth surjective detector. The full corner determinant signs are therefore
equivalent to the normal-coordinate determinant signs in the retained lower
sheet chart. All tube and sheet coordinate-order factors are retained.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
  (tube : TubularBigon (E := E) S T a b k l h 3)
  (d : StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
  (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T l)

/-- Opposite Whitney corner determinants are exactly opposite fixed normal determinants in
the actual lower sheet chart; the upper chart's sign factors are proved to cancel. -/
theorem opposite_rankThree_corners_iff_normal_sheet_determinants
    (q : M → (ℝ × EuclideanSpace ℝ (Fin 1))) {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q O)
    (hzero : ∀ y ∈ T ∩ O, q y = 0)
    (hcenter : ∀ t ∈ Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ O)
    (hqs : ∀ t ∈ Icc (0 : ℝ) 1, Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) q
        (e.chart (StripCoordinates.center t)))) :
    (tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (0, 0)).det *
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (1, 0)).det < 0 := by
  let i : (ℝ × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let j := IntersectionCoordinates.pairCoordinates rankThreePairCoordinates
  let G := e.sheetDifferential tube.chart
  let L := d.sheetDifferential tube.chart
  let C (t : ℝ) := (e.sheetComplement tube.chart t).comp i.toContinuousLinearMap
  let Q := e.normalDetector tube.chart q
  have htarget : ∀ t ∈ Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ tube.chart.target :=
    fun _ ht => tube.upper_chart_center_mem_target e ht
  have hG : ContDiffOn ℝ ∞ G (Icc (0 : ℝ) 1) :=
    (e.contDiffOn_sheetDifferential tube.chart).mono (fun t ht => ⟨e.line ht, htarget t ht⟩)
  have hC : ContDiffOn ℝ ∞ C (Icc (0 : ℝ) 1) :=
    ((e.contDiffOn_sheetComplement tube.chart).mono
      (fun t ht => ⟨e.line ht, htarget t ht⟩)).clm_comp contDiffOn_const
  have hQ : ContDiffOn ℝ ∞ Q (Icc (0 : ℝ) 1) :=
    e.contDiffOn_normalDetector tube.chart q hO hq htarget hcenter
  have hi : ∀ t ∈ Icc (0 : ℝ) 1, ((G t).coprod (C t)).IsInvertible := by
    intro t ht
    let p := ContinuousLinearEquiv.prodCongr
      (ContinuousLinearEquiv.refl ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) i
    have heq : (G t).coprod (C t) =
        ((e.sheetDifferential tube.chart t).coprod (e.sheetComplement tube.chart t)).comp
          p.toContinuousLinearMap := by
      apply ContinuousLinearMap.ext
      intro z
      rfl
    apply FrameField.isInvertible_coprod_of_bijective
    rw [heq]
    exact (e.isInvertible_sheet_coprod_complement tube.chart ht (htarget t ht)).bijective.comp
      p.bijective
  have hQs : ∀ t ∈ Icc (0 : ℝ) 1, Surjective (Q t) := fun t ht =>
    e.surjective_normalDetector tube.chart q (htarget t ht)
      (hq.contMDiffAt (hO.mem_nhds (hcenter t ht))) (hqs t ht)
  have hQG : ∀ t ∈ Icc (0 : ℝ) 1, (Q t).comp (G t) = 0 := fun t ht =>
    e.normalDetector_comp_sheet_eq_zero tube.chart q hO hq hzero ht (htarget t ht) (hcenter t ht)
  have hsign := opposite_intersectionDet_iff_normalDet j G C L Q hG hC hQ hi hQs hQG
  have hdet (t : ℝ) : tube.rankThreeSheetPairDet d e t =
      (j.symm.toContinuousLinearMap.comp ((G t).coprod (L t))).det :=
    IntersectionCoordinates.det_jointBlock_eq_tangentSum rankThreePairCoordinates (G t) (L t)
  have hcoeff (t : ℝ) (ht : t = 0 ∨ t = 1) : (Q t).comp (L t) =
      fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 1) => q (d.chart (w, 0))) (t, 0) := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
    have hpoint := tube.rankThree_corner_sheet_charts_coincide d e ht
    have hqD : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 1)) ∞ q
        (d.chart (StripCoordinates.center t)) :=
      hpoint.symm ▸ hq.contMDiffAt (hO.mem_nhds (hcenter t htI))
    have hQeq : Q t = d.normalDetector tube.chart q t := by
      change e.normalDetector tube.chart q t = d.normalDetector tube.chart q t
      unfold StripNormalData.normalDetector
      rw [hpoint]
    rw [hQeq]
    exact d.normalDetector_comp_sheet tube.chart q htI
      (tube.lower_chart_center_mem_target d htI) hqD
  rw [hdet 0, hdet 1]
  exact hsign.trans (by rw [hcoeff 0 (Or.inl rfl), hcoeff 1 (Or.inr rfl)])

end Wikipedia.SmoothSixDPoincare.TubularBigon
