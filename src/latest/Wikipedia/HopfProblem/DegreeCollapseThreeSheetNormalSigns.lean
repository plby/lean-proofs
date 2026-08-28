import Wikipedia.SmoothSixDPoincare.TubularBigonIntersectionSigns
import Wikipedia.SmoothSixDPoincare.IntersectionCoordinateOrder
import Wikipedia.SmoothSixDPoincare.NormalDetectorIntersectionSigns
import Wikipedia.SmoothSixDPoincare.StripNormalDetectorField

/-!
# The actual three/three Whitney corner signs and a fixed normal map

The retained upper strip chart supplies a continuous family of complements.
A fixed surjective native normal detector annihilating that sheet compares
the full corner determinants to the normal determinants in the retained
lower chart. All coordinate-order and complement-orientation factors cancel
between the two corners, rather than being assumed to have a chosen sign.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open WhitneyPairModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
  (tube : TubularBigon (E := E) S T a b k l h)
  (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3)) (E := E) S k)
  (e : StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 3)) (E := E) T l)

theorem opposite_three_sheet_corners_iff_normal_determinants
    (q : M → (ℝ × EuclideanSpace ℝ (Fin 2))) {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ q O)
    (hzero : ∀ y ∈ T ∩ O, q y = 0)
    (hcenter : ∀ t ∈ Icc (0 : ℝ) 1, e.chart (StripCoordinates.center t) ∈ O)
    (hqs : ∀ t ∈ Icc (0 : ℝ) 1, Surjective
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) q
        (e.chart (StripCoordinates.center t)))) :
    (tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) ↔
      (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 2) => q (d.chart (w, 0))) (0, 0)).det *
        (fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 2) => q (d.chart (w, 0))) (1, 0)).det < 0 := by
  let i : (ℝ × EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let j := IntersectionCoordinates.pairCoordinates normalPairCoordinates
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
  have hdet (t : ℝ) : tube.sheetPairDet d e t =
      (j.symm.toContinuousLinearMap.comp ((G t).coprod (L t))).det :=
    IntersectionCoordinates.det_jointBlock_eq_tangentSum normalPairCoordinates (G t) (L t)
  have hcoeff (t : ℝ) (ht : t = 0 ∨ t = 1) : (Q t).comp (L t) =
      fderiv ℝ (fun w : ℝ × EuclideanSpace ℝ (Fin 2) => q (d.chart (w, 0))) (t, 0) := by
    have htI : t ∈ Icc (0 : ℝ) 1 := by rcases ht with rfl | rfl <;> simp
    have hpoint := tube.corner_sheet_charts_coincide d e ht
    have hqD : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2)) ∞ q
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

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
