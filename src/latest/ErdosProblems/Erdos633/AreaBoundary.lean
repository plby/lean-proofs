import ErdosProblems.Erdos633.BoundaryAdditivity

/-!
# Signed area as a boundary integral

The determinant of a point and the counterclockwise unit direction is
constant along each supporting edge line. Its Hausdorff-length integral
around a triangle is the positive signed double area. This extends the
existing direction-only boundary identities to the area moment needed
to exclude closed nonempty classes of tiles.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators ENNReal

def planeDet (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem planeDet_neg_right (z w : ℂ) : planeDet z (-w) = -planeDet z w := by
  simp [planeDet]
  ring

theorem planeDet_smul_right (z w : ℂ) (t : ℝ) : planeDet z (t • w) = t * planeDet z w := by
  simp [planeDet]
  ring

theorem planeDet_lineMap (a b : ℂ) (t : ℝ) :
    planeDet (AffineMap.lineMap a b t) (b - a) = planeDet a b := by
  simp only [AffineMap.lineMap_apply_module', planeDet, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem Triangle.planeDet_unitEdgeVector_of_mem_edge (P : Triangle) (k : Fin 3)
    {z : ℂ} (hz : z ∈ P.edge k) :
    planeDet z (P.unitEdgeVector k) =
      P.orientationSign / P.sideLength k * planeDet (P.edgeStart k) (P.edgeEnd k) := by
  obtain ⟨t, ht⟩ := (P.barycentric_eq_zero_iff_lineMap k z).mp ((P.mem_edge_iff k z).mp hz).2
  rw [← ht, Triangle.unitEdgeVector, Triangle.orientedEdgeVector,
    planeDet_smul_right, planeDet_smul_right, Triangle.edgeVector, planeDet_lineMap]
  ring

noncomputable def Triangle.areaEdgeDensity (P : Triangle) (k : Fin 3) : ℂ → ℝ :=
  (P.edge k).indicator (fun _ =>
    P.orientationSign / P.sideLength k * planeDet (P.edgeStart k) (P.edgeEnd k))

noncomputable def Triangle.areaBoundaryDensity (P : Triangle) (z : ℂ) : ℝ :=
  ∑ k : Fin 3, P.areaEdgeDensity k z

theorem Triangle.areaBoundaryDensity_eq (P : Triangle) (z : ℂ) :
    P.areaBoundaryDensity z = P.boundaryDensity (planeDet z) z := by
  classical
  apply Finset.sum_congr rfl
  intro k _
  by_cases hz : z ∈ P.edge k
  · rw [Triangle.areaEdgeDensity, Set.indicator_of_mem hz,
      P.edgeDensity_of_mem (planeDet z) k hz, P.planeDet_unitEdgeVector_of_mem_edge k hz]
  · rw [Triangle.areaEdgeDensity, Set.indicator_of_notMem hz,
      P.edgeDensity_of_not_mem (planeDet z) k hz]

theorem Triangle.integrable_areaEdgeDensity (P : Triangle) (k : Fin 3) :
    Integrable (P.areaEdgeDensity k) (μH[1] : Measure ℂ) := by
  rw [Triangle.areaEdgeDensity, integrable_indicator_iff (P.measurableSet_edge k)]
  have hfinite : (μH[1] : Measure ℂ) (P.edge k) ≠ ⊤ := by
    rw [P.hausdorffMeasure_edge]
    exact ENNReal.ofReal_ne_top
  exact integrableOn_const hfinite

theorem Triangle.integrable_areaBoundaryDensity (P : Triangle) :
    Integrable P.areaBoundaryDensity (μH[1] : Measure ℂ) := by
  exact integrable_finsetSum Finset.univ (fun k _ => P.integrable_areaEdgeDensity k)

theorem Triangle.integral_areaEdgeDensity (P : Triangle) (k : Fin 3) :
    (∫ z, P.areaEdgeDensity k z ∂(μH[1] : Measure ℂ)) =
      P.orientationSign * planeDet (P.edgeStart k) (P.edgeEnd k) := by
  rw [Triangle.areaEdgeDensity, integral_indicator_const _ (P.measurableSet_edge k)]
  change ((μH[1] : Measure ℂ) (P.edge k)).toReal *
      (P.orientationSign / P.sideLength k * planeDet (P.edgeStart k) (P.edgeEnd k)) = _
  rw [P.hausdorffMeasure_edge_toReal]
  field_simp [ne_of_gt (P.sideLength_pos k)]

theorem Triangle.integral_areaBoundaryDensity (P : Triangle) :
    (∫ z, P.areaBoundaryDensity z ∂(μH[1] : Measure ℂ)) =
      P.orientationSign * orientedDoubleArea P.a P.b P.c := by
  unfold Triangle.areaBoundaryDensity
  rw [integral_finsetSum Finset.univ (fun k _ => P.integrable_areaEdgeDensity k)]
  simp_rw [P.integral_areaEdgeDensity]
  simp [Fin.sum_univ_succ, Triangle.edgeStart, Triangle.edgeEnd, planeDet,
    orientedDoubleArea]
  ring

theorem TriangleDissection.areaBoundaryDensity_ae_eq_sum
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) :
    P.areaBoundaryDensity =ᵐ[(μH[1] : Measure ℂ)]
      fun z => ∑ i : Fin N, (T.tile i).areaBoundaryDensity z := by
  let : NullSingletonClass (μH[1] : Measure ℂ) :=
    Measure.nullSingletonClass_hausdorff ℂ (by norm_num)
  have hv := T.vertexFinset.finite_toSet.countable.ae_notMem (μH[1] : Measure ℂ)
  filter_upwards [hv] with z hz
  simp_rw [Triangle.areaBoundaryDensity_eq]
  exact T.boundaryDensity_eq_sum_of_not_vertex (planeDet z) (planeDet_neg_right z) hz

end Erdos633
