import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalFormsTransport
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalFormsCoordinates

/-!
# Actual normal-crossing charts on the global cusp fibre

The native normal-crossing charts of the constructed toric cusp quotient
are composed with its actual open parametrization in the glued threefold.
The resulting charts are analytic for the existing global atlas, lie in
the full actual cusp patch, and preserve the exact branch count.  The
coordinate of the global sphere projection is a product of one, two, or
three distinct centered coordinates, with no unit factor.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms

open ToricCharts CuspGeometry

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

/-- The target coordinate is used within its genuine sphere-chart
domain at every point of the full global cusp patch. -/
theorem projectionSphere_mem_sphereChart_of_mem_cuspPatch {y : Threefold.Space}
    (hy : y ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space)) :
    Threefold.projectionSphere y ∈ sphereChart.source := by
  have hyn : y ∈ nativeParametrization.target := by
    simpa only [nativeParametrization_target] using hy
  have he : CuspGeometry.inclusion (nativeParametrization.symm y) = y :=
    nativeParametrization.right_inv' hyn
  rw [← he]
  exact projectionSphere_inclusion_mem_sphereChart_source _

/-- The actual central-fibre chart in the unchanged global threefold
atlas, with the number of coordinate factors equal to the original
quotient-invariant count of branches. -/
theorem normalCrossingChart_with_branchCount (x : LocalSpace) (hx : parameter x = 0) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.card = CuspQuotient.branchCount data.correction data.radius x ∧ J.Nonempty ∧
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, cuspCoordinate (e.symm w) = ∏ j ∈ J, w j := by
  obtain ⟨J, hcard, hJ, h⟩ := CuspQuotient.normalCrossingChart_with_branchCount
    data.correction data.radius data.radius_pos data.radius_lt_one
    data.holomorphic data.smallDrift x hx
  obtain ⟨e, hxs, hzero, hsource, hprod⟩ :=
    exists_transported_normalCrossingChart nativeParametrization
      (f := parameter) (q := cuspCoordinate)
      (by simp only [nativeParametrization_source, mem_univ])
      (fun z _ => cuspCoordinate_inclusion z) h
  refine ⟨J, e, hcard, hJ, hxs, hzero, ?_, hprod⟩
  simpa only [nativeParametrization_target] using hsource

/-- Every actual branch count on the central cusp fibre is one, two,
or three, and the chart has exactly that many coordinate factors. -/
theorem normalCrossingChart_one_two_three (x : LocalSpace) (hx : parameter x = 0) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      (J.card = 1 ∨ J.card = 2 ∨ J.card = 3) ∧
      J.card = CuspQuotient.branchCount data.correction data.radius x ∧
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, cuspCoordinate (e.symm w) = ∏ j ∈ J, w j := by
  obtain ⟨J, e, hcard, hJ, hxs, hzero, hsource, hprod⟩ :=
    normalCrossingChart_with_branchCount x hx
  have hpos : 0 < J.card := Finset.card_pos.mpr hJ
  have hle : J.card ≤ 3 := by simpa using Finset.card_le_card (Finset.subset_univ J)
  exact ⟨J, e, by omega, hcard, hxs, hzero, hsource, hprod⟩

/-- At a point on a single branch the actual local equation is exactly
the first centered coordinate. -/
theorem single_local_equation (x : LocalSpace)
    (hx : CuspQuotient.branchCount data.correction data.radius x = 1) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, cuspCoordinate (e.symm w) = w 0 := by
  have hx0 : parameter x = 0 :=
    (CuspQuotient.branchCount_pos_iff data.correction data.radius x).mp (by omega)
  obtain ⟨J, e, hcard, _, hxs, hzero, hsource, hprod⟩ :=
    normalCrossingChart_with_branchCount x hx0
  obtain ⟨d, hdzero, hdprod⟩ := exists_coordinate_normalization_card_one J (hcard.trans hx)
  exact exists_reindexed_normalForm e hxs hzero hsource hprod d hdzero hdprod

/-- At a point on two branches the actual local equation is exactly
the product of the first two centered coordinates. -/
theorem double_local_equation (x : LocalSpace)
    (hx : CuspQuotient.branchCount data.correction data.radius x = 2) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, cuspCoordinate (e.symm w) = w 0 * w 1 := by
  have hx0 : parameter x = 0 :=
    (CuspQuotient.branchCount_pos_iff data.correction data.radius x).mp (by omega)
  obtain ⟨J, e, hcard, _, hxs, hzero, hsource, hprod⟩ :=
    normalCrossingChart_with_branchCount x hx0
  obtain ⟨d, hdzero, hdprod⟩ := exists_coordinate_normalization_card_two J (hcard.trans hx)
  exact exists_reindexed_normalForm e hxs hzero hsource hprod d hdzero hdprod

/-- At either actual triple point the global cusp equation is precisely
`w 0 * w 1 * w 2` in a chart centered at that point. -/
theorem triple_local_equation (x : LocalSpace)
    (hx : CuspQuotient.branchCount data.correction data.radius x = 3) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, cuspCoordinate (e.symm w) = w 0 * w 1 * w 2 := by
  have hx0 : parameter x = 0 :=
    (CuspQuotient.branchCount_pos_iff data.correction data.radius x).mp (by omega)
  obtain ⟨J, e, hcard, _, hxs, hzero, hsource, hprod⟩ :=
    normalCrossingChart_with_branchCount x hx0
  refine ⟨e, hxs, hzero, hsource, fun w hw => ?_⟩
  exact (hprod w hw).trans (product_eq_three_of_card J (hcard.trans hx) w)

/-- The same normal form is literally an equation for the global map
to the sphere in its constructed cusp chart. -/
theorem sphere_normalCrossingChart_with_branchCount (x : LocalSpace)
    (hx : parameter x = 0) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.card = CuspQuotient.branchCount data.correction data.radius x ∧ J.Nonempty ∧
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j := by
  obtain ⟨J, e, hcard, hJ, hxs, hzero, hsource, hprod⟩ :=
    normalCrossingChart_with_branchCount x hx
  refine ⟨J, e, hcard, hJ, hxs, hzero, hsource, ?_⟩
  intro w hw
  rw [sphereChart_projectionSphere]
  exact hprod w hw

/-- The canonical one-branch form for the actual sphere projection. -/
theorem sphere_single_local_equation (x : LocalSpace)
    (hx : CuspQuotient.branchCount data.correction data.radius x = 1) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 := by
  simpa only [sphereChart_projectionSphere] using single_local_equation x hx

/-- The canonical two-branch form for the actual sphere projection. -/
theorem sphere_double_local_equation (x : LocalSpace)
    (hx : CuspQuotient.branchCount data.correction data.radius x = 2) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target, sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 * w 1 := by
  simpa only [sphereChart_projectionSphere] using double_local_equation x hx

/-- The exact triple-coordinate form for the actual sphere projection. -/
theorem sphere_triple_local_equation (x : LocalSpace)
    (hx : CuspQuotient.branchCount data.correction data.radius x = 3) :
    ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      CuspGeometry.inclusion x ∈ e.source ∧ e (CuspGeometry.inclusion x) = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      ∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = w 0 * w 1 * w 2 := by
  simpa only [sphereChart_projectionSphere] using triple_local_equation x hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms
