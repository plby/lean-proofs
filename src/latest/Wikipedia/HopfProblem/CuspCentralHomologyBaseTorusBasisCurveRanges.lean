import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisCurves
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusStrata

/-!
# The component spheres are the three named double curves

The three suspension components have the same indices as the three
unoriented edge directions.  The third chosen hexagon ray is the negative
of its edge direction, which does not change the double-curve locus.  The
range identifications below concern the original cusp quotient and retain
the already specified orientation of each actual component map.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace ToricFan ToricComponent CuspRetraction CuspCollapse

/-- The chosen rays have the same unoriented labels as the actual double curves. -/
theorem thetaEdgeIndex_ray_direction (j : Fin 3) :
    hexagonRay (thetaEdgeIndex j) = edgeDirection j ∨
      hexagonRay (thetaEdgeIndex j) = -edgeDirection j := by
  have h : ∀ j : Fin 3, hexagonRay (thetaEdgeIndex j) = edgeDirection j ∨
      hexagonRay (thetaEdgeIndex j) = -edgeDirection j := by decide
  exact h j

private theorem thetaEdgeIndex_branchPair (j : Fin 3) :
    ∃ v ∈ ({0, hexagonRay (thetaEdgeIndex j)} : Set (Fin 2 → ℤ)),
      v + edgeDirection j ∈ ({0, hexagonRay (thetaEdgeIndex j)} : Set (Fin 2 → ℤ)) := by
  rcases thetaEdgeIndex_ray_direction j with hj | hj
  · refine ⟨0, by simp, ?_⟩
    simp [hj]
  · refine ⟨hexagonRay (thetaEdgeIndex j), by simp, ?_⟩
    simp [hj]

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- Membership in a named double curve is read from the actual branch labels. -/
theorem centralProject_mem_doubleCurve_iff (x : CentralFibre) (j : Fin 3) :
    (centralProject C ε hε x).1 ∈ CuspQuotient.doubleCurve C ε hε j ↔
      ∃ v ∈ branchVertices (x : Space),
        v + edgeDirection j ∈ branchVertices (x : Space) :=
  CuspQuotient.mem_doubleCurve_quotientMap C ε hε _ j

/-- All phases of a chosen edge, including both ends, lie on its named curve. -/
theorem centralProject_thetaEdgeCylinder_mem_doubleCurve (j : Fin 3)
    (t : unitInterval) (z : Circle) :
    (centralProject C ε hε (edgeCylinder (C 0) (thetaEdgeIndex j) (t, z))).1 ∈
      CuspQuotient.doubleCurve C ε hε j := by
  rw [centralProject_mem_doubleCurve_iff]
  by_cases ht0 : t = 0
  · subst t
    rw [edgeCylinder_zero_coe, branchVertices_inclusion]
    exact Triangle.origin_has_edge_direction _ j
  by_cases ht1 : t = 1
  · subst t
    rw [edgeCylinder_one_coe, branchVertices_inclusion]
    exact Triangle.origin_has_edge_direction _ j
  rw [edgeCylinder_branchVertices (C 0) (thetaEdgeIndex j) (t, z) ht0 ht1]
  exact thetaEdgeIndex_branchPair j

/-- The three oriented cylinder components retain exactly their named curve labels. -/
theorem doubleCylinder_thetaCircle_mem_doubleCurve (j : Fin 3)
    (t : unitInterval) (z : Circle) :
    (doubleCylinder C ε hε (t, thetaCircleInclusion j z)).1 ∈
      CuspQuotient.doubleCurve C ε hε j := by
  fin_cases j
  · exact centralProject_thetaEdgeCylinder_mem_doubleCurve C ε hε 0 t z
  · exact centralProject_thetaEdgeCylinder_mem_doubleCurve C ε hε 1
      (unitInterval.symm t) z
  · exact centralProject_thetaEdgeCylinder_mem_doubleCurve C ε hε 2 t z

/-- Within the three chosen cylinders, only their two end slices are triple points. -/
theorem doubleCylinder_thetaCircle_branchCount_eq_three_iff (j : Fin 3)
    (t : unitInterval) (z : Circle) :
    CuspQuotient.branchCount C ε
        (doubleCylinder C ε hε (t, thetaCircleInclusion j z)).1 = 3 ↔
      t = 0 ∨ t = 1 := by
  fin_cases j
  · exact edgeCylinder_branchCount_eq_three_iff (C 0) 0 (t, z)
  · change ToricSpace.branchCount (edgeCylinder (C 0) 1 (unitInterval.symm t, z) : Space) =
      3 ↔ t = 0 ∨ t = 1
    rw [edgeCylinder_branchCount_eq_three_iff]
    simp only [unitInterval.symm_eq_zero, unitInterval.symm_eq_one, or_comm]
  · exact edgeCylinder_branchCount_eq_three_iff (C 0) 2 (t, z)

private theorem thetaCircleInclusion_jointly_surjective (a : ThreeCircles) :
    ∃ j : Fin 3, ∃ z : Circle, thetaCircleInclusion j z = a := by
  rcases a with z | z | z
  · exact ⟨0, z, rfl⟩
  · exact ⟨1, z, rfl⟩
  · exact ⟨2, z, rfl⟩

/-- Every point of a named curve has a representative on the matching chosen cylinder. -/
theorem mem_doubleCurve_iff_doubleCylinder (q : QuotientCentralFibre C ε) (j : Fin 3) :
    q.1 ∈ CuspQuotient.doubleCurve C ε hε j ↔
      ∃ t : unitInterval, ∃ z : Circle,
        doubleCylinder C ε hε (t, thetaCircleInclusion j z) = q := by
  constructor
  · intro hq
    have hboundary : q ∈ centralBoundary C ε hε :=
      (mem_centralBoundary_iff_branchCount C ε hε q).mpr
        (CuspQuotient.branchCount_ge_two_of_mem_doubleCurve C ε hε j hq)
    rw [← range_doubleCylinder_eq_centralBoundary C ε hε] at hboundary
    obtain ⟨⟨t, a⟩, rfl⟩ := hboundary
    obtain ⟨k, z, rfl⟩ := thetaCircleInclusion_jointly_surjective a
    by_cases hkj : k = j
    · subst k
      exact ⟨t, z, rfl⟩
    have htriple : CuspQuotient.branchCount C ε
        (doubleCylinder C ε hε (t, thetaCircleInclusion k z)).1 = 3 := by
      have hboth : (doubleCylinder C ε hε (t, thetaCircleInclusion k z)).1 ∈
          CuspQuotient.doubleCurve C ε hε k ∩ CuspQuotient.doubleCurve C ε hε j :=
        ⟨doubleCylinder_thetaCircle_mem_doubleCurve C ε hε k t z, hq⟩
      rw [CuspQuotient.doubleCurve_inter_eq_triple C ε hε k j hkj] at hboth
      exact hboth
    rcases (doubleCylinder_thetaCircle_branchCount_eq_three_iff C ε hε k t z).mp
      htriple with ht | ht
    · subst t
      exact ⟨0, 1, by simp only [doubleCylinder_zero]⟩
    · subst t
      exact ⟨1, 1, by simp only [doubleCylinder_one]⟩
  · rintro ⟨t, z, rfl⟩
    exact doubleCylinder_thetaCircle_mem_doubleCurve C ε hε j t z

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual component map lands on the same-index named double curve. -/
theorem centralDoubleCurveSphereMap_mem_doubleCurve (j : Fin 3)
    (p : Suspension Circle) :
    (centralDoubleCurveSphereMap C ε hε hε1 hC hR j p).1.1 ∈
      CuspQuotient.doubleCurve C ε hε j := by
  obtain ⟨⟨t, z⟩, rfl⟩ := Suspension.mk_surjective p
  exact doubleCylinder_thetaCircle_mem_doubleCurve C ε hε j t z

/-- The component sphere has exactly the named double curve as its actual central-fibre image. -/
theorem range_centralDoubleCurveSphereMap_central (j : Fin 3) :
    Set.range (fun p : Suspension Circle =>
      (centralDoubleCurveSphereMap C ε hε hε1 hC hR j p).1) =
        (Subtype.val : QuotientCentralFibre C ε → CuspQuotient.QuotientSpace C ε) ⁻¹'
          CuspQuotient.doubleCurve C ε hε j := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact centralDoubleCurveSphereMap_mem_doubleCurve C ε hε hε1 hC hR j p
  · intro hq
    obtain ⟨t, z, hz⟩ := (mem_doubleCurve_iff_doubleCylinder C ε hε q j).mp hq
    exact ⟨Suspension.mk t z, hz⟩

/-- The image equality also holds literally in the original cusp quotient space. -/
theorem range_centralDoubleCurveSphereMap_quotient (j : Fin 3) :
    Set.range (fun p : Suspension Circle =>
      (centralDoubleCurveSphereMap C ε hε hε1 hC hR j p).1.1) =
        CuspQuotient.doubleCurve C ε hε j := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact centralDoubleCurveSphereMap_mem_doubleCurve C ε hε hε1 hC hR j p
  · intro hq
    have hcentral : CuspQuotient.projection C ε q = 0 :=
      CuspQuotient.doubleCurve_subset_central C ε hε j hq
    obtain ⟨t, z, hz⟩ :=
      (mem_doubleCurve_iff_doubleCylinder C ε hε ⟨q, hcentral⟩ j).mp hq
    exact ⟨Suspension.mk t z, congrArg Subtype.val hz⟩

/-- The matching range equality inside the actual double locus. -/
theorem range_centralDoubleCurveSphereMap_boundary (j : Fin 3) :
    Set.range (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) =
      {q : centralBoundary C ε hε | q.1.1 ∈ CuspQuotient.doubleCurve C ε hε j} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact centralDoubleCurveSphereMap_mem_doubleCurve C ε hε hε1 hC hR j p
  · intro hq
    obtain ⟨t, z, hz⟩ := (mem_doubleCurve_iff_doubleCylinder C ε hε q.1 j).mp hq
    exact ⟨Suspension.mk t z, Subtype.ext hz⟩

end Wikipedia.HopfProblem.CuspCentralHomology
