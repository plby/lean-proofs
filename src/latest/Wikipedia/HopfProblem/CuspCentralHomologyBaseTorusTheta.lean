import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorus
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseForget
import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusHomeomorph
import Wikipedia.HopfProblem.CuspCentralHomologyBoundaryLoopNullhomotopy

/-!
# The actual base projection on the double locus factors through theta

The first three straight dual edges, with the middle one reversed, define a
map from the literal theta suspension to the marked product torus. Their
endpoint identifications follow from the actual toric corner orbits. On the
central double locus the original base projection is precisely this map
after forgetting the circle phase. Consequently its induced maps on
integral singular homology vanish in every degree at least two.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspHoneycombTiling
open CuspHoneycombHexagon PeriodTorusHigherHomology SingularMayerVietoris

local notation "Plane" => CuspHoneycombTiling.Plane

/-- A straight side of the actual dual honeycomb cell, with its original orientation. -/
def dualSidePoint (k : Fin 6) (t : unitInterval) : Plane :=
  dualStandardPlaneHomeomorph.symm (sideIntervalHomeomorph k t : Plane)

@[simp] theorem dualSidePoint_apply (k : Fin 6) (t : unitInterval) :
    dualSidePoint k t =
      dualStandardPlaneHomeomorph.symm (sideIntervalHomeomorph k t : Plane) := rfl

theorem dualSidePoint_continuous (k : Fin 6) : Continuous (dualSidePoint k) :=
  dualStandardPlaneHomeomorph.symm.continuous.comp
    (continuous_subtype_val.comp (sideIntervalHomeomorph k).continuous)

/-- Compatibility changes the positive arc, but not its planar side coordinate. -/
theorem edgeArcBase_eq_dualSidePoint (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    (edgeArcBase C₀ k t : Plane) = dualSidePoint k t := by
  have h : edgeArcBase C₀ k t = standardHexagonDualHomeomorph
      ⟨(sideIntervalHomeomorph k t : Plane), (sideIntervalHomeomorph k t).2.1⟩ := by
    apply (compatibleCellHomeomorph C₀).injective
    rw [compatibleCellHomeomorph_edgeArcBase, compatibleCellHomeomorph_sideInterval]
  exact congrArg Subtype.val h

/-- The three chosen dual edges, all directed from the odd pole to the even pole. -/
def orientedEdgeBasePoint (t : unitInterval) (j : Fin 3) : Plane :=
  dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)

@[simp] theorem orientedEdgeBasePoint_zero (t : unitInterval) :
    orientedEdgeBasePoint t 0 = dualSidePoint 0 t := by
  simp [orientedEdgeBasePoint]

@[simp] theorem orientedEdgeBasePoint_one (t : unitInterval) :
    orientedEdgeBasePoint t 1 = dualSidePoint 1 (unitInterval.symm t) := by
  simp [orientedEdgeBasePoint]

@[simp] theorem orientedEdgeBasePoint_two (t : unitInterval) :
    orientedEdgeBasePoint t 2 = dualSidePoint 2 t := by
  simp [orientedEdgeBasePoint]

theorem orientedEdgeBasePoint_continuous (j : Fin 3) :
    Continuous (fun t => orientedEdgeBasePoint t j) := by
  by_cases hj : j = 1
  · simpa only [orientedEdgeBasePoint, if_pos hj, Function.comp_def] using
      (dualSidePoint_continuous (thetaEdgeIndex j)).comp unitInterval.continuous_symm
  · simpa only [orientedEdgeBasePoint, if_neg hj] using
      dualSidePoint_continuous (thetaEdgeIndex j)

/-- The marked base coordinate on the three oriented interval representatives. -/
def thetaBaseCylinder (p : unitInterval × Fin 3) : ProductTorus 2 :=
  baseTorusPoint (orientedEdgeBasePoint p.1 p.2)

@[simp] theorem thetaBaseCylinder_apply (t : unitInterval) (j : Fin 3) :
    thetaBaseCylinder (t, j) = baseTorusPoint (orientedEdgeBasePoint t j) := rfl

theorem thetaBaseCylinder_continuous : Continuous thetaBaseCylinder :=
  continuous_prod_of_discrete_right.mpr fun j =>
    baseTorusPoint_continuous.comp (orientedEdgeBasePoint_continuous j)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The original central base projection forgets the phase on every actual edge cylinder. -/
@[simp] theorem baseTorusProjection_edgeCylinder (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    baseTorusProjection C r hr (centralProject C r hr (edgeCylinder (C 0) k (t, a))) =
      baseTorusPoint (dualSidePoint k t) := by
  have h : centralProject C r hr (edgeCylinder (C 0) k (t, a)) =
      honeycombCollapseMap C r hr
        (hexagonCharacterSection k a, (edgeArcBase (C 0) k t : Plane)) := by
    change centralCollapseMap C r hr
      (hexagonCharacterSection k a, edgeArcPositive (C 0) k t) =
        centralCollapseMap C r hr (hexagonCharacterSection k a,
          honeycombHomeomorph (C 0) (edgeArcBase (C 0) k t : Plane))
    rw [honeycombHomeomorph_edgeArcBase]
  rw [h, baseTorusProjection_honeycombCollapseMap, edgeArcBase_eq_dualSidePoint]

theorem baseTorusProjection_doubleCylinder (p : unitInterval × ThreeCircles) :
    baseTorusProjection C r hr (doubleCylinder C r hr p) =
      thetaBaseCylinder (p.1, thetaCircleLabel p.2) := by
  rcases p with ⟨t, a | (a | a)⟩ <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      baseTorusProjection_edgeCylinder, thetaCircleLabel_inl, thetaCircleLabel_inr_inl,
      thetaCircleLabel_inr_inr, thetaBaseCylinder_apply, orientedEdgeBasePoint_zero,
      orientedEdgeBasePoint_one, orientedEdgeBasePoint_two]

theorem thetaBaseCylinder_respects (p q : unitInterval × Fin 3)
    (h : (suspensionSetoid (Fin 3)).r p q) : thetaBaseCylinder p = thetaBaseCylinder q := by
  have h' : (suspensionSetoid ThreeCircles).r
      (p.1, thetaCircleInclusion p.2 1) (q.1, thetaCircleInclusion q.2 1) := by
    rcases h with ⟨ht, hzero | hone | hj⟩
    · exact ⟨ht, Or.inl hzero⟩
    · exact ⟨ht, Or.inr (Or.inl hone)⟩
    · exact ⟨ht, Or.inr (Or.inr (congrArg (fun j => thetaCircleInclusion j 1) hj))⟩
  have he := congrArg (baseTorusProjection (fun _ => 0) 1 zero_lt_one)
    (doubleCylinder_respects (fun _ => 0) 1 zero_lt_one _ _ h')
  simpa only [baseTorusProjection_doubleCylinder, thetaCircleLabel_inclusion] using he

@[simp] theorem thetaBaseCylinder_zero (j : Fin 3) :
    thetaBaseCylinder (0, j) = thetaBaseCylinder (0, 0) :=
  thetaBaseCylinder_respects _ _ ⟨rfl, Or.inl rfl⟩

@[simp] theorem thetaBaseCylinder_one (j : Fin 3) :
    thetaBaseCylinder (1, j) = thetaBaseCylinder (1, 0) :=
  thetaBaseCylinder_respects _ _ ⟨rfl, Or.inr (Or.inl rfl)⟩

private def thetaBaseMapFun : Theta → ProductTorus 2 :=
  Quotient.lift thetaBaseCylinder thetaBaseCylinder_respects

private theorem thetaBaseMapFun_continuous : Continuous thetaBaseMapFun :=
  (Suspension.isQuotientMap_mk (X := Fin 3)).continuous_iff.mpr
    thetaBaseCylinder_continuous

/-- The actual marked base map on the literal three-edge theta graph. -/
def thetaBaseMap : C(Theta, ProductTorus 2) :=
  ⟨thetaBaseMapFun, thetaBaseMapFun_continuous⟩

@[simp] theorem thetaBaseMap_mk (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) = thetaBaseCylinder (t, j) := rfl

theorem thetaBaseMap_mk_point (t : unitInterval) (j : Fin 3) :
    thetaBaseMap (Suspension.mk t j) = baseTorusPoint
      (dualSidePoint (thetaEdgeIndex j) (if j = 1 then unitInterval.symm t else t)) := rfl

@[simp] theorem thetaBaseMap_mk_zero (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 0) = baseTorusPoint (dualSidePoint 0 t) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_zero]

@[simp] theorem thetaBaseMap_mk_one (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 1) =
      baseTorusPoint (dualSidePoint 1 (unitInterval.symm t)) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_one]

@[simp] theorem thetaBaseMap_mk_two (t : unitInterval) :
    thetaBaseMap (Suspension.mk t 2) = baseTorusPoint (dualSidePoint 2 t) := by
  simp only [thetaBaseMap_mk, thetaBaseCylinder_apply, orientedEdgeBasePoint_two]

theorem thetaBaseMap_continuous : Continuous thetaBaseMap := thetaBaseMap.continuous

theorem thetaBaseMap_homology_eq_zero (n : ℕ) :
    singularHomologyMap thetaBaseMap (n + 2) = 0 := by
  let := theta_homology_subsingleton n
  exact Subsingleton.elim _ _

theorem baseTorusProjection_doubleSuspensionMap (q : ThreeCircleSuspension) :
    baseTorusProjection C r hr (doubleSuspensionMap C r hr q) =
      thetaBaseMap (thetaForgetCircle q) := by
  obtain ⟨⟨t, a⟩, rfl⟩ := Suspension.mk_surjective q
  rw [doubleSuspensionMap_mk, baseTorusProjection_doubleCylinder,
    thetaForgetCircle_mk, thetaBaseMap_mk]

variable (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- Pointwise factorization on the literal central double locus. -/
theorem baseTorusProjection_boundary (q : centralBoundary C r hr) :
    baseTorusProjection C r hr (q : QuotientCentralFibre C r) =
      thetaBaseMap (thetaForgetCircle
        (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR q)) := by
  obtain ⟨p, rfl⟩ :=
    (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR).symm.surjective q
  rw [Homeomorph.apply_symm_apply, centralBoundarySuspensionHomeomorph_symm_coe]
  exact baseTorusProjection_doubleSuspensionMap C r hr p

/-- The factorization is an equality of the actual continuous maps, not only
of their induced homology maps. -/
theorem baseTorusProjectionMap_comp_boundaryInclusion :
    (baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr) =
      thetaBaseMap.comp (thetaForgetCircle.comp
        (centralBoundarySuspensionHomeomorph C r hr hr1 hC hR :
          C(centralBoundary C r hr, ThreeCircleSuspension))) := by
  apply ContinuousMap.ext
  intro q
  exact baseTorusProjection_boundary C r hr hr1 hC hR q

include hr1 hR

/-- The restriction of the original base projection to the actual double
locus induces zero in every integral singular homology degree at least two. -/
theorem baseTorusProjection_boundary_homology_eq_zero (n : ℕ) :
    singularHomologyMap
      ((baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr))
      (n + 2) = 0 := by
  rw [baseTorusProjectionMap_comp_boundaryInclusion C r hr hr1 hC hR,
    singularHomologyMap_comp, thetaBaseMap_homology_eq_zero, LinearMap.zero_comp]

theorem baseTorusProjection_boundary_homology_two_eq_zero :
    singularHomologyMap
      ((baseTorusProjectionMap C r hr hC).comp (centralBoundaryInclusion C r hr)) 2 = 0 :=
  baseTorusProjection_boundary_homology_eq_zero C r hr hr1 hC hR 0

end Wikipedia.HopfProblem.CuspCentralHomology
