import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisCurveRanges

/-!
# Homeomorphisms and fundamental classes of the named double curves

The component-suspension parameterizations are homeomorphisms onto the
literal named double curves in the original cusp quotient.  In particular,
the three classes used in the geometric degree-two basis are images of
oriented generators of the actual curves' own integral singular homology.
The orientation convention remains the two-cone connecting orientation
and the previously fixed unit-circle orientation.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The literal inclusion of a named double curve into the central double locus. -/
def centralDoubleCurveIntoBoundary (j : Fin 3) :
    C(CuspQuotient.doubleCurve C ε hε j, centralBoundary C ε hε) where
  toFun q := ⟨⟨q.1, CuspQuotient.doubleCurve_subset_central C ε hε j q.2⟩,
    (mem_centralBoundary_iff_branchCount C ε hε _).mpr
      (CuspQuotient.branchCount_ge_two_of_mem_doubleCurve C ε hε j q.2)⟩
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem centralDoubleCurveIntoBoundary_coe (j : Fin 3)
    (q : CuspQuotient.doubleCurve C ε hε j) :
    (centralDoubleCurveIntoBoundary C ε hε j q).1.1 = q.1 := rfl

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- Restrict the genuine component sphere map to its named geometric image. -/
def centralDoubleCurveSphereToCurve (j : Fin 3) :
    C(Suspension Circle, CuspQuotient.doubleCurve C ε hε j) where
  toFun p := ⟨(centralDoubleCurveSphereMap C ε hε hε1 hC hR j p).1.1,
    centralDoubleCurveSphereMap_mem_doubleCurve C ε hε hε1 hC hR j p⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp
        (centralDoubleCurveSphereMap C ε hε hε1 hC hR j).continuous)).subtype_mk _

theorem centralDoubleCurveSphereToCurve_bijective (j : Fin 3) :
    Function.Bijective (centralDoubleCurveSphereToCurve C ε hε hε1 hC hR j) := by
  constructor
  · intro p q hpq
    apply centralDoubleCurveSphereMap_injective C ε hε hε1 hC hR j
    have h : (centralDoubleCurveSphereMap C ε hε hε1 hC hR j p).1.1 =
        (centralDoubleCurveSphereMap C ε hε hε1 hC hR j q).1.1 :=
      congrArg (fun x : CuspQuotient.doubleCurve C ε hε j => x.1) hpq
    exact Subtype.ext (Subtype.ext h)
  · rintro ⟨q, hq⟩
    rw [← range_centralDoubleCurveSphereMap_quotient C ε hε hε1 hC hR j] at hq
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩

/-- The actual component sphere is homeomorphic to the same-index named double curve. -/
def centralDoubleCurveHomeomorph (j : Fin 3) :
    Suspension Circle ≃ₜ CuspQuotient.doubleCurve C ε hε j := by
  letI := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact (Equiv.ofBijective (centralDoubleCurveSphereToCurve C ε hε hε1 hC hR j)
    (centralDoubleCurveSphereToCurve_bijective C ε hε hε1 hC hR j)).toHomeomorphOfContinuousClosed
      (centralDoubleCurveSphereToCurve C ε hε hε1 hC hR j).continuous
      (centralDoubleCurveSphereToCurve C ε hε hε1 hC hR j).continuous.isClosedMap

@[simp] theorem centralDoubleCurveHomeomorph_coe (j : Fin 3) (p : Suspension Circle) :
    (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j p : CuspQuotient.QuotientSpace C ε) =
      (centralDoubleCurveSphereMap C ε hε hε1 hC hR j p).1.1 := rfl

/-- The homeomorphism is the original quotient of the chosen edge cylinder. -/
@[simp] theorem centralDoubleCurveHomeomorph_mk_coe (j : Fin 3)
    (t : unitInterval) (z : Circle) :
    (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j (Suspension.mk t z) :
      CuspQuotient.QuotientSpace C ε) =
        (doubleCylinder C ε hε (t, thetaCircleInclusion j z)).1 := rfl

/-- Inclusion of the named curve recovers the actual sphere map into the double locus. -/
theorem centralDoubleCurveIntoBoundary_comp_homeomorph (j : Fin 3) :
    (centralDoubleCurveIntoBoundary C ε hε j).comp
        (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j :
          C(Suspension Circle, CuspQuotient.doubleCurve C ε hε j)) =
      centralDoubleCurveSphereMap C ε hε hε1 hC hR j := by
  apply ContinuousMap.ext
  intro p
  rfl

/-- The actual named curve's second integral singular homology, with the
orientation induced by its constructed suspension homeomorphism. -/
def centralDoubleCurveHomologyTwoEquiv (j : Fin 3) :
    SingularHomology (CuspQuotient.doubleCurve C ε hε j) 2 ≃ₗ[ℤ] ℤ :=
  (homeomorphHomologyEquiv (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j).symm 2).trans
    suspensionCircleHomologyTwoEquiv

/-- An oriented fundamental class in the actual named curve, before its inclusion into `D`. -/
def centralDoubleCurveOrientedFundamentalClass (j : Fin 3) :
    SingularHomology (CuspQuotient.doubleCurve C ε hε j) 2 :=
  singularHomologyMap (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j :
    C(Suspension Circle, CuspQuotient.doubleCurve C ε hε j)) 2
      suspensionCircleFundamentalClass

/-- The oriented class generates the actual curve's rank-one second homology. -/
@[simp] theorem centralDoubleCurveOrientedFundamentalClass_coordinate (j : Fin 3) :
    centralDoubleCurveHomologyTwoEquiv C ε hε hε1 hC hR j
        (centralDoubleCurveOrientedFundamentalClass C ε hε hε1 hC hR j) = 1 := by
  change suspensionCircleHomologyTwoEquiv
    (homeomorphHomologyEquiv (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j).symm 2
      (homeomorphHomologyEquiv (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j) 2
        suspensionCircleFundamentalClass)) = 1
  rw [← homeomorphHomologyEquiv_symm, LinearEquiv.symm_apply_apply,
    suspensionCircleFundamentalClass_coordinate]

/-- The component class in the double locus is induced by its literal inclusion. -/
@[simp] theorem centralDoubleCurveOrientedFundamentalClass_inclusion (j : Fin 3) :
    singularHomologyMap (centralDoubleCurveIntoBoundary C ε hε j) 2
        (centralDoubleCurveOrientedFundamentalClass C ε hε hε1 hC hR j) =
      centralDoubleCurveFundamentalClass C ε hε hε1 hC hR j := by
  change ((singularHomologyMap (centralDoubleCurveIntoBoundary C ε hε j) 2).comp
    (singularHomologyMap (centralDoubleCurveHomeomorph C ε hε hε1 hC hR j :
      C(Suspension Circle, CuspQuotient.doubleCurve C ε hε j)) 2))
        suspensionCircleFundamentalClass = _
  rw [← singularHomologyMap_comp, centralDoubleCurveIntoBoundary_comp_homeomorph]
  rfl

end Wikipedia.HopfProblem.CuspCentralHomology
