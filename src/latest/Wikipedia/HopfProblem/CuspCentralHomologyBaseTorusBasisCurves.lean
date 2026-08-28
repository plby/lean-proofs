import Wikipedia.HopfProblem.CuspCentralHomologyDoubleLocusHomology
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseTarget

/-!
# The three geometric degree-two classes of the actual double locus

Each circle summand of the literal three-circle suspension gives an actual
map from the suspension of one circle.  Naturality of the proved singular
Mayer--Vietoris connecting map identifies its degree-two class with the
corresponding coordinate in the existing double-locus homology marking.
The orientation is induced by the northern/southern cover and the existing
unit-circle orientation; no class of the double locus is chosen by inverting
its three-dimensional coordinate marking.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspCollapse
open SingularMayerVietoris PeriodTorusHigherHomology

private def suspensionCircleFun (j : Fin 3) : Suspension Circle → ThreeCircleSuspension :=
  Quotient.lift (s := suspensionSetoid Circle)
    (fun p => Suspension.mk p.1 (thetaCircleInclusion j p.2))
    (fun a b hab => by
      apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
      rcases hab with ⟨ht, hzero | hone | hz⟩
      · exact ⟨ht, Or.inl hzero⟩
      · exact ⟨ht, Or.inr (Or.inl hone)⟩
      · exact ⟨ht, Or.inr (Or.inr (congrArg (thetaCircleInclusion j) hz))⟩)

private theorem suspensionCircleFun_continuous (j : Fin 3) :
    Continuous (suspensionCircleFun j) := by
  apply (Suspension.isQuotientMap_mk (X := Circle)).continuous_iff.mpr
  change Continuous (fun p : unitInterval × Circle =>
    Suspension.mk p.1 (thetaCircleInclusion j p.2))
  exact Suspension.continuous_mk.comp
    (continuous_fst.prodMk ((thetaCircleMap j).continuous.comp continuous_snd))

/-- The actual suspension of the inclusion of the indicated circle summand. -/
def suspensionCircleMap (j : Fin 3) : C(Suspension Circle, ThreeCircleSuspension) :=
  ⟨suspensionCircleFun j, suspensionCircleFun_continuous j⟩

@[simp] theorem suspensionCircleMap_mk (j : Fin 3) (t : unitInterval) (z : Circle) :
    suspensionCircleMap j (Suspension.mk t z) =
      Suspension.mk t (thetaCircleInclusion j z) := rfl

@[simp] theorem suspensionCircleMap_height (j : Fin 3) (q : Suspension Circle) :
    Suspension.height (suspensionCircleMap j q) = Suspension.height q := by
  obtain ⟨⟨t, z⟩, rfl⟩ := Suspension.mk_surjective q
  rfl

/-- Each component suspension is included without any further identifications. -/
theorem suspensionCircleMap_injective (j : Fin 3) :
    Function.Injective (suspensionCircleMap j) := by
  have hj : Function.Injective (thetaCircleInclusion j) := by
    fin_cases j <;> intro z w h <;> simpa using h
  intro p q hpq
  obtain ⟨⟨s, z⟩, rfl⟩ := Suspension.mk_surjective p
  obtain ⟨⟨t, w⟩, rfl⟩ := Suspension.mk_surjective q
  rw [suspensionCircleMap_mk, suspensionCircleMap_mk,
    Suspension.mk_eq_mk_iff] at hpq
  apply (Suspension.mk_eq_mk_iff _ _ _ _).mpr
  rcases hpq with ⟨hst, hs | hs | hzw⟩
  · exact ⟨hst, Or.inl hs⟩
  · exact ⟨hst, Or.inr (Or.inl hs)⟩
  · exact ⟨hst, Or.inr (Or.inr (hj hzw))⟩

theorem suspensionCircleMap_mapsTo_northOpen (j : Fin 3) :
    MapsTo (suspensionCircleMap j) Suspension.northOpen Suspension.northOpen := by
  intro q hq
  simpa only [Suspension.mem_northOpen, suspensionCircleMap_height] using hq

theorem suspensionCircleMap_mapsTo_southOpen (j : Fin 3) :
    MapsTo (suspensionCircleMap j) Suspension.southOpen Suspension.southOpen := by
  intro q hq
  simpa only [Suspension.mem_southOpen, suspensionCircleMap_height] using hq

/-- The restriction of the actual circle-suspension inclusion to the open belt. -/
def suspensionCircleBeltMap (j : Fin 3) :
    C(Suspension.middleBand Circle, Suspension.middleBand ThreeCircles) :=
  intersectionRestriction (suspensionCircleMap j)
    Suspension.northOpen Suspension.southOpen Suspension.northOpen Suspension.southOpen
    (suspensionCircleMap_mapsTo_northOpen j) (suspensionCircleMap_mapsTo_southOpen j)

/-- Dropping the belt height commutes with the literal circle inclusion. -/
theorem suspensionCircleBeltMap_label (j : Fin 3) :
    (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun.comp
        (suspensionCircleBeltMap j) =
      (thetaCircleMap j).comp (Suspension.middleBandHomotopyEquiv (X := Circle)).toFun := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨⟨t, z⟩, rfl⟩ :=
    (Suspension.middleBandHomeomorph (X := Circle)).symm.surjective p
  have h : suspensionCircleBeltMap j (Suspension.middleBandHomeomorph.symm (t, z)) =
      Suspension.middleBandHomeomorph.symm (t, thetaCircleInclusion j z) := by
    apply Subtype.ext
    rfl
  change Suspension.middleBandHomotopyEquiv (suspensionCircleBeltMap j _) =
    thetaCircleMap j (Suspension.middleBandHomotopyEquiv _)
  rw [h]
  simp only [Suspension.middleBandHomotopyEquiv_apply, Homeomorph.apply_symm_apply,
    thetaCircleMap_apply]

/-- Integral orientation of the actual one-circle suspension, through its
actual connecting map and the already fixed unit-circle orientation. -/
def suspensionCircleHomologyTwoEquiv :
    SingularHomology (Suspension Circle) 2 ≃ₗ[ℤ] ℤ :=
  (contractibleCoverHomologyHigherEquiv
    (Suspension.northOpen : Set (Suspension Circle)) Suspension.southOpen
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover 0).trans
      ((homotopyEquivHomologyEquiv
        (Suspension.middleBandHomotopyEquiv (X := Circle)) 1).trans
          unitCircleHomologyOneEquiv)

/-- The actual connecting-map square fixes each suspended component's
coordinate and its integral sign. -/
theorem suspensionCircleMap_homologyTwo (j : Fin 3)
    (a : SingularHomology (Suspension Circle) 2) :
    threeCircleSuspensionHomologyTwoEquiv
        (singularHomologyMap (suspensionCircleMap j) 2 a) =
      Pi.single j (suspensionCircleHomologyTwoEquiv a) := by
  have hn := connectingHomomorphism_naturality_apply (suspensionCircleMap j)
    Suspension.northOpen Suspension.southOpen Suspension.northOpen Suspension.southOpen
    (suspensionCircleMap_mapsTo_northOpen j) (suspensionCircleMap_mapsTo_southOpen j)
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
    Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover 1 a
  change singularHomologyMap (suspensionCircleBeltMap j) 1
      (connectingHomomorphism _ _ _ _ _ 1 a) = _ at hn
  change threeCirclesHomologyOneEquiv
    (singularHomologyMap (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun 1
      (connectingHomomorphism _ _ _ _ _ 1
        (singularHomologyMap (suspensionCircleMap j) 2 a))) = _
  rw [← hn]
  change threeCirclesHomologyOneEquiv
    (((singularHomologyMap (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun
      1).comp (singularHomologyMap (suspensionCircleBeltMap j) 1)) _) = _
  rw [← singularHomologyMap_comp, suspensionCircleBeltMap_label,
    singularHomologyMap_comp, LinearMap.comp_apply, thetaCircleMap_homologyOne]
  rfl

/-- The integral generator of the actual suspended circle with this orientation. -/
def suspensionCircleFundamentalClass : SingularHomology (Suspension Circle) 2 :=
  suspensionCircleHomologyTwoEquiv.symm 1

@[simp] theorem suspensionCircleFundamentalClass_coordinate :
    suspensionCircleHomologyTwoEquiv suspensionCircleFundamentalClass = 1 :=
  suspensionCircleHomologyTwoEquiv.apply_symm_apply 1

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The genuine component map into the actual central double locus. -/
def centralDoubleCurveSphereMap (j : Fin 3) :
    C(Suspension Circle, centralBoundary C ε hε) :=
  ((centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm :
    C(ThreeCircleSuspension, centralBoundary C ε hε)).comp (suspensionCircleMap j)

/-- On the original cylinder this is exactly the actual edge-cylinder map. -/
@[simp] theorem centralDoubleCurveSphereMap_mk_coe (j : Fin 3) (t : unitInterval)
    (z : Circle) :
    (centralDoubleCurveSphereMap C ε hε hε1 hC hR j (Suspension.mk t z) :
      QuotientCentralFibre C ε) = doubleCylinder C ε hε (t, thetaCircleInclusion j z) := rfl

theorem centralDoubleCurveSphereMap_injective (j : Fin 3) :
    Function.Injective (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) :=
  (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.injective.comp
    (suspensionCircleMap_injective j)

/-- The actual component parameterization is a closed embedding. -/
theorem centralDoubleCurveSphereMap_isClosedEmbedding (j : Fin 3) :
    IsClosedEmbedding (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact (centralDoubleCurveSphereMap C ε hε hε1 hC hR j).continuous.isClosedEmbedding
    (centralDoubleCurveSphereMap_injective C ε hε hε1 hC hR j)

/-- Actual component homology, transported along the proved geometric homeomorphism. -/
theorem centralDoubleCurveSphereMap_homologyTwo (j : Fin 3)
    (a : SingularHomology (Suspension Circle) 2) :
    centralBoundaryHomologyTwoEquiv C ε hε hε1 hC hR
        (singularHomologyMap (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) 2 a) =
      Pi.single j (suspensionCircleHomologyTwoEquiv a) := by
  have hc : (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR :
      C(centralBoundary C ε hε, ThreeCircleSuspension)).comp
        (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) = suspensionCircleMap j := by
    apply ContinuousMap.ext
    intro q
    exact (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).apply_symm_apply _
  change threeCircleSuspensionHomologyTwoEquiv
    (((singularHomologyMap (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR :
      C(centralBoundary C ε hε, ThreeCircleSuspension)) 2).comp
        (singularHomologyMap (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) 2)) a) = _
  rw [← singularHomologyMap_comp, hc]
  exact suspensionCircleMap_homologyTwo j a

/-- The three degree-two classes are images of the oriented fundamental
class under the three actual component parameterizations. -/
def centralDoubleCurveFundamentalClass (j : Fin 3) :
    SingularHomology (centralBoundary C ε hε) 2 :=
  singularHomologyMap (centralDoubleCurveSphereMap C ε hε hε1 hC hR j) 2
    suspensionCircleFundamentalClass

@[simp] theorem centralDoubleCurveFundamentalClass_coordinate (j : Fin 3) :
    centralBoundaryHomologyTwoEquiv C ε hε hε1 hC hR
        (centralDoubleCurveFundamentalClass C ε hε hε1 hC hR j) = Pi.single j 1 := by
  rw [centralDoubleCurveFundamentalClass, centralDoubleCurveSphereMap_homologyTwo,
    suspensionCircleFundamentalClass_coordinate]

end Wikipedia.HopfProblem.CuspCentralHomology
