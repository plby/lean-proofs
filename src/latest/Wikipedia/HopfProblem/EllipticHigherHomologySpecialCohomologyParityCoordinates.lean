import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomologyInvariantIndices
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSource
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWangSplitTwo

/-!
# Original period-pair coordinates for the elliptic invariant cohomology

The two deck-coinvariant coordinates are represented by the actual split
fibre class and the positive split circle crossed with the original `w`
loop.  This identifies the existing invariant-cohomology coordinates with
evaluation on those genuine cycles, and identifies the existing dual
covering shear with the original surface-cover shear without changing a
Wang splitting or a homology marking.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyParity

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang

/-- The actual positive split fibre two-cycle in the original complex period torus. -/
def periodSplitFibreClassTwo (j : Kind) (p : FixedPeriod j) :
    SingularHomology p.val.Torus 2 :=
  singularHomologyMap (flatTorusPeriodHomeomorph p.val : C(_, _)) 2
    (splitFibreClassTwo j)

/-- The actual positive twist-circle crossed with `w`, in the original period torus. -/
def periodSplitCircleClassTwo (j : Kind) (p : FixedPeriod j) :
    SingularHomology p.val.Torus 2 :=
  singularHomologyMap (flatTorusPeriodHomeomorph p.val : C(_, _)) 2
    (splitCircleClassTwo j)

/-- The original real and complex splittings commute on every native homology class. -/
theorem periodCircleHomologyEquiv_flat_split (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology (CircleTopology.Circle × ProductTorus 3) (n + 1)) :
    periodCircleHomologyEquiv j p n
        (singularHomologyMap
          (flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)) (n + 1)
          (singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
            C(CircleTopology.Circle × ProductTorus 3, RealTorus₄)) (n + 1) a)) =
      circleProductHomologyEquiv (ProductTorus 3) n a := by
  have hmap : (splitPeriodTorusHomeomorph j p.val :
      C(p.val.Torus, CircleTopology.Circle × ProductTorus 3)).comp
      ((flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)).comp
        ((splitFlatTorusHomeomorph j).symm :
          C(CircleTopology.Circle × ProductTorus 3, RealTorus₄))) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro x
    change splitFlatTorusHomeomorph j
      ((flatTorusPeriodHomeomorph p.val).symm
        (flatTorusPeriodHomeomorph p.val ((splitFlatTorusHomeomorph j).symm x))) = x
    rw [Homeomorph.symm_apply_apply, Homeomorph.apply_symm_apply]
  change circleProductHomologyEquiv (ProductTorus 3) n
    (singularHomologyMap (splitPeriodTorusHomeomorph j p.val :
      C(p.val.Torus, CircleTopology.Circle × ProductTorus 3)) (n + 1)
      (singularHomologyMap
        (flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)) (n + 1)
        (singularHomologyMap ((splitFlatTorusHomeomorph j).symm :
          C(CircleTopology.Circle × ProductTorus 3, RealTorus₄)) (n + 1) a))) = _
  congr 1
  have h := congrArg (fun f => singularHomologyMap f (n + 1)) hmap
  simp only [singularHomologyMap_comp, singularHomologyMap_id] at h
  exact LinearMap.congr_fun h a

/-- The genuine fibre class is the first, unmodified deck-coinvariant basis vector. -/
theorem periodDeckCoinvariantsH2Equiv_splitFibre (j : Kind) (p : FixedPeriod j) :
    periodDeckCoinvariantsH2Equiv j p
        (Submodule.Quotient.mk (periodSplitFibreClassTwo j p)) = ![1, 0] := by
  rw [periodDeckCoinvariantsH2Equiv_mk, periodSplitFibreClassTwo,
    splitFibreClassTwo, periodCircleHomologyEquiv_flat_split,
    circleProductHomologyEquiv_section]
  simp [splitFibreInputTwo]

/-- The genuine circle-first class is the second, unmodified coinvariant basis vector. -/
theorem periodDeckCoinvariantsH2Equiv_splitCircle (j : Kind) (p : FixedPeriod j) :
    periodDeckCoinvariantsH2Equiv j p
        (Submodule.Quotient.mk (periodSplitCircleClassTwo j p)) = ![0, 1] := by
  rw [periodDeckCoinvariantsH2Equiv_mk, periodSplitCircleClassTwo,
    splitCircleClassTwo, periodCircleHomologyEquiv_flat_split,
    circleProductHomologyEquiv_positiveCircleCross]
  simp [splitFibreInputOne]

theorem periodDeckCoinvariantsH2Equiv_symm_first (j : Kind) (p : FixedPeriod j) :
    (periodDeckCoinvariantsH2Equiv j p).symm (Pi.single 0 1) =
      Submodule.Quotient.mk (periodSplitFibreClassTwo j p) := by
  apply (periodDeckCoinvariantsH2Equiv j p).injective
  rw [LinearEquiv.apply_symm_apply, periodDeckCoinvariantsH2Equiv_splitFibre]
  decide

theorem periodDeckCoinvariantsH2Equiv_symm_second (j : Kind) (p : FixedPeriod j) :
    (periodDeckCoinvariantsH2Equiv j p).symm (Pi.single 1 1) =
      Submodule.Quotient.mk (periodSplitCircleClassTwo j p) := by
  apply (periodDeckCoinvariantsH2Equiv j p).injective
  rw [LinearEquiv.apply_symm_apply, periodDeckCoinvariantsH2Equiv_splitCircle]
  decide

/-- The first invariant coordinate is evaluation on the actual positive fibre pair. -/
theorem invariantH2Coordinates_first (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2) :
    periodInvariantCohomologyH2Coordinates j p a 0 =
      singularEvaluation p.val.Torus 2 a (periodSplitFibreClassTwo j p) := by
  rw [periodInvariantCohomologyH2Coordinates, LinearEquiv.trans_apply,
    intDualCoordinatesOfEquiv_apply, periodDeckCoinvariantsH2Equiv_symm_first,
    periodCohomologyInvariantsEquivDualCoinvariants_apply_mk]

/-- The second invariant coordinate is evaluation on the actual positive circle-first pair. -/
theorem invariantH2Coordinates_second (j : Kind) (p : FixedPeriod j)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2) :
    periodInvariantCohomologyH2Coordinates j p a 1 =
      singularEvaluation p.val.Torus 2 a (periodSplitCircleClassTwo j p) := by
  rw [periodInvariantCohomologyH2Coordinates, LinearEquiv.trans_apply,
    intDualCoordinatesOfEquiv_apply, periodDeckCoinvariantsH2Equiv_symm_second,
    periodCohomologyInvariantsEquivDualCoinvariants_apply_mk]

/-- The two independently retained shears refer to the very same original covering column. -/
theorem special_cover_shear_eq_sourceShearTwo (j : Kind) :
    periodCoverDeckDualH2Shear j (specialLocalData j).centralPeriod = sourceShearTwo j := by
  have haxis : (![0, 1] : Fin 2 → ℤ) = Pi.single 1 1 := by decide
  unfold periodCoverDeckDualH2Shear periodCoverCoinvariantH2Map
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, haxis,
    periodDeckCoinvariantsH2Equiv_symm_second, periodCoverFromDeckCoinvariants_mk,
    periodSplitCircleClassTwo]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← surfaceCover_eq_periodCover]
  rfl

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyParity
