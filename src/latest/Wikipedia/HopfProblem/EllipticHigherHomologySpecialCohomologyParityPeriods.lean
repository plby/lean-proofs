import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomologyParityCoordinates
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryThirdRelationShearCoordinates
import Wikipedia.HopfProblem.PeriodTorusCohomologyCup

/-!
# The literal Appendix A basis in actual invariant cohomology

The classes `gammaEtaClass` and `etaClass` are the actual native cups
`γ ∪ ηⱼ` and `u ∪ w + 6 γ ∪ δ`.  Their invariant coordinates are computed
by evaluation on the original positive period pairs.  This keeps both
the order-four negative twist and the original covering markings.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyParity

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior
open PeriodTorusHigherHomologyPontryagin PeriodTorusTypeOneOne
open PeriodTorusCohomology PeriodTorusCohomologyCup SingularCohomologyCup
open SpecialPeriods
open TrianglePeriodFamily TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open TrianglePeriodFamily.Boundary.ThirdRelation
open SpecialPeriods.Threefold.Homology.DeltaSweep

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual real-to-complex coordinate homeomorphism preserves the original exterior marking. -/
theorem periodH2Exterior_flat_image (p : PeriodDomain)
    (a : SingularHomology RealTorus₄ 2) :
    periodTorusH2ExteriorEquiv p
        (singularHomologyMap (flatTorusPeriodHomeomorph p : C(RealTorus₄, p.Torus)) 2 a) =
      FlatTorus.singularH2Equiv a := by
  rw [← coordinateTorusH2ExteriorEquiv_periodCoordinates]
  have hmap : (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)).comp
      (flatTorusPeriodHomeomorph p : C(RealTorus₄, p.Torus)) =
        (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) := by
    apply ContinuousMap.ext
    intro x
    change flatTorusCircleHomeomorph
      ((flatTorusPeriodHomeomorph p).symm (flatTorusPeriodHomeomorph p x)) =
        flatTorusCircleHomeomorph x
    rw [Homeomorph.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, hmap]
  rfl

/-- Evaluation on the native fibre class is the literal `uw` coefficient. -/
theorem coefficientClass_evaluate_splitFibre (j : Kind) (p : FixedPeriod j)
    (E : Fin 6 → ℤ) :
    singularEvaluation p.val.Torus 2 (coefficientClass p.val E)
        (periodSplitFibreClassTwo j p) = E 3 := by
  rw [coefficientClass_evaluate, periodSplitFibreClassTwo, periodH2Exterior_flat_image,
    splitFibreClassTwo_eq_product, flat_product11_exterior, integralExteriorForm_pairing]
  simp [coordinateForm_apply, coordinateValue]

/-- Circle first fixes the signs: the values are `twist₀ Eγw + twist₁ Euw`. -/
theorem coefficientClass_evaluate_splitCircle (j : Kind) (p : FixedPeriod j)
    (E : Fin 6 → ℤ) :
    singularEvaluation p.val.Torus 2 (coefficientClass p.val E)
        (periodSplitCircleClassTwo j p) = j.twist 0 * E 1 + j.twist 1 * E 3 := by
  rw [coefficientClass_evaluate, periodSplitCircleClassTwo, periodH2Exterior_flat_image,
    splitCircleClassTwo_eq_product, flat_product11_exterior, integralExteriorForm_pairing]
  cases j <;> simp [Kind.twist, ε, ε', coordinateForm_apply, coordinateValue] <;> ring

/-- The source coefficients of `γ ∧ ηⱼ`, in the original six-pair order. -/
def gammaEtaCoefficients : Kind → Fin 6 → ℤ
  | .three => ![2, 1, 3, 0, 0, 0]
  | .four => ![1, 1, 2, 0, 0, 0]

/-- The actual native class with the source's `γ ∧ ηⱼ` periods. -/
def gammaEtaClass (j : Kind) (p : PeriodDomain) : SingularCohomology p.Torus 2 :=
  coefficientClass p (gammaEtaCoefficients j)

/-- The source's `η₁ = 2u + w + 3δ` and `η₂ = u + w + 2δ` as native degree-one classes. -/
def ellipticEtaOneClass (j : Kind) (p : PeriodDomain) : SingularCohomology p.Torus 1 :=
  gammaEtaCoefficients j 0 • periodOneClass p 1 + periodOneClass p 2 +
    gammaEtaCoefficients j 2 • periodOneClass p 3

/-- The marked alternating class is the genuine native cup `γ ∪ ηⱼ`. -/
theorem gammaEtaClass_eq_cup (j : Kind) (p : PeriodDomain) :
    gammaEtaClass j p =
      cupProduct p.Torus 1 1 (periodOneClass p 0) (ellipticEtaOneClass j p) := by
  unfold ellipticEtaOneClass
  rw [map_add, map_add, map_zsmul, map_zsmul,
    periodOneCup_eq_coefficientClass, periodOneCup_eq_coefficientClass,
    periodOneCup_eq_coefficientClass, ← coefficientClass_smul, ← coefficientClass_smul,
    ← coefficientClass_add, ← coefficientClass_add]
  apply congrArg (coefficientClass p)
  cases j <;> decide

/-- Both source vectors are preserved by the original affine deck generator. -/
theorem gammaEtaCoefficients_preserved (j : Kind) :
    coefficientPullback j.matrix.mulVecLin (gammaEtaCoefficients j) = gammaEtaCoefficients j := by
  cases j with
  | three =>
    change coefficientPullback A₁.mulVecLin _ = _
    rw [coefficientPullback_A₁]
    decide
  | four =>
    change coefficientPullback A₂.mulVecLin _ = _
    rw [coefficientPullback_A₂]
    decide

/-- The actual source cup class belongs to all actual deck invariants. -/
def gammaEtaInvariantClass (j : Kind) (p : FixedPeriod j) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2 :=
  ⟨gammaEtaClass j p.val,
    (coefficientClass_mem_deckInvariants_iff j p j.twist (mainTwist_admissible j)
      (gammaEtaCoefficients j)).mpr (gammaEtaCoefficients_preserved j)⟩

@[simp] theorem gammaEtaInvariantClass_coe (j : Kind) (p : FixedPeriod j) :
    (gammaEtaInvariantClass j p : SingularCohomology p.val.Torus 2) =
      gammaEtaClass j p.val := rfl

/-- The source `γ ∧ ηⱼ` has zero fibre period and the signed unit circle-first period. -/
theorem gammaEtaInvariantClass_coordinates (j : Kind) (p : FixedPeriod j) :
    periodInvariantCohomologyH2Coordinates j p (gammaEtaInvariantClass j p) =
      ![0, j.twist 0] := by
  ext i
  fin_cases i
  · change periodInvariantCohomologyH2Coordinates j p (gammaEtaInvariantClass j p) 0 = 0
    rw [invariantH2Coordinates_first j p (gammaEtaInvariantClass j p)]
    change singularEvaluation p.val.Torus 2 (coefficientClass p.val (gammaEtaCoefficients j))
      (periodSplitFibreClassTwo j p) = _
    rw [coefficientClass_evaluate_splitFibre]
    cases j <;> rfl
  · change periodInvariantCohomologyH2Coordinates j p (gammaEtaInvariantClass j p) 1 = j.twist 0
    rw [invariantH2Coordinates_second j p (gammaEtaInvariantClass j p)]
    change singularEvaluation p.val.Torus 2 (coefficientClass p.val (gammaEtaCoefficients j))
      (periodSplitCircleClassTwo j p) = _
    rw [coefficientClass_evaluate_splitCircle]
    cases j <;> simp [gammaEtaCoefficients]

/-- The source `q = η` retains its positive `uw` period and its literal twist-circle period. -/
theorem etaInvariantClass_coordinates (j : Kind) (p : FixedPeriod j) :
    periodInvariantCohomologyH2Coordinates j p
        (etaInvariantClass j p j.twist (mainTwist_admissible j)) = ![1, j.twist 1] := by
  ext i
  fin_cases i
  · change periodInvariantCohomologyH2Coordinates j p
      (etaInvariantClass j p j.twist (mainTwist_admissible j)) 0 = 1
    rw [invariantH2Coordinates_first j p
      (etaInvariantClass j p j.twist (mainTwist_admissible j))]
    change singularEvaluation p.val.Torus 2 (coefficientClass p.val periodRelationEta)
      (periodSplitFibreClassTwo j p) = _
    rw [coefficientClass_evaluate_splitFibre]
    rfl
  · change periodInvariantCohomologyH2Coordinates j p
      (etaInvariantClass j p j.twist (mainTwist_admissible j)) 1 = j.twist 1
    rw [invariantH2Coordinates_second j p
      (etaInvariantClass j p j.twist (mainTwist_admissible j))]
    change singularEvaluation p.val.Torus 2 (coefficientClass p.val periodRelationEta)
      (periodSplitCircleClassTwo j p) = _
    rw [coefficientClass_evaluate_splitCircle]
    simp [periodRelationEta]

/-- The literal source combination as an element of the actual all-deck invariant submodule. -/
def sourceCombination (j : Kind) (p : FixedPeriod j) (a b : ℤ) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2 :=
  a • gammaEtaInvariantClass j p + b • etaInvariantClass j p j.twist (mainTwist_admissible j)

@[simp] theorem sourceCombination_coe (j : Kind) (p : FixedPeriod j) (a b : ℤ) :
    (sourceCombination j p a b : SingularCohomology p.val.Torus 2) =
      a • gammaEtaClass j p.val + b • etaClass p.val := rfl

/-- These coordinates follow from the actual ordered period evaluations, not from an index. -/
theorem sourceCombination_coordinates (j : Kind) (p : FixedPeriod j) (a b : ℤ) :
    periodInvariantCohomologyH2Coordinates j p (sourceCombination j p a b) =
      ![b, a * j.twist 0 + b * j.twist 1] := by
  rw [sourceCombination, map_add, map_zsmul, map_zsmul,
    gammaEtaInvariantClass_coordinates, etaInvariantClass_coordinates]
  ext i
  fin_cases i <;> simp

/-- In the order-four case the retained negative twist gives the literal pair `(b,-a-3b)`. -/
theorem sourceCombination_four_coordinates (p : FixedPeriod .four) (a b : ℤ) :
    periodInvariantCohomologyH2Coordinates .four p (sourceCombination .four p a b) =
      ![b, -a - 3 * b] := by
  rw [sourceCombination_coordinates]
  ext i
  fin_cases i
  · rfl
  · simp [Kind.twist, ε']
    ring

/-- The two native source classes span all genuine deck-invariant second cohomology. -/
theorem sourceCombination_surjective (j : Kind) (p : FixedPeriod j)
    (c : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) 2) :
    ∃ a b : ℤ, sourceCombination j p a b = c := by
  let v := periodInvariantCohomologyH2Coordinates j p c
  refine ⟨j.twist 0 * (v 1 - v 0 * j.twist 1), v 0, ?_⟩
  apply (periodInvariantCohomologyH2Coordinates j p).injective
  rw [sourceCombination_coordinates]
  change ![v 0, j.twist 0 * (v 1 - v 0 * j.twist 1) * j.twist 0 + v 0 * j.twist 1] = v
  cases j <;> ext i <;> fin_cases i <;> simp [Kind.twist, ε, ε']

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyParity
