import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularManifold
import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Wikipedia.HopfProblem.SpecialPeriodsTriangleDiscrete

/-!
# The actual regular triangle domain and its analytic quotient

The faithful free-product action on the upper half-plane is properly
discontinuous: lift each group element to the proved-discrete generated matrix
subgroup, then use finiteness of its compact transporters.  This discharges the
proper-discontinuity input in the general free-locus construction.

The regular domain is the open subset of the actual upper half-plane on which
no nonidentity triangle element fixes a point.  Its orbit quotient is a
Hausdorff, second-countable complex curve, and the actual projection is a
holomorphic quotient covering.  No identification of the whole orbifold
quotient with an affine line is assumed or asserted here.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold Pointwise

namespace Wikipedia.HopfProblem.SpecialPeriods

attribute [local instance] triangleGeometricAction

/-- Choose a representative in the actual generated matrix subgroup.  This
choice is used only to compare finite sets of compact transporters. -/
def triangleMatrixLift (g : TriangleGroup) : Triangle.matrixGroup :=
  (Triangle.triangleGeometricRepresentation_matrixGroup_lift g).choose

theorem triangleMatrixLift_spec (g : TriangleGroup) :
    Triangle.realSLPermutation (triangleMatrixLift g) = triangleGeometricRepresentation g :=
  (Triangle.triangleGeometricRepresentation_matrixGroup_lift g).choose_spec

theorem triangleMatrixLift_injective : Function.Injective triangleMatrixLift := by
  intro g h hgh
  apply triangleGeometricRepresentation_injective
  rw [← triangleMatrixLift_spec, ← triangleMatrixLift_spec, hgh]

theorem triangleMatrixLift_smul (g : TriangleGroup) (z : ℍ) :
    triangleMatrixLift g • z = g • z := by
  exact congrArg (fun f : Equiv.Perm ℍ => f z) (triangleMatrixLift_spec g)

/-- Proper discontinuity for the actual abstract triangle group, with its
genuine Möbius action, follows from the discrete matrix subgroup. -/
theorem triangleGeometricAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul TriangleGroup ℍ where
  finite_disjoint_inter_image {K L} hK hL := by
    have hf := Triangle.matrixGroup_finite_compact_transporter hK hL
    apply (hf.preimage triangleMatrixLift_injective.injOn).subset
    rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
    exact ⟨y, ⟨x, hx, (triangleMatrixLift_smul g x).trans hxy⟩, hy⟩

theorem triangleGeometricAction_continuous : ContinuousConstSMul TriangleGroup ℍ where
  continuous_const_smul g := (triangleGeometricRepresentation_holomorphic g).continuous

attribute [local instance] triangleGeometricAction_properlyDiscontinuous
  triangleGeometricAction_continuous

/-- A fixed point of an abstract triangle element forces that element to
have finite order; finite stabilizers have been proved from properness. -/
theorem triangle_isOfFinOrder_of_fixed (g : TriangleGroup) (z : ℍ)
    (hg : triangleGeometricRepresentation g z = z) : IsOfFinOrder g :=
  FreeActionLocus.isOfFinOrder_of_smul_eq TriangleGroup ℍ g z hg

/-- The regular set in the original upper half-plane. -/
def triangleRegularLocus : Set ℍ := FreeActionLocus.locus TriangleGroup ℍ

theorem mem_triangleRegularLocus_iff (z : ℍ) :
    z ∈ triangleRegularLocus ↔ ∀ g : TriangleGroup,
      triangleGeometricRepresentation g z = z → g = 1 := Iff.rfl

theorem triangleRegularLocus_isOpen : IsOpen triangleRegularLocus :=
  FreeActionLocus.isOpen_locus TriangleGroup ℍ

theorem triangleRegularLocus_invariant (g : TriangleGroup) (z : ℍ) :
    triangleGeometricRepresentation g z ∈ triangleRegularLocus ↔
      z ∈ triangleRegularLocus :=
  FreeActionLocus.smul_mem_locus_iff TriangleGroup ℍ g z

/-- The regular domain as an actual open subset, with its inherited charts. -/
def triangleRegularDomain : TopologicalSpace.Opens ℍ :=
  FreeActionLocus.opens TriangleGroup ℍ

abbrev TriangleRegularPoint := triangleRegularDomain

instance triangleRegularPoint_locallyCompact : LocallyCompactSpace TriangleRegularPoint :=
  triangleRegularDomain.isOpen.locallyCompactSpace

instance triangleRegularAction : MulAction TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.mulAction TriangleGroup ℍ

@[simp] theorem triangleRegularAction_val (g : TriangleGroup) (z : TriangleRegularPoint) :
    (g • z).val = triangleGeometricRepresentation g z.val := rfl

instance triangleRegularAction_free : IsCancelSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.isCancelSMul TriangleGroup ℍ

instance triangleRegularAction_continuous :
    ContinuousConstSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.continuousConstSMul TriangleGroup ℍ

instance triangleRegularAction_properlyDiscontinuous :
    ProperlyDiscontinuousSMul TriangleGroup TriangleRegularPoint :=
  FreeActionLocus.properlyDiscontinuousSMul TriangleGroup ℍ

/-- The whole restricted action is holomorphic, not only its two generators. -/
theorem triangleRegularAction_holomorphic (g : TriangleGroup) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : TriangleRegularPoint => g • z) :=
  FreeActionLocus.smul_contMDiff TriangleGroup ℍ ℂ ω
    triangleGeometricRepresentation_holomorphic g

/-- The actual quotient of regular points by the triangle action. -/
abbrev TriangleRegularQuotient :=
  Quotient (MulAction.orbitRel TriangleGroup TriangleRegularPoint)

def triangleRegularProject : TriangleRegularPoint → TriangleRegularQuotient := Quotient.mk _

theorem triangleRegularProject_surjective : Function.Surjective triangleRegularProject :=
  Quotient.mk_surjective

theorem triangleRegularProject_covering :
    IsQuotientCoveringMap triangleRegularProject TriangleGroup :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

instance triangleRegularQuotient_t2 : T2Space TriangleRegularQuotient := inferInstance

instance triangleRegularQuotient_secondCountable :
    SecondCountableTopology TriangleRegularQuotient :=
  ContinuousConstSMul.secondCountableTopology

/-- The complex atlas made from local lifts of the actual orbit projection. -/
@[instance_reducible] def triangleRegularQuotientChartedSpace :
    ChartedSpace ℂ TriangleRegularQuotient :=
  CoveringQuotient.chartedSpace (E := ℂ) triangleRegularProject_covering

theorem triangleRegularQuotient_isManifold :
    letI := triangleRegularQuotientChartedSpace
    IsManifold 𝓘(ℂ) ω TriangleRegularQuotient :=
  CoveringQuotient.isManifold triangleRegularProject_covering ω triangleRegularAction_holomorphic

theorem triangleRegularProject_isLocalDiffeomorph :
    letI := triangleRegularQuotientChartedSpace
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularProject :=
  CoveringQuotient.project_isLocalDiffeomorph triangleRegularProject_covering
    triangleRegularAction_holomorphic

theorem triangleRegularProject_holomorphic :
    letI := triangleRegularQuotientChartedSpace
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω triangleRegularProject := by
  let := triangleRegularQuotientChartedSpace
  exact triangleRegularProject_isLocalDiffeomorph.contMDiff

end Wikipedia.HopfProblem.SpecialPeriods
