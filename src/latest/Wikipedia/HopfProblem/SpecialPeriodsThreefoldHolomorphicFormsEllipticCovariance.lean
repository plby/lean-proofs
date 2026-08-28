import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticGlobal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsGroupTriangular
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsWeights
import Mathlib.Topology.Instances.Matrix

/-!
# Genuine covariance on the whole upper half-plane

The constructed global coefficient functions agree with the actual
regular-cover coefficients on the proved dense regular locus. Both sides
of each covariance equation are continuous in the original upper-half-plane
atlas. The genuine regular-cover laws therefore persist at every elliptic
orbit point, without a covariance or extension assumption.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension

open Elliptic HolomorphicDifferentialForms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "I₁" => modelWithCornersSelf ℂ ℂ

private theorem continuous_eq_of_regular {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {f h : ℍ → Y} (hf : Continuous f) (hh : Continuous h)
    (heq : ∀ z : TriangleRegularPoint, f z.val = h z.val) : f = h :=
  Continuous.ext_on triangleRegularLocus_dense hf hh fun z hz => heq ⟨z, hz⟩

private theorem rightBlock_continuous (g : TriangleGroup) :
    Continuous (RegularCover.groupRightBlockExtension g) :=
  continuous_matrix fun i k =>
    (RegularCover.groupRightBlockExtension_entry_holomorphic g i k).continuous

/-- The actual global vertical coefficient obeys the original row-covector law everywhere. -/
theorem fibreOne_covariance (θ : Form FamilyModel Threefold.Space 1)
    (g : TriangleGroup) (z : ℍ) :
    fibreOne θ (triangleGeometricRepresentation g z) ᵥ*
      RegularCover.groupRightBlockExtension g z = fibreOne θ z := by
  have hC := (fibreOne_holomorphic θ).continuous
  have hleft := (hC.comp (triangleGeometricRepresentation_holomorphic g).continuous).matrix_vecMul
    (rightBlock_continuous g)
  have heq := continuous_eq_of_regular hleft hC (fun w => by
    simpa only [Function.comp_apply, ← triangleRegularAction_val, fibreOne_restrict,
      RegularCover.groupRightBlockExtension_restrict] using
      RegularCover.fibreOne_group_covariance θ g w)
  exact congrFun heq z

/-- The actual mixed coefficient law persists across both entire elliptic orbits. -/
theorem mixedTwo_covariance (θ : Form FamilyModel Threefold.Space 2)
    (g : TriangleGroup) (z : ℍ) :
    RegularCover.groupBaseDerivativeExtension g z •
      (mixedTwo θ (triangleGeometricRepresentation g z) ᵥ*
        RegularCover.groupRightBlockExtension g z) = mixedTwo θ z := by
  have hB := (mixedTwo_holomorphic θ).continuous
  have hrow := (hB.comp (triangleGeometricRepresentation_holomorphic g).continuous).matrix_vecMul
    (rightBlock_continuous g)
  have hleft := (RegularCover.groupBaseDerivativeExtension_holomorphic g).continuous.smul hrow
  have heq := continuous_eq_of_regular hleft hB (fun w => by
    change RegularCover.groupBaseDerivativeExtension g w.val •
      (mixedTwo θ (triangleGeometricRepresentation g w.val) ᵥ*
        RegularCover.groupRightBlockExtension g w.val) = mixedTwo θ w.val
    simpa only [← triangleRegularAction_val, mixedTwo_restrict,
      RegularCover.groupRightBlockExtension_restrict,
      RegularCover.groupBaseDerivativeExtension_restrict] using
      RegularCover.mixedTwo_group_covariance θ g w)
  exact congrFun heq z

/-- The actual top coefficient has the original base-Jacobian and fibre-determinant law. -/
theorem baseTop_covariance (θ : Form FamilyModel Threefold.Space 3)
    (g : TriangleGroup) (z : ℍ) :
    baseTop θ (triangleGeometricRepresentation g z) *
      RegularCover.groupBaseDerivativeExtension g z *
        (RegularCover.groupRightBlockExtension g z).det = baseTop θ z := by
  have hC := (baseTop_holomorphic θ).continuous
  have hleft := ((hC.comp (triangleGeometricRepresentation_holomorphic g).continuous).mul
    (RegularCover.groupBaseDerivativeExtension_holomorphic g).continuous).mul
      (rightBlock_continuous g).matrix_det
  have heq := continuous_eq_of_regular hleft hC (fun w => by
    simpa only [Function.comp_apply, Pi.mul_apply, ← triangleRegularAction_val, baseTop_restrict,
      RegularCover.groupRightBlockExtension_restrict,
      RegularCover.groupBaseDerivativeExtension_restrict] using
      RegularCover.baseTop_group_covariance θ g w)
  exact congrFun heq z

/-- After the source's prior vertical vanishing step, the actual extended
base coefficient obeys the one-differential law everywhere. -/
theorem baseOne_covariance (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ w : TriangleRegularPoint, RegularCover.fibreOne θ w = 0)
    (g : TriangleGroup) (z : ℍ) :
    baseOne θ hc (triangleGeometricRepresentation g z) *
      RegularCover.groupBaseDerivativeExtension g z = baseOne θ hc z := by
  have hA := (baseOne_holomorphic θ hc).continuous
  have hleft := (hA.comp (triangleGeometricRepresentation_holomorphic g).continuous).mul
    (RegularCover.groupBaseDerivativeExtension_holomorphic g).continuous
  have heq := continuous_eq_of_regular hleft hA (fun w => by
    simpa only [Function.comp_apply, Pi.mul_apply, ← triangleRegularAction_val, baseOne_restrict,
      RegularCover.groupBaseDerivativeExtension_restrict] using
      RegularCover.baseOne_group_covariance θ g w)
  exact congrFun heq z

/-- The genuine second fibre coefficient is invariant on the whole original base. -/
theorem fibreOne_second_invariant (θ : Form FamilyModel Threefold.Space 1)
    (g : TriangleGroup) (z : ℍ) :
    fibreOne θ (triangleGeometricRepresentation g z) 1 = fibreOne θ z 1 := by
  have h := congrFun (fibreOne_covariance θ g z) 1
  have h01 : RegularCover.groupRightBlockExtension g z 0 1 = 0 :=
    congrFun (RegularCover.groupRightBlockExtension_secondColumn g z) 0
  have h11 : RegularCover.groupRightBlockExtension g z 1 1 = 1 :=
    congrFun (RegularCover.groupRightBlockExtension_secondColumn g z) 1
  simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
    h01, h11, mul_zero, mul_one, zero_add] using h

/-- The genuine second mixed coefficient carries only the actual base derivative. -/
theorem mixedTwo_second_covariance (θ : Form FamilyModel Threefold.Space 2)
    (g : TriangleGroup) (z : ℍ) :
    mixedTwo θ (triangleGeometricRepresentation g z) 1 *
      RegularCover.groupBaseDerivativeExtension g z = mixedTwo θ z 1 := by
  have h := congrFun (mixedTwo_covariance θ g z) 1
  have h01 : RegularCover.groupRightBlockExtension g z 0 1 = 0 :=
    congrFun (RegularCover.groupRightBlockExtension_secondColumn g z) 0
  have h11 : RegularCover.groupRightBlockExtension g z 1 1 = 1 :=
    congrFun (RegularCover.groupRightBlockExtension_secondColumn g z) 1
  rw [mul_comm]
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.transpose_apply, h01, h11, mul_zero, mul_one, zero_add] using h

/-- The global first fibre coefficient retains the complete lower shear contribution. -/
theorem fibreOne_first_covariance (θ : Form FamilyModel Threefold.Space 1)
    (g : TriangleGroup) (z : ℍ) :
    fibreOne θ (triangleGeometricRepresentation g z) 0 *
        (RegularCover.groupRightBlockExtension g z).det +
      fibreOne θ (triangleGeometricRepresentation g z) 1 *
        RegularCover.groupRightBlockExtension g z 1 0 = fibreOne θ z 0 := by
  have h := congrFun (fibreOne_covariance θ g z) 0
  simpa only [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
    RegularCover.groupRightBlockExtension_det_eq_entry] using h

/-- The full global first mixed-coefficient law, before the second coefficient vanishes. -/
theorem mixedTwo_first_covariance (θ : Form FamilyModel Threefold.Space 2)
    (g : TriangleGroup) (z : ℍ) :
    (mixedTwo θ (triangleGeometricRepresentation g z) 0 *
        (RegularCover.groupRightBlockExtension g z).det +
      mixedTwo θ (triangleGeometricRepresentation g z) 1 *
        RegularCover.groupRightBlockExtension g z 1 0) *
          RegularCover.groupBaseDerivativeExtension g z = mixedTwo θ z 0 := by
  have h := congrFun (mixedTwo_covariance θ g z) 0
  rw [mul_comm]
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct,
    Fin.sum_univ_two, Matrix.transpose_apply,
    RegularCover.groupRightBlockExtension_det_eq_entry] using h

/-- The native Jacobian is exactly the scalar derivative used by the
source's differential vanishing theorems, in the same original charts. -/
theorem groupBaseDerivativeExtension_eq_actionDerivative (g : TriangleGroup) (z : ℍ) :
    RegularCover.groupBaseDerivativeExtension g z =
      TriangleHolomorphicDifferentials.actionDerivative g z := by
  have h : mfderiv I₁ I₁ (triangleGeometricRepresentation g : ℍ → ℍ) z =
      fderiv ℂ (fun w : ℂ =>
        (triangleGeometricRepresentation g (UpperHalfPlane.ofComplex w) : ℂ)) (z : ℂ) := by
    simpa [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
      chartAt_self_eq, UpperHalfPlane.ofComplex, Function.comp_def] using
      ((triangleGeometricRepresentation_holomorphic g z).mdifferentiableAt (by simp)).mfderiv
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) h

/-- Both determinant factors are computed from the same actual global special periods. -/
theorem groupRightBlockExtension_det_eq_determinantFactor (g : TriangleGroup) (z : ℍ) :
    (RegularCover.groupRightBlockExtension g z).det =
      TriangleHolomorphicDifferentials.determinantFactor g z := rfl

theorem groupRightBlockExtension_det_inv_eq_inverseDeterminantFactor
    (g : TriangleGroup) (z : ℍ) :
    ((RegularCover.groupRightBlockExtension g z).det)⁻¹ =
      TriangleHolomorphicDifferentials.inverseDeterminantFactor g z := rfl

/-- The genuine second mixed coefficient satisfies exactly the existing
invariant one-differential predicate. -/
theorem mixedTwo_second_isInvariantDifferential (θ : Form FamilyModel Threefold.Space 2) :
    TriangleHolomorphicDifferentials.IsInvariantDifferential 1 (fun z => mixedTwo θ z 1) := by
  intro g z
  simpa only [pow_one, groupBaseDerivativeExtension_eq_actionDerivative] using
    mixedTwo_second_covariance θ g z

theorem baseOne_isInvariantDifferential (θ : Form FamilyModel Threefold.Space 1)
    (hc : ∀ w : TriangleRegularPoint, RegularCover.fibreOne θ w = 0) :
    TriangleHolomorphicDifferentials.IsInvariantDifferential 1 (baseOne θ hc) := by
  intro g z
  simpa only [pow_one, groupBaseDerivativeExtension_eq_actionDerivative] using
    baseOne_covariance θ hc g z

private theorem isWeightOne_of_block_covariance {F : ℍ → ℂ}
    (hF : ∀ (g : TriangleGroup) (z : ℍ),
      F (triangleGeometricRepresentation g z) * RegularCover.groupBaseDerivativeExtension g z *
        (RegularCover.groupRightBlockExtension g z).det = F z) :
    TriangleHolomorphicDifferentials.IsWeightOneDifferential F := by
  intro g z
  rw [TriangleHolomorphicDifferentials.inverseDeterminantFactor_eq_inv]
  have h := hF g z
  rw [groupBaseDerivativeExtension_eq_actionDerivative,
    groupRightBlockExtension_det_eq_determinantFactor] at h
  calc
    F (triangleGeometricRepresentation g z) *
        TriangleHolomorphicDifferentials.actionDerivative g z =
        F z / TriangleHolomorphicDifferentials.determinantFactor g z :=
      (eq_div_iff (TriangleHolomorphicDifferentials.determinantFactor_ne_zero g z)).mpr h
    _ = (TriangleHolomorphicDifferentials.determinantFactor g z)⁻¹ * F z := by
      rw [div_eq_mul_inv, mul_comm]

/-- The genuine top coefficient has exactly the reciprocal-determinant
weight used by the source's weight-one vanishing theorem. -/
theorem baseTop_isWeightOneDifferential (θ : Form FamilyModel Threefold.Space 3) :
    TriangleHolomorphicDifferentials.IsWeightOneDifferential (baseTop θ) :=
  isWeightOne_of_block_covariance (baseTop_covariance θ)

/-- Once the genuine second mixed coefficient vanishes, the first has
the same actual weight-one law as the top coefficient. -/
theorem mixedTwo_first_isWeightOneDifferential (θ : Form FamilyModel Threefold.Space 2)
    (hsecond : (fun z : ℍ => mixedTwo θ z 1) = 0) :
    TriangleHolomorphicDifferentials.IsWeightOneDifferential (fun z => mixedTwo θ z 0) := by
  apply isWeightOne_of_block_covariance
  intro g z
  have h := mixedTwo_first_covariance θ g z
  have hs : mixedTwo θ (triangleGeometricRepresentation g z) 1 = 0 :=
    congrFun hsecond (triangleGeometricRepresentation g z)
  rw [hs, zero_mul, add_zero, mul_right_comm] at h
  exact h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticExtension
