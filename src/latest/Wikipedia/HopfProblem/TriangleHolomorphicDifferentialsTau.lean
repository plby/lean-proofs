import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsGeometryGenerators
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTauData
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTauRegular
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsTauCuspOrder

/-!
# The actual first-period differential and its determinant covariance

Differentiating the two proved period identities gives the source
determinant-square law for the two actual triangle generators. The chain
rule and the actual determinant cocycle extend this law to every word
in the constructed triangle group. The derivative is holomorphic,
nonzero on the actual regular locus, and has analytic cusp order zero.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

open SpecialPeriods

/-- The actual scalar derivative of the actual first special period. -/
def tauDerivative : ℍ → ℂ := scalarDeriv specialTau

theorem tauDerivative_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω tauDerivative :=
  scalarDeriv_holomorphic specialTau_holomorphic

theorem tauHasDerivAt (z : ℍ) :
    HasDerivAt (specialTau ∘ ofComplex) (tauDerivative z) (z : ℂ) :=
  scalarHasDerivAt specialTau_holomorphic z

/-- The differentiated first-generator identity uses the determinant
of the actual complex period-covariance matrix. -/
theorem tauDerivative_covariance_generator₁ (z : ℍ) :
    tauDerivative (triangleGeometricRepresentation triangleGenerator₁ z) *
        actionDerivative triangleGenerator₁ z =
      determinantFactor triangleGenerator₁ z ^ 2 * tauDerivative z := by
  have hn : (specialTau ∘ ofComplex) (z : ℂ) ≠ 0 := by
    simpa only [Function.comp_apply, ofComplex_apply] using specialTau_ne_zero z
  have hd := ((tauHasDerivAt z).sub_const 1).fun_div (tauHasDerivAt z) hn
  have hd' : HasDerivAt
      (fun w : ℂ => (specialTau (ofComplex w) - 1) / specialTau (ofComplex w))
      ((tauDerivative z * specialTau z - (specialTau z - 1) * tauDerivative z) /
        specialTau z ^ 2) (z : ℂ) := by
    simpa only [Function.comp_apply, ofComplex_apply] using hd
  have hcoeff :
      (tauDerivative z * specialTau z - (specialTau z - 1) * tauDerivative z) /
          specialTau z ^ 2 = determinantFactor triangleGenerator₁ z ^ 2 * tauDerivative z := by
    rw [determinantFactor_generator₁, div_pow]
    norm_num
    ring
  have hf : ((specialTau ∘ triangleGeometricRepresentation triangleGenerator₁) ∘ ofComplex) =
      fun w : ℂ => (specialTau (ofComplex w) - 1) / specialTau (ofComplex w) := by
    funext w
    simp only [Function.comp_apply, triangleGeometricRepresentation_generator₁_apply]
    exact (specialPeriods_generator₁ (ofComplex w)).1
  have he := (hd'.congr_deriv hcoeff).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun w => congrFun hf w))
  exact (scalarDeriv_comp_action specialTau_holomorphic triangleGenerator₁ z).symm.trans he.deriv

/-- The differentiated second-generator identity in the same actual convention. -/
theorem tauDerivative_covariance_generator₂ (z : ℍ) :
    tauDerivative (triangleGeometricRepresentation triangleGenerator₂ z) *
        actionDerivative triangleGenerator₂ z =
      determinantFactor triangleGenerator₂ z ^ 2 * tauDerivative z := by
  have hn : (specialTau ∘ ofComplex) (z : ℂ) ≠ 0 := by
    simpa only [Function.comp_apply, ofComplex_apply] using specialTau_ne_zero z
  have hd := (hasDerivAt_const (z : ℂ) (-1 : ℂ)).fun_div (tauHasDerivAt z) hn
  have hd' : HasDerivAt (fun w : ℂ => -1 / specialTau (ofComplex w))
      ((0 * specialTau z - (-1) * tauDerivative z) / specialTau z ^ 2) (z : ℂ) := by
    simpa only [Function.comp_apply, ofComplex_apply] using hd
  have hcoeff :
      (0 * specialTau z - (-1) * tauDerivative z) / specialTau z ^ 2 =
        determinantFactor triangleGenerator₂ z ^ 2 * tauDerivative z := by
    rw [determinantFactor_generator₂, div_pow]
    norm_num
    ring
  have hf : ((specialTau ∘ triangleGeometricRepresentation triangleGenerator₂) ∘ ofComplex) =
      fun w : ℂ => -1 / specialTau (ofComplex w) := by
    funext w
    simp only [Function.comp_apply, triangleGeometricRepresentation_generator₂_apply]
    exact (specialPeriods_generator₂ (ofComplex w)).1
  have he := (hd'.congr_deriv hcoeff).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun w => congrFun hf w))
  exact (scalarDeriv_comp_action specialTau_holomorphic triangleGenerator₂ z).symm.trans he.deriv

private def HasTauCovariance (g : TriangleGroup) : Prop :=
  ∀ z : ℍ, tauDerivative (triangleGeometricRepresentation g z) * actionDerivative g z =
    determinantFactor g z ^ 2 * tauDerivative z

private theorem hasTauCovariance_one : HasTauCovariance 1 := by
  intro z
  simp only [map_one, Equiv.Perm.one_apply, actionDerivative_one,
    determinantFactor_one, one_pow, mul_one, one_mul]

private theorem hasTauCovariance_mul {g h : TriangleGroup}
    (hg : HasTauCovariance g) (hh : HasTauCovariance h) : HasTauCovariance (g * h) := by
  intro z
  rw [map_mul, Equiv.Perm.mul_apply, actionDerivative_mul, determinantFactor_mul]
  calc
    _ = (tauDerivative (triangleGeometricRepresentation g (triangleGeometricRepresentation h z)) *
        actionDerivative g (triangleGeometricRepresentation h z)) * actionDerivative h z := by ring
    _ = (determinantFactor g (triangleGeometricRepresentation h z) ^ 2 *
        tauDerivative (triangleGeometricRepresentation h z)) * actionDerivative h z := by
      rw [hg]
    _ = determinantFactor g (triangleGeometricRepresentation h z) ^ 2 *
        (tauDerivative (triangleGeometricRepresentation h z) * actionDerivative h z) := by ring
    _ = determinantFactor g (triangleGeometricRepresentation h z) ^ 2 *
        (determinantFactor h z ^ 2 * tauDerivative z) := by rw [hh]
    _ = _ := by ring

private theorem hasTauCovariance_pow {g : TriangleGroup}
    (hg : HasTauCovariance g) (n : ℕ) : HasTauCovariance (g ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using hasTauCovariance_one
  | succ n ih => simpa only [pow_succ] using hasTauCovariance_mul ih hg

private theorem cyclic_eq_generator_pow {n : ℕ} [NeZero n]
    (x : Multiplicative (ZMod n)) :
    x = Multiplicative.ofAdd (1 : ZMod n) ^ x.toAdd.val := by
  change x.toAdd = x.toAdd.val • (1 : ZMod n)
  simpa only [nsmul_eq_mul, mul_one] using (ZMod.natCast_zmod_val x.toAdd).symm

/-- The determinant-square transformation law holds for every element
of the actual triangle group, not just for its two generators. -/
theorem tauDerivative_covariance (g : TriangleGroup) (z : ℍ) :
    tauDerivative (triangleGeometricRepresentation g z) * actionDerivative g z =
      determinantFactor g z ^ 2 * tauDerivative z := by
  have hg : HasTauCovariance g := by
    induction g using Monoid.Coprod.induction_on with
    | inl x =>
        rw [cyclic_eq_generator_pow x, map_pow]
        exact hasTauCovariance_pow tauDerivative_covariance_generator₁ _
    | inr x =>
        rw [cyclic_eq_generator_pow x, map_pow]
        exact hasTauCovariance_pow tauDerivative_covariance_generator₂ _
    | mul g h hg hh => exact hasTauCovariance_mul hg hh
  exact hg z

/-- The same source formula written with its reciprocal determinant factor. -/
theorem tauDerivative_covariance_inverseFactor (g : TriangleGroup) (z : ℍ) :
    tauDerivative (triangleGeometricRepresentation g z) * actionDerivative g z =
      inverseDeterminantFactor g z ^ (-2 : ℤ) * tauDerivative z := by
  have hi : inverseDeterminantFactor g z ^ (-2 : ℤ) = determinantFactor g z ^ 2 := by
    simp only [inverseDeterminantFactor_eq_inv, zpow_neg, zpow_ofNat, inv_pow, inv_inv]
  rw [hi]
  exact tauDerivative_covariance g z

/-- A scalar-derivative spelling for direct use with coefficient functions. -/
theorem specialTau_scalarDeriv_covariance (g : TriangleGroup) (z : ℍ) :
    scalarDeriv specialTau (triangleGeometricRepresentation g z) * actionDerivative g z =
      determinantFactor g z ^ 2 * scalarDeriv specialTau z := tauDerivative_covariance g z

@[simp] theorem tauDerivative_cusp (z : ℍ) :
    tauDerivative (triangleGeometricRepresentation triangleCuspGenerator z) = tauDerivative z := by
  simpa only [actionDerivative_cusp, determinantFactor_cusp, one_pow, mul_one, one_mul] using
    tauDerivative_covariance triangleCuspGenerator z

theorem tauDerivative_ne_zero_of_regular {z : ℍ} (hz : z ∈ triangleRegularLocus) :
    tauDerivative z ≠ 0 := specialTau_scalarDeriv_ne_zero_of_regular hz

theorem tauDerivative_hasCuspOrder_zero : HasCuspOrder 0 tauDerivative :=
  specialTau_scalarDeriv_hasCuspOrder_zero

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
