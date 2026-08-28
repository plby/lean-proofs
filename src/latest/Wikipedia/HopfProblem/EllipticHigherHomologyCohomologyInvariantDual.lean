import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDeckFixed
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsMap
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologySpaces

/-!
# Actual invariant cohomology and the dual deck-coinvariant covering map

All projectivity needed by integral singular evaluation follows from the
already proved actual torus and surface homology.  The actual all-deck
invariant cohomology is therefore the integer dual of the actual inverse
deck coinvariants.  Under these equivalences the original covering's
pullback is exactly the dual of its induced coinvariant map, on every
actual class and in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- Evaluation for the genuine period-torus singular cochain complex;
the required projectivity is proved from its actual homology computation. -/
def periodTorusEvaluationEquiv (p : PeriodDomain) (n : ℕ) :
    SingularCohomology p.Torus n ≃ₗ[ℤ] Module.Dual ℤ (SingularHomology p.Torus n) := by
  letI (k : ℕ) : Module.Projective ℤ (SingularHomology p.Torus k) := by
    let := periodTorus_homology_free p k
    infer_instance
  exact singularEvaluationEquiv p.Torus n

@[simp] theorem periodTorusEvaluationEquiv_apply (p : PeriodDomain) (n : ℕ)
    (a : SingularCohomology p.Torus n) :
    periodTorusEvaluationEquiv p n a = singularEvaluation p.Torus n a := rfl

/-- Evaluation for the actual main central surface, with no projectivity assumption. -/
def surfaceEvaluationEquiv (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      Module.Dual ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) := by
  letI (k : ℕ) : Module.Projective ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) k) :=
    Module.Projective.of_basis
      ((Pi.basisFun ℤ (Fin (ellipticBettiNumber k))).map (surfaceHomologyCoordinates j p k).symm)
  exact singularEvaluationEquiv (Surface j p j.twist (mainTwist_admissible j)) n

@[simp] theorem surfaceEvaluationEquiv_apply (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :
    surfaceEvaluationEquiv j p n a =
      singularEvaluation (Surface j p j.twist (mainTwist_admissible j)) n a := rfl

/-- The actual invariant condition is integral annihilation of the
actual inverse-deck difference. -/
theorem periodCohomologyInvariants_iff_annihilator (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularCohomology p.val.Torus n) :
    a ∈ periodCohomologyInvariants j p j.twist (mainTwist_admissible j) n ↔
      periodTorusEvaluationEquiv p.val n a ∈
        (LinearMap.range (periodDeckDifference j p n)).dualAnnihilator := by
  let (k : ℕ) : Module.Projective ℤ (SingularHomology p.val.Torus k) := by
    let := periodTorus_homology_free p.val k
    infer_instance
  rw [periodCohomologyInvariants_eq_inverse_fixed]
  exact singularEvaluation_fixed_iff (surfaceInverseAffineGenerator j p j.twist) n a

/-- The genuine invariant cohomology is the integral dual of the genuine deck quotient. -/
def periodCohomologyInvariantsEquivDualCoinvariants (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    periodCohomologyInvariants j p j.twist (mainTwist_admissible j) n ≃ₗ[ℤ]
      Module.Dual ℤ (SingularHomology p.val.Torus n ⧸
        LinearMap.range (periodDeckDifference j p n)) :=
  evaluationDualQuotientEquivInt (periodTorusEvaluationEquiv p.val n)
    (periodCohomologyInvariants j p j.twist (mainTwist_admissible j) n)
    (LinearMap.range (periodDeckDifference j p n))
    (periodCohomologyInvariants_iff_annihilator j p n)

/-- Actual evaluation on every represented homology coinvariant is preserved. -/
@[simp] theorem periodCohomologyInvariantsEquivDualCoinvariants_apply_mk
    (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : periodCohomologyInvariants j p j.twist (mainTwist_admissible j) n)
    (b : SingularHomology p.val.Torus n) :
    periodCohomologyInvariantsEquivDualCoinvariants j p n a (Submodule.Quotient.mk b) =
      singularEvaluation p.val.Torus n a b := rfl

/-- The original covering pullback is exactly the dual of the actual map on deck coinvariants. -/
theorem periodCoverCohomologyToInvariants_dual (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :
    periodCohomologyInvariantsEquivDualCoinvariants j p n
      (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) n a) =
      (periodCoverFromDeckCoinvariants j p n).dualMap (surfaceEvaluationEquiv j p n a) := by
  ext b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (periodDeckDifference j p n)) b
  rw [periodCohomologyInvariantsEquivDualCoinvariants_apply_mk]
  change singularEvaluation p.val.Torus n
    (singularCohomologyPullback (periodCover j p j.twist (mainTwist_admissible j)) n a) x =
      singularEvaluation (Surface j p j.twist (mainTwist_admissible j)) n a
        (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) n x)
  exact singularEvaluation_naturality _ n a x

/-- The complete native cohomology/coinvariant-dual square commutes as linear maps. -/
theorem periodCoverCohomologyToInvariants_dual_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (periodCohomologyInvariantsEquivDualCoinvariants j p n).toLinearMap.comp
      (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) n) =
      (periodCoverFromDeckCoinvariants j p n).dualMap.comp
        (surfaceEvaluationEquiv j p n).toLinearMap := by
  ext a b
  exact LinearMap.congr_fun (periodCoverCohomologyToInvariants_dual j p n a) b

end Wikipedia.HopfProblem.Elliptic.HigherHomology
