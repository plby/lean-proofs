import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingFullPeriod
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingPullback

/-!
# Native alternating-cohomology pullback on arbitrary full period tori

A verified diagram on actual full-period second homology determines the
native singular-cohomology pullback of every alternating class and every
six-coefficient class.  For continuous additive maps the already proved
exterior-square naturality reduces this to the actual degree-one marking.
No normalization of either full period matrix is needed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- An actual exterior-square homology diagram determines native full-period pullback. -/
theorem fullAlternatingClass_pullback_of_exterior (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (A : Lattice →ₗ[ℤ] Lattice)
    (hA : ∀ z : SingularHomology q.Torus 2,
      fullPeriodTorusH2ExteriorEquiv r (singularHomologyMap f 2 z) =
        exteriorPower.map 2 A (fullPeriodTorusH2ExteriorEquiv q z))
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback f 2 (fullAlternatingClass r B) =
      fullAlternatingClass q (B.compLinearMap A) := by
  apply (fullEvaluationEquiv q 2).injective
  apply LinearMap.ext
  intro z
  simp only [fullEvaluationEquiv_apply, singularEvaluation_naturality,
    fullAlternatingClass_evaluate, hA]
  rw [exteriorLift_compLinearMap]
  rfl

/-- The same actual diagram gives pullback coordinates for every native cohomology class. -/
theorem fullCohomologyAlternatingEquiv_pullback_of_exterior (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (A : Lattice →ₗ[ℤ] Lattice)
    (hA : ∀ z : SingularHomology q.Torus 2,
      fullPeriodTorusH2ExteriorEquiv r (singularHomologyMap f 2 z) =
        exteriorPower.map 2 A (fullPeriodTorusH2ExteriorEquiv q z))
    (a : SingularCohomology r.Torus 2) :
    fullCohomologyAlternatingEquiv q (singularCohomologyPullback f 2 a) =
      (fullCohomologyAlternatingEquiv r a).compLinearMap A := by
  have h := congrArg (fullCohomologyAlternatingEquiv q)
    (fullAlternatingClass_pullback_of_exterior q r f A hA
      (fullCohomologyAlternatingEquiv r a))
  simpa only [fullAlternatingClass_fullCohomologyAlternatingEquiv,
    fullCohomologyAlternatingEquiv_fullAlternatingClass] using h

/-- For a genuine additive map its actual first-homology marking suffices. -/
theorem fullAlternatingClass_pullback_of_h1 (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (hf : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v))
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback f 2 (fullAlternatingClass r B) =
      fullAlternatingClass q (B.compLinearMap A) :=
  fullAlternatingClass_pullback_of_exterior q r f A
    (fullPeriodTorusH2ExteriorEquiv_natural q r f hf A hmark) B

/-- Actual degree-one naturality determines the alternating coordinates of every pullback. -/
theorem fullCohomologyAlternatingEquiv_pullback_of_h1 (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (hf : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v))
    (a : SingularCohomology r.Torus 2) :
    fullCohomologyAlternatingEquiv q (singularCohomologyPullback f 2 a) =
      (fullCohomologyAlternatingEquiv r a).compLinearMap A :=
  fullCohomologyAlternatingEquiv_pullback_of_exterior q r f A
    (fullPeriodTorusH2ExteriorEquiv_natural q r f hf A hmark) a

/-- The verified full-period homology diagram gives the actual six-coefficient pullback. -/
theorem fullCoefficientClass_pullback_of_exterior (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (A : Lattice →ₗ[ℤ] Lattice)
    (hA : ∀ z : SingularHomology q.Torus 2,
      fullPeriodTorusH2ExteriorEquiv r (singularHomologyMap f 2 z) =
        exteriorPower.map 2 A (fullPeriodTorusH2ExteriorEquiv q z)) (E : Fin 6 → ℤ) :
    singularCohomologyPullback f 2 (fullCoefficientClass r E) =
      fullCoefficientClass q (coefficientPullback A E) := by
  rw [fullCoefficientClass_asAlternating, fullCoefficientClass_asAlternating,
    coefficientAlternatingEquiv_coefficientPullback]
  exact fullAlternatingClass_pullback_of_exterior q r f A hA _

/-- For additive full-period maps the actual degree-one action determines coefficient pullback. -/
theorem fullCoefficientClass_pullback_of_h1 (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (hf : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v)) (E : Fin 6 → ℤ) :
    singularCohomologyPullback f 2 (fullCoefficientClass r E) =
      fullCoefficientClass q (coefficientPullback A E) :=
  fullCoefficientClass_pullback_of_exterior q r f A
    (fullPeriodTorusH2ExteriorEquiv_natural q r f hf A hmark) E

end Wikipedia.HopfProblem.PeriodTorusCohomology
