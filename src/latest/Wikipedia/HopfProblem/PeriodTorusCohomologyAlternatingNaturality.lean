import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMonodromy

/-!
# Actual pullback of native alternating cohomology classes

Canonical evaluation transports a verified exterior-square homology
diagram to the native singular-cohomology pullback.  The generic
statement is then applied to all three genuine period-change maps using
their already proved actual homology markings.  The final period-change
equations have no homology, cohomology, projectivity or matrix-action
hypothesis.

The affine elliptic actions and any Chern-class interpretation are
outside the scope of this file.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- The universal exterior lift respects precomposition on the period lattice. -/
theorem exteriorLift_compLinearMap (A : Lattice →ₗ[ℤ] Lattice)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    exteriorPower.alternatingMapLinearEquiv (B.compLinearMap A) =
      (exteriorPower.alternatingMapLinearEquiv B).comp (exteriorPower.map 2 A) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, Function.comp_def]

/-- A genuine exterior-square homology diagram determines the actual
pullback of every native alternating cohomology class. -/
theorem alternatingClass_pullback_of_exterior (p q : PeriodDomain)
    (f : C(p.Torus, q.Torus)) (A : Lattice →ₗ[ℤ] Lattice)
    (hA : ∀ z : SingularHomology p.Torus 2,
      periodTorusH2ExteriorEquiv q (singularHomologyMap f 2 z) =
        exteriorPower.map 2 A (periodTorusH2ExteriorEquiv p z))
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback f 2 (alternatingClass q B) =
      alternatingClass p (B.compLinearMap A) := by
  apply (evaluationEquiv p 2).injective
  apply LinearMap.ext
  intro z
  simp only [evaluationEquiv_apply, singularEvaluation_naturality,
    alternatingClass_evaluate, hA]
  rw [exteriorLift_compLinearMap]
  rfl

/-- The same actual pullback statement expressed in alternating-form coordinates. -/
theorem cohomologyAlternatingEquiv_pullback_of_exterior (p q : PeriodDomain)
    (f : C(p.Torus, q.Torus)) (A : Lattice →ₗ[ℤ] Lattice)
    (hA : ∀ z : SingularHomology p.Torus 2,
      periodTorusH2ExteriorEquiv q (singularHomologyMap f 2 z) =
        exteriorPower.map 2 A (periodTorusH2ExteriorEquiv p z))
    (a : SingularCohomology q.Torus 2) :
    cohomologyAlternatingEquiv p (singularCohomologyPullback f 2 a) =
      (cohomologyAlternatingEquiv q a).compLinearMap A := by
  have h := congrArg (cohomologyAlternatingEquiv p)
    (alternatingClass_pullback_of_exterior p q f A hA (cohomologyAlternatingEquiv q a))
  simpa only [alternatingClass_cohomologyAlternatingEquiv,
    cohomologyAlternatingEquiv_alternatingClass] using h

/-- For an actual additive map it suffices to verify its genuine first-homology marking. -/
theorem alternatingClass_pullback_of_h1 (p q : PeriodDomain)
    (f : C(p.Torus, q.Torus)) (hf : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (p.singularH1Equiv.symm v) =
      q.singularH1Equiv.symm (A v))
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback f 2 (alternatingClass q B) =
      alternatingClass p (B.compLinearMap A) :=
  alternatingClass_pullback_of_exterior p q f A
    (periodTorusH2ExteriorEquiv_natural p q f hf A hmark) B

/-- Pullback by the actual period-change map `step₁` on every alternating class. -/
theorem alternatingClass_pullback_step₁ (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback p.step₁ContinuousMap 2 (alternatingClass p.step₁ B) =
      alternatingClass p (B.compLinearMap A₁.mulVecLin) :=
  alternatingClass_pullback_of_exterior p p.step₁ p.step₁ContinuousMap A₁.mulVecLin
    (periodTorusH2ExteriorEquiv_step₁ p) B

/-- Actual alternating-form coordinates of pullback by `step₁`, for every native class. -/
theorem cohomologyAlternatingEquiv_pullback_step₁ (p : PeriodDomain)
    (a : SingularCohomology p.step₁.Torus 2) :
    cohomologyAlternatingEquiv p (singularCohomologyPullback p.step₁ContinuousMap 2 a) =
      (cohomologyAlternatingEquiv p.step₁ a).compLinearMap A₁.mulVecLin :=
  cohomologyAlternatingEquiv_pullback_of_exterior
    p p.step₁ p.step₁ContinuousMap A₁.mulVecLin
    (periodTorusH2ExteriorEquiv_step₁ p) a

/-- Pullback by the actual period-change map `step₂` on every alternating class. -/
theorem alternatingClass_pullback_step₂ (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback p.step₂ContinuousMap 2 (alternatingClass p.step₂ B) =
      alternatingClass p (B.compLinearMap A₂.mulVecLin) :=
  alternatingClass_pullback_of_exterior p p.step₂ p.step₂ContinuousMap A₂.mulVecLin
    (periodTorusH2ExteriorEquiv_step₂ p) B

/-- Actual alternating-form coordinates of pullback by `step₂`, for every native class. -/
theorem cohomologyAlternatingEquiv_pullback_step₂ (p : PeriodDomain)
    (a : SingularCohomology p.step₂.Torus 2) :
    cohomologyAlternatingEquiv p (singularCohomologyPullback p.step₂ContinuousMap 2 a) =
      (cohomologyAlternatingEquiv p.step₂ a).compLinearMap A₂.mulVecLin :=
  cohomologyAlternatingEquiv_pullback_of_exterior
    p p.step₂ p.step₂ContinuousMap A₂.mulVecLin
    (periodTorusH2ExteriorEquiv_step₂ p) a

/-- Pullback by the actual period-change map `step₀` on every alternating class. -/
theorem alternatingClass_pullback_step₀ (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    singularCohomologyPullback p.step₀ContinuousMap 2 (alternatingClass p.step₀ B) =
      alternatingClass p (B.compLinearMap M₀.mulVecLin) :=
  alternatingClass_pullback_of_exterior p p.step₀ p.step₀ContinuousMap M₀.mulVecLin
    (periodTorusH2ExteriorEquiv_step₀ p) B

/-- Actual alternating-form coordinates of pullback by `step₀`, for every native class. -/
theorem cohomologyAlternatingEquiv_pullback_step₀ (p : PeriodDomain)
    (a : SingularCohomology p.step₀.Torus 2) :
    cohomologyAlternatingEquiv p (singularCohomologyPullback p.step₀ContinuousMap 2 a) =
      (cohomologyAlternatingEquiv p.step₀ a).compLinearMap M₀.mulVecLin :=
  cohomologyAlternatingEquiv_pullback_of_exterior
    p p.step₀ p.step₀ContinuousMap M₀.mulVecLin
    (periodTorusH2ExteriorEquiv_step₀ p) a

end Wikipedia.HopfProblem.PeriodTorusCohomology
