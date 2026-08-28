import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarking
import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Native second cohomology and integral alternating period forms

Canonical singular-cochain evaluation and the proved exterior-square
marking of actual period-torus homology identify native integral second
cohomology with alternating integer forms on the period lattice.
All projectivity is supplied by the actual torus homology computation.

The inverse assigns an actual cohomology class to every alternating form.
Its evaluation on the actual product of the positive period loops for
`x` and `y` is exactly the alternating form evaluated on `![x,y]`.
These evaluations also characterize the class uniquely.  No cup-product,
Chern-class or orientation comparison is asserted here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin

/-- Native evaluation on the genuine period torus, with actual homology
freeness supplying every required projectivity instance. -/
def evaluationEquiv (p : PeriodDomain) (n : ℕ) :
    SingularCohomology p.Torus n ≃ₗ[ℤ] Module.Dual ℤ (SingularHomology p.Torus n) := by
  letI (k : ℕ) : Module.Projective ℤ (SingularHomology p.Torus k) := by
    let := periodTorus_homology_free p k
    infer_instance
  exact singularEvaluationEquiv p.Torus n

@[simp] theorem evaluationEquiv_apply (p : PeriodDomain) (n : ℕ)
    (a : SingularCohomology p.Torus n) :
    evaluationEquiv p n a = singularEvaluation p.Torus n a := rfl

/-- Actual integral second cohomology as alternating forms on the actual period lattice. -/
def cohomologyAlternatingEquiv (p : PeriodDomain) :
    SingularCohomology p.Torus 2 ≃ₗ[ℤ] AlternatingMap ℤ Lattice ℤ (Fin 2) :=
  (evaluationEquiv p 2).trans
    ((periodTorusH2ExteriorEquiv p).symm.dualMap.trans
      exteriorPower.alternatingMapLinearEquiv.symm)

/-- The underlying alternating form is canonical evaluation on the actual exterior marking. -/
theorem cohomologyAlternatingEquiv_apply_exterior (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) (v : Fin 2 → Lattice) :
    cohomologyAlternatingEquiv p a v =
      singularEvaluation p.Torus 2 a
        ((periodTorusH2ExteriorEquiv p).symm (exteriorPower.ιMulti ℤ 2 v)) := by
  simp only [cohomologyAlternatingEquiv, LinearEquiv.trans_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply,
    LinearMap.compAlternatingMap_apply, LinearEquiv.dualMap_apply, evaluationEquiv_apply]

/-- The alternating form evaluates the original cohomology class on the
actual product of the two ordered positive period loops. -/
theorem cohomologyAlternatingEquiv_apply (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) (v : Fin 2 → Lattice) :
    cohomologyAlternatingEquiv p a v =
      singularEvaluation p.Torus 2 a
        (product11 p.Torus (loopHomologyClass (p.periodLoop (v 0)))
          (loopHomologyClass (p.periodLoop (v 1)))) := by
  rw [cohomologyAlternatingEquiv_apply_exterior,
    periodTorusH2ExteriorEquiv_symm_ιMulti]

/-- The actual native cohomology class determined by an integral alternating form. -/
def alternatingClass (p : PeriodDomain) (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    SingularCohomology p.Torus 2 :=
  (cohomologyAlternatingEquiv p).symm B

@[simp] theorem cohomologyAlternatingEquiv_alternatingClass (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    cohomologyAlternatingEquiv p (alternatingClass p B) = B :=
  (cohomologyAlternatingEquiv p).apply_symm_apply B

@[simp] theorem alternatingClass_cohomologyAlternatingEquiv (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    alternatingClass p (cohomologyAlternatingEquiv p a) = a :=
  (cohomologyAlternatingEquiv p).symm_apply_apply a

/-- Evaluation on every actual homology class is the exterior lift of the form. -/
theorem alternatingClass_evaluate (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (z : SingularHomology p.Torus 2) :
    singularEvaluation p.Torus 2 (alternatingClass p B) z =
      exteriorPower.alternatingMapLinearEquiv B (periodTorusH2ExteriorEquiv p z) := by
  change evaluationEquiv p 2 (alternatingClass p B) z = _
  simp only [alternatingClass, cohomologyAlternatingEquiv,
    LinearEquiv.symm_trans_apply, LinearEquiv.dualMap_symm, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply]

theorem alternatingClass_evaluate_exterior (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (v : Fin 2 → Lattice) :
    singularEvaluation p.Torus 2 (alternatingClass p B)
      ((periodTorusH2ExteriorEquiv p).symm (exteriorPower.ιMulti ℤ 2 v)) = B v := by
  rw [alternatingClass_evaluate, LinearEquiv.apply_symm_apply,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- Exact integral evaluation on the genuine product of the two positive period loops. -/
theorem alternatingClass_evaluate_periodLoops (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (x y : Lattice) :
    singularEvaluation p.Torus 2 (alternatingClass p B)
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) = B ![x, y] := by
  have h := alternatingClass_evaluate_exterior p B ![x, y]
  rw [periodTorusH2ExteriorEquiv_symm_ιMulti] at h
  exact h

/-- Actual period-loop products detect every native integral second cohomology class. -/
theorem cohomology_ext_periodLoops (p : PeriodDomain)
    {a b : SingularCohomology p.Torus 2}
    (h : ∀ x y : Lattice,
      singularEvaluation p.Torus 2 a
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) =
      singularEvaluation p.Torus 2 b
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y)))) : a = b := by
  apply (cohomologyAlternatingEquiv p).injective
  apply AlternatingMap.ext
  intro v
  rw [cohomologyAlternatingEquiv_apply, cohomologyAlternatingEquiv_apply]
  exact h (v 0) (v 1)

theorem alternatingClass_unique (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) (a : SingularCohomology p.Torus 2)
    (h : ∀ x y : Lattice,
      singularEvaluation p.Torus 2 a
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) = B ![x, y]) :
    a = alternatingClass p B := by
  apply cohomology_ext_periodLoops p
  intro x y
  rw [alternatingClass_evaluate_periodLoops]
  exact h x y

/-- Every integral alternating form gives one and only one actual class with these evaluations. -/
theorem existsUnique_alternatingClass (p : PeriodDomain)
    (B : AlternatingMap ℤ Lattice ℤ (Fin 2)) :
    ∃! a : SingularCohomology p.Torus 2, ∀ x y : Lattice,
      singularEvaluation p.Torus 2 a
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) = B ![x, y] :=
  ⟨alternatingClass p B, alternatingClass_evaluate_periodLoops p B,
    fun a h => alternatingClass_unique p B a h⟩

/-- Conversely every native second cohomology class arises from exactly one alternating form. -/
theorem alternatingClass_bijective (p : PeriodDomain) :
    Function.Bijective (alternatingClass p) :=
  (cohomologyAlternatingEquiv p).symm.bijective

end Wikipedia.HopfProblem.PeriodTorusCohomology
