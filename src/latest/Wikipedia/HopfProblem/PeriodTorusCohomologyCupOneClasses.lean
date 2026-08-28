import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneBasic
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Coordinate classes and their actual homology evaluations

The native cocycle representatives give classes in the actual singular
cohomology group.  Their evaluation is the homology map of the corresponding
circle projection.  Pulling back by the genuine period-coordinate
homeomorphism gives the same representatives on every original period torus.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz PeriodTorusHigherHomology SingularCohomologyFree SingularMayerVietoris

/-- Actual cohomology evaluation on a based loop is the coordinate homology functional. -/
theorem coordinateOneClass_evaluation_loop (n : ℕ) (i : Fin n)
    (p : Path (0 : ProductTorus n) 0) :
    singularEvaluation (ProductTorus n) 1 (coordinateOneClass n i) (loopHomologyClass p) =
      coordinateH1Functional n i (loopHomologyClass p) := by
  let c : ModuleHomology.Cycle (singularComplex (ProductTorus n)) 1 := loopCycle p
  have h := singularEvaluation_cocycle_cycle (ProductTorus n) 1
    (coordinateOneCocycle n i) c
  exact h.trans (coordinateOneCochain_loop n i p)

/-- The equality concerns every actual first-homology class, not only the displayed loops. -/
theorem coordinateOneClass_evaluation (n : ℕ) (i : Fin n) :
    singularEvaluation (ProductTorus n) 1 (coordinateOneClass n i) =
      coordinateH1Functional n i := by
  apply LinearMap.ext
  intro a
  obtain ⟨p, rfl⟩ := loopHomologyClass_surjective (0 : ProductTorus n) a
  exact coordinateOneClass_evaluation_loop n i p

/-- Positive coordinate periods are the integral normalization of these actual classes. -/
@[simp] theorem coordinateOneClass_periodLoop (n : ℕ) (i : Fin n)
    (v : Fin n → ℤ) :
    singularEvaluation (ProductTorus n) 1 (coordinateOneClass n i)
      (loopHomologyClass (coordinatePeriodLoop n v)) = v i := by
  rw [coordinateOneClass_evaluation, coordinateH1Functional_periodLoop]

/-- Pullback of the literal coordinate one-cochain to the original period torus. -/
def periodOneCochain (p : PeriodDomain) (i : Fin 4) : Chains p.Torus 1 →ₗ[ℤ] ℤ :=
  (coordinateOneCochain 4 i).comp
    (inducedChain (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 1)

theorem periodOneCochain_boundaryTwo (p : PeriodDomain) (i : Fin 4)
    (c : Chains p.Torus 2) : periodOneCochain p i (boundaryTwo p.Torus c) = 0 := by
  change coordinateOneCochain 4 i
    (inducedChain (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 1
      (boundaryTwo p.Torus c)) = 0
  rw [inducedChain_boundaryTwo, coordinateOneCochain_boundaryTwo]

theorem periodOneCochain_closed (p : PeriodDomain) (i : Fin 4) :
    ((singularCochainComplex p.Torus).d 1 2).hom (periodOneCochain p i) = 0 :=
  LinearMap.ext (periodOneCochain_boundaryTwo p i)

/-- The original period loop has its literal marked integral coordinate. -/
@[simp] theorem periodOneCochain_periodLoop (p : PeriodDomain) (i : Fin 4) (v : Lattice) :
    periodOneCochain p i (simplexChain p.Torus 1 (pathSimplex (p.periodLoop v))) = v i := by
  have he : (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)).comp
      (pathSimplex (p.periodLoop v)) =
      pathSimplex (coordinatePeriodLoop 4 v) := by
    rw [← pathSimplex_map, periodTorusCircleHomeomorph_periodLoop]
    rfl
  change coordinateOneCochain 4 i
    (inducedChain (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 1
      (simplexChain p.Torus 1 (pathSimplex (p.periodLoop v)))) = v i
  rw [inducedChain_simplex, he, coordinateOneCochain_periodLoop]

/-- The representative on the actual period torus is a native cocycle. -/
def periodOneCocycle (p : PeriodDomain) (i : Fin 4) :
    Cocycle (singularCochainComplex p.Torus) 1 :=
  mkCocycle _ 1 (periodOneCochain p i) (periodOneCochain_closed p i)

@[simp] theorem periodOneCocycle_val (p : PeriodDomain) (i : Fin 4) :
    (periodOneCocycle p i).val = periodOneCochain p i := rfl

/-- Its actual cohomology class is the literal pullback by the coordinate homeomorphism. -/
def periodOneClass (p : PeriodDomain) (i : Fin 4) : SingularCohomology p.Torus 1 :=
  singularCohomologyPullback (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4)) 1
    (coordinateOneClass 4 i)

theorem periodOneCocycle_pullback (p : PeriodDomain) (i : Fin 4) :
    mapCocycles (singularPullback
      (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4))) 1
      (coordinateOneCocycle 4 i) = periodOneCocycle p i := by
  apply Subtype.ext
  rw [mapCocycles_val, singularPullback_f_apply, coordinateOneCocycle_val,
    periodOneCocycle_val]
  rfl

theorem periodOneClass_eq_cocycleClass (p : PeriodDomain) (i : Fin 4) :
    periodOneClass p i = cocycleClass (singularCochainComplex p.Torus) 1
      (periodOneCocycle p i) := by
  have h := homologyMap_cocycleClass
    (singularPullback (periodTorusCircleHomeomorph p : C(p.Torus, ProductTorus 4))) 1
    (coordinateOneCocycle 4 i)
  exact h.trans (congrArg (cocycleClass (singularCochainComplex p.Torus) 1)
    (periodOneCocycle_pullback p i))

/-- Evaluation on the original period torus preserves the ordered integral marking. -/
@[simp] theorem periodOneClass_periodLoop (p : PeriodDomain) (i : Fin 4) (v : Lattice) :
    singularEvaluation p.Torus 1 (periodOneClass p i)
      (loopHomologyClass (p.periodLoop v)) = v i := by
  rw [periodOneClass, singularEvaluation_naturality, singularHomologyMap_one,
    periodTorusCircle_inducedHomology_periodLoop, coordinateOneClass_periodLoop]

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
