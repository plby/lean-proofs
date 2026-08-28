import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeTwo
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusHomomorphisms
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyMonodromy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorBasis

/-!
# The marked exterior-square map for actual period tori

The exterior-square map uses the proved positive-period-loop marking of actual
first singular homology. The needed torsion freeness of actual second homology
is a proved theorem of the period tori. Its naturality under all three genuine
period changes follows from their proved additive and first-homology formulas.
No claim that the exterior-square map is an isomorphism is made here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris FirstHurewicz
open PeriodTorusHigherHomologyPontryagin PeriodTorusHigherHomologyExterior
open LocalSystemMatrices

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual exterior-square map into the actual second singular homology of a period torus. -/
def periodTorusWedgeTwo (p : PeriodDomain) :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularHomology p.Torus 2 := by
  letI := periodTorus_homology_torsionFree p 2
  exact latticeWedgeTwo p.Torus p.singularH1Equiv.symm.toLinearMap

@[simp] theorem periodTorusWedgeTwo_apply_ιMulti (p : PeriodDomain) (v : Fin 2 → Lattice) :
    periodTorusWedgeTwo p (exteriorPower.ιMulti ℤ 2 v) =
      product11 p.Torus (p.singularH1Equiv.symm (v 0)) (p.singularH1Equiv.symm (v 1)) := by
  let := periodTorus_homology_torsionFree p 2
  exact latticeWedgeTwo_apply_ιMulti p.Torus p.singularH1Equiv.symm.toLinearMap v

/-- The marking is given by the actual positively oriented straight period loops. -/
theorem periodTorusWedgeTwo_apply_ιMulti_periodLoops (p : PeriodDomain) (v : Fin 2 → Lattice) :
    periodTorusWedgeTwo p (exteriorPower.ιMulti ℤ 2 v) =
      product11 p.Torus (loopHomologyClass (p.periodLoop (v 0)))
        (loopHomologyClass (p.periodLoop (v 1))) := by
  rw [periodTorusWedgeTwo_apply_ιMulti, p.singularH1Equiv_symm_apply,
    p.singularH1Equiv_symm_apply]

/-- On each ordered exterior-square basis vector, the map is the product of the two
corresponding actual period-loop classes. -/
theorem periodTorusWedgeTwo_squareBasis (p : PeriodDomain) (i : Fin 6) :
    periodTorusWedgeTwo p (squareBasis i) =
      product11 p.Torus
        (loopHomologyClass (p.periodLoop (latticeBasis (pairIndices i 0))))
        (loopHomologyClass (p.periodLoop (latticeBasis (pairIndices i 1)))) := by
  rw [squareBasis_apply, periodTorusWedgeTwo_apply_ιMulti_periodLoops]
  rfl

/-- Marked naturality for an actual continuous additive map of period tori. -/
theorem periodTorusWedgeTwo_natural (p q : PeriodDomain) (f : C(p.Torus, q.Torus))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v : Lattice, singularHomologyMap f 1 (p.singularH1Equiv.symm v) =
      q.singularH1Equiv.symm (A v)) :
    (singularHomologyMap f 2).comp (periodTorusWedgeTwo p) =
      (periodTorusWedgeTwo q).comp (exteriorPower.map 2 A) := by
  let := periodTorus_homology_torsionFree p 2
  let := periodTorus_homology_torsionFree q 2
  exact latticeWedgeTwo_natural f hf p.singularH1Equiv.symm.toLinearMap
    q.singularH1Equiv.symm.toLinearMap A hmark

/-- The first actual period change on the positive degree-one marking. -/
theorem periodTorusH1_marking_step₁ (p : PeriodDomain) (v : Lattice) :
    singularHomologyMap p.step₁ContinuousMap 1 (p.singularH1Equiv.symm v) =
      p.step₁.singularH1Equiv.symm (A₁.mulVecLin v) := by
  change inducedHomology p.step₁ContinuousMap (p.singularH1Equiv.symm v) =
    p.step₁.singularH1Equiv.symm (A₁ *ᵥ v)
  rw [p.singularH1Equiv_symm_apply, p.step₁.singularH1Equiv_symm_apply]
  exact p.step₁_inducedHomology_periodLoop v

/-- The second actual period change on the positive degree-one marking. -/
theorem periodTorusH1_marking_step₂ (p : PeriodDomain) (v : Lattice) :
    singularHomologyMap p.step₂ContinuousMap 1 (p.singularH1Equiv.symm v) =
      p.step₂.singularH1Equiv.symm (A₂.mulVecLin v) := by
  change inducedHomology p.step₂ContinuousMap (p.singularH1Equiv.symm v) =
    p.step₂.singularH1Equiv.symm (A₂ *ᵥ v)
  rw [p.singularH1Equiv_symm_apply, p.step₂.singularH1Equiv_symm_apply]
  exact p.step₂_inducedHomology_periodLoop v

/-- The actual cusp change on the positive degree-one marking. -/
theorem periodTorusH1_marking_step₀ (p : PeriodDomain) (v : Lattice) :
    singularHomologyMap p.step₀ContinuousMap 1 (p.singularH1Equiv.symm v) =
      p.step₀.singularH1Equiv.symm (M₀.mulVecLin v) := by
  change inducedHomology p.step₀ContinuousMap (p.singularH1Equiv.symm v) =
    p.step₀.singularH1Equiv.symm (M₀ *ᵥ v)
  rw [p.singularH1Equiv_symm_apply, p.step₀.singularH1Equiv_symm_apply]
  exact p.step₀_inducedHomology_periodLoop v

/-- Naturality under the first actual biholomorphism, with its proved lattice matrix. -/
theorem periodTorusWedgeTwo_step₁ (p : PeriodDomain) :
    (singularHomologyMap p.step₁ContinuousMap 2).comp (periodTorusWedgeTwo p) =
      (periodTorusWedgeTwo p.step₁).comp (exteriorPower.map 2 A₁.mulVecLin) :=
  periodTorusWedgeTwo_natural p p.step₁ p.step₁ContinuousMap (step₁ContinuousMap_add p)
    A₁.mulVecLin (periodTorusH1_marking_step₁ p)

/-- Naturality under the second actual biholomorphism, with its proved lattice matrix. -/
theorem periodTorusWedgeTwo_step₂ (p : PeriodDomain) :
    (singularHomologyMap p.step₂ContinuousMap 2).comp (periodTorusWedgeTwo p) =
      (periodTorusWedgeTwo p.step₂).comp (exteriorPower.map 2 A₂.mulVecLin) :=
  periodTorusWedgeTwo_natural p p.step₂ p.step₂ContinuousMap (step₂ContinuousMap_add p)
    A₂.mulVecLin (periodTorusH1_marking_step₂ p)

/-- Naturality under the actual cusp biholomorphism, with its proved lattice matrix. -/
theorem periodTorusWedgeTwo_step₀ (p : PeriodDomain) :
    (singularHomologyMap p.step₀ContinuousMap 2).comp (periodTorusWedgeTwo p) =
      (periodTorusWedgeTwo p.step₀).comp (exteriorPower.map 2 M₀.mulVecLin) :=
  periodTorusWedgeTwo_natural p p.step₀ p.step₀ContinuousMap (step₀ContinuousMap_add p)
    M₀.mulVecLin (periodTorusH1_marking_step₀ p)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
