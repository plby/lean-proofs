import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeThree
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgePeriodTwo

/-!
# The marked exterior-cube map for actual period tori

The alternating triple Pontryagin product uses the actual positive period-loop
marking. Its torsion-free input is supplied by the proved actual degree-two
homology theorem, and its naturality is instantiated at each actual period change.
No isomorphism is asserted in this file.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomologyPontryagin
open PeriodTorusHigherHomologyExterior LocalSystemMatrices

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The exterior cube of the positive period-loop marking maps to actual third singular homology. -/
def periodTorusWedgeThree (p : PeriodDomain) :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularHomology p.Torus 3 := by
  letI := periodTorus_homology_torsionFree p 2
  exact latticeWedgeThree p.Torus p.singularH1Equiv.symm.toLinearMap

@[simp] theorem periodTorusWedgeThree_apply_ιMulti (p : PeriodDomain) (v : Fin 3 → Lattice) :
    periodTorusWedgeThree p (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct p.Torus (p.singularH1Equiv.symm (v 0))
        (p.singularH1Equiv.symm (v 1)) (p.singularH1Equiv.symm (v 2)) := by
  let := periodTorus_homology_torsionFree p 2
  exact latticeWedgeThree_apply_ιMulti p.Torus p.singularH1Equiv.symm.toLinearMap v

theorem periodTorusWedgeThree_apply_ιMulti_periodLoops (p : PeriodDomain) (v : Fin 3 → Lattice) :
    periodTorusWedgeThree p (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct p.Torus
        (loopHomologyClass (p.periodLoop (v 0)))
        (loopHomologyClass (p.periodLoop (v 1)))
        (loopHomologyClass (p.periodLoop (v 2))) := by
  let := periodTorus_homology_torsionFree p 2
  change latticeWedgeThree p.Torus p.singularH1Equiv.symm.toLinearMap
    (exteriorPower.ιMulti ℤ 3 v) = _
  rw [latticeWedgeThree_apply_ιMulti]
  simp only [LinearEquiv.coe_coe, p.singularH1Equiv_symm_apply]

/-- Ordered basis vectors give products of the three indicated actual positive period loops. -/
theorem periodTorusWedgeThree_cubeBasis (p : PeriodDomain) (i : Fin 4) :
    periodTorusWedgeThree p (cubeBasis i) =
      tripleProduct p.Torus
        (loopHomologyClass (p.periodLoop (latticeBasis (tripleIndices i 0))))
        (loopHomologyClass (p.periodLoop (latticeBasis (tripleIndices i 1))))
        (loopHomologyClass (p.periodLoop (latticeBasis (tripleIndices i 2)))) := by
  rw [cubeBasis_apply, periodTorusWedgeThree_apply_ιMulti_periodLoops]
  rfl

/-- Naturality for an actual additive map and its proved action on marked first homology. -/
theorem periodTorusWedgeThree_natural (p q : PeriodDomain) (f : C(p.Torus, q.Torus))
    (hfadd : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (p.singularH1Equiv.symm v) =
      q.singularH1Equiv.symm (A v)) :
    (singularHomologyMap f 3).comp (periodTorusWedgeThree p) =
      (periodTorusWedgeThree q).comp (exteriorPower.map 3 A) := by
  let := periodTorus_homology_torsionFree p 2
  let := periodTorus_homology_torsionFree q 2
  exact latticeWedgeThree_natural f hfadd p.singularH1Equiv.symm.toLinearMap
    q.singularH1Equiv.symm.toLinearMap A hmark

/-- The first genuine period change intertwines the cube map
with the actual exterior action of `A₁`. -/
theorem periodTorusWedgeThree_step₁ (p : PeriodDomain) :
    (singularHomologyMap p.step₁ContinuousMap 3).comp (periodTorusWedgeThree p) =
      (periodTorusWedgeThree p.step₁).comp (exteriorPower.map 3 A₁.mulVecLin) := by
  apply periodTorusWedgeThree_natural p p.step₁ p.step₁ContinuousMap
    (step₁ContinuousMap_add p) A₁.mulVecLin
  intro v
  simpa only [singularHomologyMap_one, p.singularH1Equiv_symm_apply,
    p.step₁.singularH1Equiv_symm_apply, Matrix.mulVecLin_apply] using
    p.step₁_inducedHomology_periodLoop v

/-- The second genuine period change gives the exterior action of A₂. -/
theorem periodTorusWedgeThree_step₂ (p : PeriodDomain) :
    (singularHomologyMap p.step₂ContinuousMap 3).comp (periodTorusWedgeThree p) =
      (periodTorusWedgeThree p.step₂).comp (exteriorPower.map 3 A₂.mulVecLin) := by
  apply periodTorusWedgeThree_natural p p.step₂ p.step₂ContinuousMap
    (step₂ContinuousMap_add p) A₂.mulVecLin
  intro v
  simpa only [singularHomologyMap_one, p.singularH1Equiv_symm_apply,
    p.step₂.singularH1Equiv_symm_apply, Matrix.mulVecLin_apply] using
    p.step₂_inducedHomology_periodLoop v

/-- The genuine cusp period change gives the exterior action of M₀. -/
theorem periodTorusWedgeThree_step₀ (p : PeriodDomain) :
    (singularHomologyMap p.step₀ContinuousMap 3).comp (periodTorusWedgeThree p) =
      (periodTorusWedgeThree p.step₀).comp (exteriorPower.map 3 M₀.mulVecLin) := by
  apply periodTorusWedgeThree_natural p p.step₀ p.step₀ContinuousMap
    (step₀ContinuousMap_add p) M₀.mulVecLin
  intro v
  simpa only [singularHomologyMap_one, p.singularH1Equiv_symm_apply,
    p.step₀.singularH1Equiv_symm_apply, Matrix.mulVecLin_apply] using
    p.step₀_inducedHomology_periodLoop v


end Wikipedia.HopfProblem.PeriodTorusHigherHomology
