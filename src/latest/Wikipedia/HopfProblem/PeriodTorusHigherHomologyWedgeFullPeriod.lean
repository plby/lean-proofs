import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeThree
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsFullPeriod

/-!
# Marked wedge maps for arbitrary full period tori

The coordinate order is the original `(m₀,m₁,n₀,n₁)` order. The marking of
actual first singular homology comes from the actual straight period loops.
The proved all-degree homology calculation supplies torsion freeness, so the
actual second and third Pontryagin products factor through the corresponding
exterior powers without an additional hypothesis on the period matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris FirstHurewicz PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The positive actual first-homology marking in the ordered four integral coordinates. -/
def fullPeriodCoordinateH1 (q : FullPeriodMatrix) :
    Lattice →ₗ[ℤ] SingularHomology q.Torus 1 :=
  q.singularH1Equiv.symm.toLinearMap.comp
    FullPeriodMatrix.integerCoordinatesEquiv.symm.toLinearMap

@[simp] theorem fullPeriodCoordinateH1_apply (q : FullPeriodMatrix) (v : Lattice) :
    fullPeriodCoordinateH1 q v =
      q.singularH1Equiv.symm (FullPeriodMatrix.integerCoordinatesEquiv.symm v) := rfl

/-- The marked class is represented by the actual positive straight loop. -/
theorem fullPeriodCoordinateH1_periodLoop (q : FullPeriodMatrix) (v : Lattice) :
    fullPeriodCoordinateH1 q v =
      loopHomologyClass (q.periodLoop (FullPeriodMatrix.integerCoordinatesEquiv.symm v)) := by
  rw [fullPeriodCoordinateH1_apply, q.singularH1Equiv_symm_apply]

theorem fullPeriodCoordinateH1_bijective (q : FullPeriodMatrix) :
    Function.Bijective (fullPeriodCoordinateH1 q) :=
  q.singularH1Equiv.symm.bijective.comp FullPeriodMatrix.integerCoordinatesEquiv.symm.bijective

theorem fullPeriodCoordinateH1_injective (q : FullPeriodMatrix) :
    Function.Injective (fullPeriodCoordinateH1 q) :=
  (fullPeriodCoordinateH1_bijective q).1

theorem fullPeriodCoordinateH1_surjective (q : FullPeriodMatrix) :
    Function.Surjective (fullPeriodCoordinateH1 q) :=
  (fullPeriodCoordinateH1_bijective q).2

/-- The genuine coordinate homeomorphism preserves precisely the marked positive loop class. -/
theorem fullPeriodCoordinateH1_productTorusHomeomorph (q : FullPeriodMatrix) (v : Lattice) :
    singularHomologyMap (q.productTorusHomeomorph : C(q.Torus, ProductTorus 4)) 1
        (fullPeriodCoordinateH1 q v) =
      loopHomologyClass (coordinatePeriodLoop 4 v) := by
  rw [singularHomologyMap_one, fullPeriodCoordinateH1_apply,
    q.productTorusHomeomorph_inducedHomology_singularH1Equiv, LinearEquiv.apply_symm_apply]

/-- Torsion freeness is already proved from the actual full-period coordinate homeomorphism. -/
theorem fullPeriodTorus_homology_torsionFree (q : FullPeriodMatrix) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology q.Torus n) :=
  q.singularHomology_torsionFree n

/-- The actual marked exterior-square map for every full period torus. -/
def fullPeriodTorusWedgeTwo (q : FullPeriodMatrix) :
    (⋀[ℤ]^2 Lattice) →ₗ[ℤ] SingularHomology q.Torus 2 := by
  letI := fullPeriodTorus_homology_torsionFree q 2
  exact latticeWedgeTwo q.Torus (fullPeriodCoordinateH1 q)

/-- The actual marked exterior-cube map for every full period torus. -/
def fullPeriodTorusWedgeThree (q : FullPeriodMatrix) :
    (⋀[ℤ]^3 Lattice) →ₗ[ℤ] SingularHomology q.Torus 3 := by
  letI := fullPeriodTorus_homology_torsionFree q 2
  exact latticeWedgeThree q.Torus (fullPeriodCoordinateH1 q)

theorem fullPeriodTorusWedgeTwo_eq (q : FullPeriodMatrix) :
    letI := fullPeriodTorus_homology_torsionFree q 2
    fullPeriodTorusWedgeTwo q = latticeWedgeTwo q.Torus (fullPeriodCoordinateH1 q) := rfl

theorem fullPeriodTorusWedgeThree_eq (q : FullPeriodMatrix) :
    letI := fullPeriodTorus_homology_torsionFree q 2
    fullPeriodTorusWedgeThree q = latticeWedgeThree q.Torus (fullPeriodCoordinateH1 q) := rfl

@[simp] theorem fullPeriodTorusWedgeTwo_apply_ιMulti (q : FullPeriodMatrix)
    (v : Fin 2 → Lattice) :
    fullPeriodTorusWedgeTwo q (exteriorPower.ιMulti ℤ 2 v) =
      product11 q.Torus (fullPeriodCoordinateH1 q (v 0)) (fullPeriodCoordinateH1 q (v 1)) := by
  let := fullPeriodTorus_homology_torsionFree q 2
  exact latticeWedgeTwo_apply_ιMulti q.Torus (fullPeriodCoordinateH1 q) v

@[simp] theorem fullPeriodTorusWedgeThree_apply_ιMulti (q : FullPeriodMatrix)
    (v : Fin 3 → Lattice) :
    fullPeriodTorusWedgeThree q (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct q.Torus (fullPeriodCoordinateH1 q (v 0))
        (fullPeriodCoordinateH1 q (v 1)) (fullPeriodCoordinateH1 q (v 2)) := by
  let := fullPeriodTorus_homology_torsionFree q 2
  exact latticeWedgeThree_apply_ιMulti q.Torus (fullPeriodCoordinateH1 q) v

theorem fullPeriodTorusWedgeTwo_apply_ιMulti_periodLoops (q : FullPeriodMatrix)
    (v : Fin 2 → Lattice) :
    fullPeriodTorusWedgeTwo q (exteriorPower.ιMulti ℤ 2 v) =
      product11 q.Torus
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 0))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 1)))) := by
  rw [fullPeriodTorusWedgeTwo_apply_ιMulti, fullPeriodCoordinateH1_periodLoop,
    fullPeriodCoordinateH1_periodLoop]

theorem fullPeriodTorusWedgeThree_apply_ιMulti_periodLoops (q : FullPeriodMatrix)
    (v : Fin 3 → Lattice) :
    fullPeriodTorusWedgeThree q (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct q.Torus
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 0))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 1))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 2)))) := by
  rw [fullPeriodTorusWedgeThree_apply_ιMulti, fullPeriodCoordinateH1_periodLoop,
    fullPeriodCoordinateH1_periodLoop, fullPeriodCoordinateH1_periodLoop]

/-- Degree-two naturality for an actual additive map with a proved marked degree-one action. -/
theorem fullPeriodTorusWedgeTwo_natural (q r : FullPeriodMatrix) (f : C(q.Torus, r.Torus))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v : Lattice, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v)) :
    (singularHomologyMap f 2).comp (fullPeriodTorusWedgeTwo q) =
      (fullPeriodTorusWedgeTwo r).comp (exteriorPower.map 2 A) := by
  let := fullPeriodTorus_homology_torsionFree q 2
  let := fullPeriodTorus_homology_torsionFree r 2
  exact latticeWedgeTwo_natural f hf (fullPeriodCoordinateH1 q) (fullPeriodCoordinateH1 r)
    A hmark

/-- Degree-three naturality for the same actual marked group map. -/
theorem fullPeriodTorusWedgeThree_natural (q r : FullPeriodMatrix) (f : C(q.Torus, r.Torus))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v : Lattice, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v)) :
    (singularHomologyMap f 3).comp (fullPeriodTorusWedgeThree q) =
      (fullPeriodTorusWedgeThree r).comp (exteriorPower.map 3 A) := by
  let := fullPeriodTorus_homology_torsionFree q 2
  let := fullPeriodTorus_homology_torsionFree r 2
  exact latticeWedgeThree_natural f hf (fullPeriodCoordinateH1 q) (fullPeriodCoordinateH1 r)
    A hmark

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
