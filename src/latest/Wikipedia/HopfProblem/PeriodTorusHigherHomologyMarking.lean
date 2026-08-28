import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjective
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Canonical exterior-power markings of actual period-torus homology

The products of actual positive period loops define surjective exterior
maps by the proved coordinate-subtorus basis. The source and target are
finite free integral modules of the same proved rank, so these actual
maps are isomorphisms. Their inverses give the natural exterior-square
and exterior-cube markings used in §7 of `tex/s6.tex`.

No topological comparison, rank, or surjectivity is assumed in the final
markings below. All are supplied by the preceding actual singular-chain,
Mayer--Vietoris, and product constructions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomologyExterior PeriodTorusHigherHomologyPontryagin

/-- The actual period-loop exterior-square map is an integral isomorphism. -/
theorem periodTorusWedgeTwo_bijective (p : PeriodDomain) :
    Function.Bijective (periodTorusWedgeTwo p) := by
  let := periodTorus_homology_free p 2
  let := periodTorus_homology_finite p 2
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (periodTorusWedgeTwo p) (periodTorusWedgeTwo_surjective p)
  rw [latticeExterior_finrank, periodTorus_homology_finrank]

/-- The actual period-loop exterior-cube map is an integral isomorphism. -/
theorem periodTorusWedgeThree_bijective (p : PeriodDomain) :
    Function.Bijective (periodTorusWedgeThree p) := by
  let := periodTorus_homology_free p 3
  let := periodTorus_homology_finite p 3
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (periodTorusWedgeThree p) (periodTorusWedgeThree_surjective p)
  rw [latticeExterior_finrank, periodTorus_homology_finrank]

/-- Exterior products of positive periods, as an equivalence onto actual second homology. -/
def periodTorusWedgeTwoEquiv (p : PeriodDomain) :
    latticeExterior 2 ≃ₗ[ℤ] SingularHomology p.Torus 2 :=
  LinearEquiv.ofBijective (periodTorusWedgeTwo p) (periodTorusWedgeTwo_bijective p)

/-- Exterior products of positive periods, as an equivalence onto actual third homology. -/
def periodTorusWedgeThreeEquiv (p : PeriodDomain) :
    latticeExterior 3 ≃ₗ[ℤ] SingularHomology p.Torus 3 :=
  LinearEquiv.ofBijective (periodTorusWedgeThree p) (periodTorusWedgeThree_bijective p)

@[simp] theorem periodTorusWedgeTwoEquiv_apply (p : PeriodDomain) (v : latticeExterior 2) :
    periodTorusWedgeTwoEquiv p v = periodTorusWedgeTwo p v := rfl

@[simp] theorem periodTorusWedgeThreeEquiv_apply (p : PeriodDomain) (v : latticeExterior 3) :
    periodTorusWedgeThreeEquiv p v = periodTorusWedgeThree p v := rfl

/-- The natural exterior-square marking of actual integral second singular homology. -/
def periodTorusH2ExteriorEquiv (p : PeriodDomain) :
    SingularHomology p.Torus 2 ≃ₗ[ℤ] latticeExterior 2 :=
  (periodTorusWedgeTwoEquiv p).symm

/-- The natural exterior-cube marking of actual integral third singular homology. -/
def periodTorusH3ExteriorEquiv (p : PeriodDomain) :
    SingularHomology p.Torus 3 ≃ₗ[ℤ] latticeExterior 3 :=
  (periodTorusWedgeThreeEquiv p).symm

@[simp] theorem periodTorusH2ExteriorEquiv_wedge (p : PeriodDomain) (v : latticeExterior 2) :
    periodTorusH2ExteriorEquiv p (periodTorusWedgeTwo p v) = v :=
  (periodTorusWedgeTwoEquiv p).symm_apply_apply v

@[simp] theorem periodTorusH3ExteriorEquiv_wedge (p : PeriodDomain) (v : latticeExterior 3) :
    periodTorusH3ExteriorEquiv p (periodTorusWedgeThree p v) = v :=
  (periodTorusWedgeThreeEquiv p).symm_apply_apply v

/-- Inverse marking sends a decomposable exterior vector to the actual period-loop product. -/
theorem periodTorusH2ExteriorEquiv_symm_ιMulti (p : PeriodDomain) (v : Fin 2 → Lattice) :
    (periodTorusH2ExteriorEquiv p).symm (exteriorPower.ιMulti ℤ 2 v) =
      product11 p.Torus (loopHomologyClass (p.periodLoop (v 0)))
        (loopHomologyClass (p.periodLoop (v 1))) :=
  periodTorusWedgeTwo_apply_ιMulti_periodLoops p v

/-- The inverse cubic marking is the actual ordered product of the three positive period loops. -/
theorem periodTorusH3ExteriorEquiv_symm_ιMulti (p : PeriodDomain) (v : Fin 3 → Lattice) :
    (periodTorusH3ExteriorEquiv p).symm (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct p.Torus (loopHomologyClass (p.periodLoop (v 0)))
        (loopHomologyClass (p.periodLoop (v 1))) (loopHomologyClass (p.periodLoop (v 2))) :=
  periodTorusWedgeThree_apply_ιMulti_periodLoops p v

/-- Actual additive maps act on the canonical second-homology marking by the exterior square. -/
theorem periodTorusH2ExteriorEquiv_natural (p q : PeriodDomain) (f : C(p.Torus, q.Torus))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (p.singularH1Equiv.symm v) =
      q.singularH1Equiv.symm (A v)) (a : SingularHomology p.Torus 2) :
    periodTorusH2ExteriorEquiv q (singularHomologyMap f 2 a) =
      exteriorPower.map 2 A (periodTorusH2ExteriorEquiv p a) := by
  obtain ⟨v, rfl⟩ := periodTorusWedgeTwo_surjective p a
  have h := LinearMap.congr_fun (periodTorusWedgeTwo_natural p q f hf A hmark) v
  change singularHomologyMap f 2 (periodTorusWedgeTwo p v) =
    periodTorusWedgeTwo q (exteriorPower.map 2 A v) at h
  rw [h, periodTorusH2ExteriorEquiv_wedge, periodTorusH2ExteriorEquiv_wedge]

/-- Actual additive maps act on the canonical third-homology marking by the exterior cube. -/
theorem periodTorusH3ExteriorEquiv_natural (p q : PeriodDomain) (f : C(p.Torus, q.Torus))
    (hf : ∀ x y, f (x + y) = f x + f y) (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (p.singularH1Equiv.symm v) =
      q.singularH1Equiv.symm (A v)) (a : SingularHomology p.Torus 3) :
    periodTorusH3ExteriorEquiv q (singularHomologyMap f 3 a) =
      exteriorPower.map 3 A (periodTorusH3ExteriorEquiv p a) := by
  obtain ⟨v, rfl⟩ := periodTorusWedgeThree_surjective p a
  have h := LinearMap.congr_fun (periodTorusWedgeThree_natural p q f hf A hmark) v
  change singularHomologyMap f 3 (periodTorusWedgeThree p v) =
    periodTorusWedgeThree q (exteriorPower.map 3 A v) at h
  rw [h, periodTorusH3ExteriorEquiv_wedge, periodTorusH3ExteriorEquiv_wedge]

/-- The natural second-homology marking in the ordered six-minor basis. -/
def periodTorusH2Coordinates (p : PeriodDomain) :
    SingularHomology p.Torus 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (periodTorusH2ExteriorEquiv p).trans squareCoordinates

/-- The natural third-homology marking in the ordered four-minor basis. -/
def periodTorusH3Coordinates (p : PeriodDomain) :
    SingularHomology p.Torus 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (periodTorusH3ExteriorEquiv p).trans cubeCoordinates

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
