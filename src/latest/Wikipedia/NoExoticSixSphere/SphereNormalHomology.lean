import Wikipedia.NoExoticSixSphere.ModHomologyHomotopyEquiv
import Wikipedia.NoExoticSixSphere.ZeroProductHomotopy
import Wikipedia.NoExoticSixSphere.Definitions
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere

/-!
# The actual middle homology of the sphere normal-product model

Projection to the sphere is a genuine homotopy equivalence with the
specified zero section as inverse. Its native homology map followed by
the original sphere marking identifies the middle homology with mod-two
coefficients. The original zero-section class is its unique nonzero class.
-/

noncomputable section

open ContinuousMap
open Wikipedia.HopfProblem.SphereHomologyCoefficients

namespace NoExoticSixSphere.SphereNormalHomology

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The specified zero section, not an unspecified homotopy inverse. -/
def zeroSection : C(Sphere 3, Sphere 3 × E) :=
  (ContinuousMap.id (Sphere 3)).prodMk (ContinuousMap.const (Sphere 3) (0 : E))

/-- The original projection contracts only the normal coordinate. -/
def projectionEquiv : (Sphere 3 × E) ≃ₕ Sphere 3 :=
  (Homeomorph.prodComm (Sphere 3) E).toHomotopyEquiv.trans
    (ZeroProduct.homotopyEquiv E (Sphere 3))

theorem projectionEquiv_forward : (projectionEquiv E).toFun = ContinuousMap.fst := rfl

theorem projectionEquiv_inverse : (projectionEquiv E).invFun = zeroSection E := rfl

/-- Native homology projection to the actual sphere. -/
def projectionHomologyEquiv : ModHomology 2 (Sphere 3 × E) 3 ≃ₗ[ℤ]
    ModHomology 2 (Sphere 3) 3 := modHomologyHomotopyEquiv 2 (projectionEquiv E) 3

theorem projectionHomologyEquiv_apply (a : ModHomology 2 (Sphere 3 × E) 3) :
    projectionHomologyEquiv E a = modHomologyMap 2 ContinuousMap.fst 3 a := rfl

theorem projectionHomologyEquiv_symm_apply (a : ModHomology 2 (Sphere 3) 3) :
    (projectionHomologyEquiv E).symm a = modHomologyMap 2 (zeroSection E) 3 a := rfl

/-- The original product projection followed by the original sphere top marking. -/
def marking : ModHomology 2 (Sphere 3 × E) 3 ≃ₗ[ℤ] ZMod 2 :=
  (projectionHomologyEquiv E).trans (unitSphereModHomologyTopEquiv 2 (by decide) 2)

/-- The image of the original sphere fundamental class along the actual zero section. -/
def zeroSectionClass : ModHomology 2 (Sphere 3 × E) 3 :=
  modHomologyMap 2 (zeroSection E) 3 (unitSphereModTopClass 2 2)

theorem marking_zeroSectionClass : marking E (zeroSectionClass E) = 1 := by
  change unitSphereModHomologyTopEquiv 2 (by decide) 2
    (projectionHomologyEquiv E ((projectionHomologyEquiv E).symm _)) = 1
  rw [LinearEquiv.apply_symm_apply]
  exact unitSphereModHomologyTopEquiv_topClass 2 (by decide) 2

theorem zeroSectionClass_ne_zero : zeroSectionClass E ≠ 0 := by
  intro he
  exact one_ne_zero ((marking_zeroSectionClass E).symm.trans
    ((congrArg (marking E) he).trans (marking E).map_zero))

/-- In this actual product homology, the zero-section class is the only nonzero element. -/
theorem eq_zeroSectionClass_of_ne_zero (a : ModHomology 2 (Sphere 3 × E) 3) (ha : a ≠ 0) :
    a = zeroSectionClass E := by
  have hn : marking E a ≠ 0 := by
    intro he
    exact ha ((marking E).injective (he.trans (marking E).map_zero.symm))
  have he : marking E a = 1 := by
    rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (marking E a) with h | h
    · exact (hn h).elim
    · exact h
  exact (marking E).injective (he.trans (marking_zeroSectionClass E).symm)

end NoExoticSixSphere.SphereNormalHomology
