import Wikipedia.NoExoticSixSphere.PartialFrameIntegerRelations
import Wikipedia.NoExoticSixSphere.IntegerTwistedParity

/-!
# The actual third groups of the five-dimensional two-frame space

The genuine integer relations have the form `(b, -(A a + B b))`, and the
proved image of `A` is `2ℤ`. The residue of `v + B u` therefore has exactly
that relation submodule as kernel and is onto `ℤ/2`. Composing with the
already constructed native presentations computes the actual third singular
homology and native third homotopy groups, without a degree, exactness, or
connectivity hypothesis.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris

variable (v : UnitSphere (Vector 2))

def parityProjection : (ℤ × ℤ) →ₗ[ℤ] ZMod 2 :=
  IntegerTwistedParity.projection (fiberIntegerMap v)

theorem parityProjection_apply (p : ℤ × ℤ) :
    parityProjection v p = ((p.2 + fiberIntegerMap v p.1 : ℤ) : ZMod 2) :=
  IntegerTwistedParity.projection_apply (fiberIntegerMap v) p

theorem parityProjection_surjective : Function.Surjective (parityProjection v) :=
  IntegerTwistedParity.projection_surjective (fiberIntegerMap v)

theorem relationMap_range_eq_parity_kernel :
    LinearMap.range (integerRelationMap v) = LinearMap.ker (parityProjection v) :=
  IntegerTwistedParity.range_eq_kernel (baseIntegerMap v) (fiberIntegerMap v)
    (integerRelationMap v) (integerRelationMap_apply v) (baseIntegerMap_range v)

def integerQuotientParityEquiv : ((ℤ × ℤ) ⧸ integerRelations v) ≃ₗ[ℤ] ZMod 2 :=
  (Submodule.quotEquivOfEq _ _
    ((integerRelations_eq_range v).trans (relationMap_range_eq_parity_kernel v))).trans
      ((parityProjection v).quotKerEquivOfSurjective (parityProjection_surjective v))

def thirdHomologyEquivZModTwo : SingularHomology (Space 5 2) 3 ≃ₗ[ℤ] ZMod 2 :=
  (integerThirdHomologyPresentation v).symm.trans (integerQuotientParityEquiv v)

def thirdHomotopyEquivZModTwo (a : Space 5 2) :
    Additive (HomotopyGroup (Fin 3) (Space 5 2) a) ≃ₗ[ℤ] ZMod 2 :=
  (thirdHomotopyPresentation v a).trans (integerQuotientParityEquiv v)

end NoExoticSixSphere.Stiefel.ColumnHomology
