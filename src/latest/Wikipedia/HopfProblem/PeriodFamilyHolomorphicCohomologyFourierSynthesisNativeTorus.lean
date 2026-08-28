import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusTopology
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic

/-!
# The actual standard real torus in unit-circle Fourier coordinates

The existing quotient homeomorphism has exactly the unit additive torus
as its target, with the same coordinate order as the Fourier quotient.
Reusing it gives the literal formula on every real representative,
continuity, and bijectivity without any additional quotient or atlas.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative

open PeriodTorusLineBundleClassification

/-- The genuine quotient homeomorphism to the product of four unit additive circles. -/
def unitTorusMarkHomeomorph : RealTorus₄ ≃ₜ UnitAddTorus (Fin 4) :=
  PeriodTorusHigherHomology.flatTorusCircleHomeomorph

/-- The original standard lattice quotient in the actual unit-torus Fourier marking. -/
def unitTorusMark : RealTorus₄ → UnitAddTorus (Fin 4) := unitTorusMarkHomeomorph

@[simp] theorem unitTorusMark_mkQ (x : RealPlane₄) :
    unitTorusMark (standardLattice.mkQ x) = torusQuotient x := rfl

theorem unitTorusMark_continuous : Continuous unitTorusMark :=
  unitTorusMarkHomeomorph.continuous

theorem unitTorusMark_injective : Function.Injective unitTorusMark :=
  unitTorusMarkHomeomorph.injective

theorem unitTorusMark_surjective : Function.Surjective unitTorusMark :=
  unitTorusMarkHomeomorph.surjective

@[simp] theorem unitTorusMark_zero : unitTorusMark 0 = 0 :=
  PeriodTorusHigherHomology.flatTorusCircleMap.map_zero

@[simp] theorem unitTorusMark_add (x y : RealTorus₄) :
    unitTorusMark (x + y) = unitTorusMark x + unitTorusMark y :=
  PeriodTorusHigherHomology.flatTorusCircleMap.map_add x y

/-- The inverse marking returns the original lattice class of every real representative. -/
@[simp] theorem unitTorusMarkHomeomorph_symm_quotient (x : RealPlane₄) :
    unitTorusMarkHomeomorph.symm (torusQuotient x) = standardLattice.mkQ x :=
  unitTorusMarkHomeomorph.symm_apply_apply (standardLattice.mkQ x)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisNative
