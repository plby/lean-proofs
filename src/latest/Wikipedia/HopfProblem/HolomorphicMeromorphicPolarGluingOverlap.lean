import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarPresentation
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarTransition

/-!
# Native transition sections on actual polar-presentation overlaps

The ratio of two principal polar denominators is the constructed native
holomorphic unit on their literal overlap. Both denominators and numerators
obey the same transition identity. The numerator identity follows from the
unchanged meromorphic fraction germs and cancellation of nonzero denominator
germs, including at points where both denominator values vanish.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]
  {s : Section I M ⊤} (A B : PolarLocal.Presentation I M s)

/-- The first original numerator restricted to the literal overlap. -/
def numeratorLeft : HolomorphicFunctionSheaf.Section I M (A.overlap B) :=
  HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_left A.numerator

/-- The second original numerator restricted to the literal overlap. -/
def numeratorRight : HolomorphicFunctionSheaf.Section I M (A.overlap B) :=
  HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_right B.numerator

/-- The native transition function is the regular representative of the
actual denominator ratio, not total pointwise division of their values. -/
def transitionSection : HolomorphicFunctionSheaf.Section I M (A.overlap B) :=
  PolarTransition.transitionUnit I M (A.denominatorRight B) (A.denominatorLeft B)
    (A.denominatorLeft_ne_zero B) (A.denominators_associated B)

/-- The transition section is nowhere zero on the full original overlap. -/
theorem transitionSection_ne_zero (x : A.overlap B) :
    transitionSection I M A B x ≠ 0 :=
  PolarTransition.transitionUnit_ne_zero I M (A.denominatorRight B) (A.denominatorLeft B)
    (A.denominatorLeft_ne_zero B) (A.denominators_associated B) x

/-- Exact meromorphic germs of the transition, on the literal overlap. -/
theorem transitionSection_germ (x : A.overlap B) :
    sectionGerm I M (A.overlap B) x (transitionSection I M A B) =
      sectionGerm I M (A.overlap B) x (A.denominatorRight B) /
        sectionGerm I M (A.overlap B) x (A.denominatorLeft B) :=
  PolarTransition.transitionUnit_germ I M (A.denominatorRight B) (A.denominatorLeft B)
    (A.denominatorLeft_ne_zero B) (A.denominators_associated B) x

/-- The same exact germ formula in the two original presentation domains. -/
theorem transitionSection_germ_original (x : A.overlap B) :
    sectionGerm I M (A.overlap B) x (transitionSection I M A B) =
      sectionGerm I M B.domain (Set.inclusion inf_le_right x) B.denominator /
        sectionGerm I M A.domain (Set.inclusion inf_le_left x) A.denominator := by
  rw [transitionSection_germ, PolarLocal.Presentation.denominatorRight,
    PolarLocal.Presentation.denominatorLeft, sectionGerm_restrict, sectionGerm_restrict]

/-- Denominators agree by the actual native transition section. -/
theorem transitionSection_mul_denominator :
    transitionSection I M A B * A.denominatorLeft B = A.denominatorRight B :=
  (PolarTransition.transitionUnit_mul I M (A.denominatorRight B) (A.denominatorLeft B)
    (A.denominatorLeft_ne_zero B) (A.denominators_associated B)).symm

private theorem fractions_eq_on_overlap (x : A.overlap B) :
    fraction I M (A.overlap B) (numeratorLeft I M A B) (A.denominatorLeft B) x =
      fraction I M (A.overlap B) (numeratorRight I M A B) (A.denominatorRight B) x := by
  change fraction I M (A.overlap B)
      (HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_left A.numerator)
      (HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_left A.denominator) x =
    fraction I M (A.overlap B)
      (HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_right B.numerator)
      (HolomorphicFunctionSheaf.restrictionAlgHom I M inf_le_right B.denominator) x
  rw [fraction_restrict, fraction_restrict]
  exact (A.fraction_eq (Set.inclusion inf_le_left x)).symm.trans
    (B.fraction_eq (Set.inclusion inf_le_right x))

private theorem numerator_denominator_cross :
    numeratorLeft I M A B * A.denominatorRight B =
      numeratorRight I M A B * A.denominatorLeft B := by
  apply ofHolomorphic_injective I M (A.overlap B)
  apply section_ext
  intro x
  rw [ofHolomorphic_apply, ofHolomorphic_apply]
  exact congrArg (ofHolomorphicGerm I M x.val)
    ((fraction_eq_iff I M (A.overlap B) (numeratorLeft I M A B) (A.denominatorLeft B)
      (numeratorRight I M A B) (A.denominatorRight B) x
      (A.denominatorLeft_ne_zero B x) (A.denominatorRight_ne_zero B x)).mp
        (fractions_eq_on_overlap I M A B x))

/-- The original numerators obey the same transition identity, proved
from their exact meromorphic germs rather than division of point values. -/
theorem transitionSection_mul_numerator :
    transitionSection I M A B * numeratorLeft I M A B = numeratorRight I M A B := by
  apply PolarTransition.section_mul_right_cancel I M (A.denominatorLeft_ne_zero B)
  calc
    (transitionSection I M A B * numeratorLeft I M A B) * A.denominatorLeft B =
        numeratorLeft I M A B * (transitionSection I M A B * A.denominatorLeft B) := by
      ac_rfl
    _ = numeratorLeft I M A B * A.denominatorRight B := by
      rw [transitionSection_mul_denominator]
    _ = numeratorRight I M A B * A.denominatorLeft B :=
      numerator_denominator_cross I M A B

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing
