import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenOppositeHalf
import Wikipedia.HopfProblem.DegreeCollapseEqualNativeLevels
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainCollars

/-!
# The actual complementary half has a constructed inward boundary collar

Use the unnegated excellent time to construct its native regular-sublevel
handle chain. The whole body is the literal negative half, and the native
zero atlases are compared by the identity diffeomorphism. Propagating the
actual attachment collars therefore supplies the inward collar required
for handle interchanges on the original opposite body.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

variable {B : Type} [TopologicalSpace B]

def negativeHalfInclusion (S : CollaredSevenState B) : C(S.NegativeHalf, S.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

namespace ExcellentMorsePresentation

variable {S : CollaredSevenState B} (P : S.ExcellentMorsePresentation)

theorem function_nonpositive_iff (p : S.Space) : P.function p ≤ 0 ↔ S.time p ≤ 0 := by
  constructor
  · intro hp
    exact not_lt.mp (fun ht ↦ (not_lt_of_ge hp) ((P.positive_iff p).mpr ht))
  · intro hp
    exact not_lt.mp (fun ht ↦ (not_lt_of_ge hp) ((P.positive_iff p).mp ht))

def negativeSublevelBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model (Vector 7)) :=
  RegularMorseSublevel.body P.smooth 0 (RegularTimeMorse.regular_zero_not_critical P.regular)

def negativeSublevelHomeomorph : P.negativeSublevelBody.body ≃ₜ S.NegativeHalf :=
  (Homeomorph.refl S.Space).subtype
    (p := fun p ↦ P.function p ≤ 0) (q := fun p ↦ S.time p ≤ 0) P.function_nonpositive_iff

def negativeSublevelBodyEquiv :
    SmoothBoundaryBody.Equiv P.negativeSublevelBody P.oppositeHalf.toBody where
  body := P.negativeSublevelHomeomorph
  boundary := MorseCancellation.equalLevelDiffeomorph P.smooth P.sublevelFunction_smooth
    (RegularTimeMorse.regular_zero_not_critical P.regular)
    (RegularTimeMorse.regular_zero_not_critical P.sublevelFunction_regular)
    (fun _ ↦ neg_eq_zero)
  boundary_point _ := Subtype.ext rfl

theorem oppositeHalf_hasInwardCollar : P.oppositeHalf.toBody.HasInwardCollar := by
  obtain ⟨_, c, _⟩ := RegularMorseSublevel.exists_fullSmoothHandleChain
    P.smooth P.morse P.distinct 0 (RegularTimeMorse.regular_zero_not_critical P.regular)
  exact SmoothBoundaryBody.hasInwardCollar_transport P.negativeSublevelBodyEquiv
    (c.hasInwardCollar ⟨InwardBoundaryCollar.ofIsEmpty _⟩)

end ExcellentMorsePresentation
end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
