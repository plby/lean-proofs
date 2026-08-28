import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrameCorrection
import Wikipedia.HopfProblem.HolomorphicCharacterBundleCoreTrivialization

/-!
# The actual nonzero holomorphic section and analytic scalar-core trivialization

The corrected coefficients glue using the original transition functions.
They give an actual native `ContMDiffSection`, and the already proved
section-to-product construction gives a genuine fibre-linear analytic
trivialization of the original scalar-core total space.
-/

noncomputable section

open Set Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame

open HolomorphicCharacterBundle PeriodTorusLineBundleClassificationFrame
  PeriodTorusLineBundleClassificationGlobalTransport

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {ι : Type*} (A : TransitionData ComplexPlane₂ ι) [A.IsHolomorphic Iℂ]

/-- The genuine holomorphic section obtained by gluing the corrected actual
local coefficients. It is constructed for every given holomorphic cocycle. -/
def coreHolomorphicSection : ContMDiffSection Iℂ ℂ ω A.core.Fiber :=
  A.holomorphicSectionFromLocal Iℂ (correctedCoefficient A)
    (correctedCoefficient_compatible A)
    (fun i => (correctedCoefficient_contDiffOn_complex A i).contMDiffOn)

@[simp] theorem coreHolomorphicSection_apply (x : ComplexPlane₂) :
    coreHolomorphicSection A x = correctedCoefficient A (A.indexAt x) x := rfl

theorem coreHolomorphicSection_ne_zero (x : ComplexPlane₂) :
    coreHolomorphicSection A x ≠ 0 :=
  correctedCoefficient_ne_zero A (A.indexAt x) x

/-- The constructed holomorphic section is literally the negative
exponential correction of the previously constructed smooth section. -/
theorem coreHolomorphicSection_eq_correction (x : ComplexPlane₂) :
    coreHolomorphicSection A x = correctionFactor A x • coreFrame A x := by
  change correctedCoefficient A (A.indexAt x) x =
    correctionFactor A x * globalRadialScalar A x
  rw [correctedCoefficient, frameCoefficient_indexAt]

/-- The corrected coefficients are read in the existing original charts. -/
theorem coreHolomorphicSection_localCoefficient (i : ι) {x : ComplexPlane₂}
    (hx : x ∈ A.baseSet i) :
    A.localCoefficient (coreHolomorphicSection A) i x = correctedCoefficient A i x :=
  A.localCoefficient_sectionFromLocal (correctedCoefficient A)
    (correctedCoefficient_compatible A) i hx

/-- An actual fibre-linear analytic total-space trivialization, obtained
from the constructed holomorphic nonzero section. -/
def coreAnalyticTrivialization : A.AnalyticTrivialization Iℂ :=
  A.analyticTrivializationOfSection (coreHolomorphicSection A) Iℂ
    (coreHolomorphicSection A).contMDiff (coreHolomorphicSection_ne_zero A)

theorem exists_core_holomorphic_nonzero_section :
    ∃ s : ContMDiffSection Iℂ ℂ ω A.core.Fiber, ∀ x, s x ≠ 0 :=
  ⟨coreHolomorphicSection A, coreHolomorphicSection_ne_zero A⟩

theorem nonempty_core_analyticTrivialization : Nonempty (A.AnalyticTrivialization Iℂ) :=
  ⟨coreAnalyticTrivialization A⟩

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationHolomorphicFrame
