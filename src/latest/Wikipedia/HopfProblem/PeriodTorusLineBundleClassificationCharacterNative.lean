import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterGauge
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCharacterGaugeIso

/-!
# Native bundle normalization of a constant lattice character

The constructed exponential gauge induces an actual analytic, fibrewise
complex-linear isomorphism between the original native line bundles.
The source factor has zero Hermitian form and a genuinely unitary character.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

variable {p : PeriodDomain}

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

theorem unitaryCharacterFactor_norm (ρ : LatticeCharacter p) (l : p.lattice)
    (z : ComplexPlane₂) :
    ‖((constantCharacterFactor (unitaryCharacter ρ)).factor l z : ℂ)‖ = 1 := by
  rw [constantCharacterFactor_coe]
  exact unitaryCharacter_isUnitary ρ l

/-- The actual exponential gauge is a native analytic bundle isomorphism
from the normalized unitary character to the original character. -/
def characterNormalizationBundleIso (ρ : LatticeCharacter p) :
    AnalyticBundleIso IC
      (Core.data (constantCharacterFactor (unitaryCharacter ρ))).core.Fiber
      (Core.data (constantCharacterFactor ρ)).core.Fiber :=
  gaugeBundleIso (constantCharacterFactor (unitaryCharacter ρ))
    (constantCharacterFactor ρ) (characterGauge ρ) (characterGauge_holomorphic ρ)
    (characterGauge_ne_zero ρ) (characterGauge_factor_relation ρ)

/-- On actual quotient representatives the native map is multiplication by
the explicit exponential, with the positive-translation sign convention. -/
theorem characterNormalizationBundleIso_associatedMap (ρ : LatticeCharacter p)
    (z : ComplexPlane₂) (c : ℂ) :
    Core.toAssociated (constantCharacterFactor ρ)
      ((characterNormalizationBundleIso ρ).diffeomorph
        (Core.fromAssociated (constantCharacterFactor (unitaryCharacter ρ))
          (associatedMap (constantCharacterFactor (unitaryCharacter ρ)) (z, c)))) =
      associatedMap (constantCharacterFactor ρ)
        (z, Complex.exp (characterLinear ρ z) * c) :=
  gaugeBundleIso_associatedMap _ _ _ _ _ _ z c

/-- The original character bundle is analytically isomorphic to its
canonical unitary normalization, on the original native total spaces. -/
def originalCharacterToUnitaryBundleIso (ρ : LatticeCharacter p) :
    AnalyticBundleIso IC
      (Core.data (constantCharacterFactor ρ)).core.Fiber
      (Core.data (constantCharacterFactor (unitaryCharacter ρ))).core.Fiber :=
  (characterNormalizationBundleIso ρ).symm

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
