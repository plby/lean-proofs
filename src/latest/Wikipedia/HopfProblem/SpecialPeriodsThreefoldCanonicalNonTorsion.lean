import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersSquare
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersNegative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersVanishingCriterion

/-!
# Pluricanonical vanishing and non-torsion for the actual compact threefold

The genuine canonical square comparison and the proved vanishing of
every positive power of the pulled-back sphere ideal line imply that
every positive pluricanonical section is zero.  The powers here have
their actual full intrinsic tensor-fibre identifications.  Every
positive holomorphic fibre-linear trivialization is consequently
impossible, so the actual canonical bundle is non-torsion.

The proof uses the compact scalar maximum principle and the explicit
bundle comparisons.  It assumes neither relative duality nor a
canonical pushforward theorem, and does not infer non-torsion merely
from vanishing in the first degree.
-/

noncomputable section

open Bundle
open scoped ContDiff OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- Every positive pluricanonical section of the actual threefold is zero. -/
theorem pluricanonicalSection_eq_zero (n : ℕ) (hn : 0 < n) (s : HolomorphicSections n) : s = 0 :=
  CanonicalGlobalLineBundle.Powers.section_eq_zero_of_square_comparison
    (A := canonicalData) (B := baseData) canonicalSquareGauge
    (fun m hm t => PowersNegative.section_eq_zero m hm t) n hn s

/-- The assertion concerns the whole genuine native section space. -/
theorem pluricanonicalSection_subsingleton (n : ℕ) (hn : 0 < n) :
    Subsingleton (HolomorphicSections n) :=
  ⟨fun s t => (pluricanonicalSection_eq_zero n hn s).trans
    (pluricanonicalSection_eq_zero n hn t).symm⟩

/-- All positive plurigenera of the actual native canonical bundle vanish. -/
theorem plurigenus_eq_zero (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (HolomorphicSections n) = 0 := by
  let := pluricanonicalSection_subsingleton n hn
  exact Module.finrank_zero_of_subsingleton

/-- No positive power admits a genuine holomorphic fibre-linear
trivialization of its original native total space. -/
theorem canonical_power_not_holomorphicallyTrivial (n : ℕ) (hn : 0 < n) :
    ¬ HolomorphicallyTrivial IF (canonicalData.power n) := by
  let : Nonempty Threefold.Space :=
    ⟨(Threefold.projectionSphere_surjective (∞ : RiemannSphere)).choose⟩
  exact not_holomorphicallyTrivial_of_sections_zero IF (canonicalData.power n)
    (pluricanonicalSection_eq_zero n hn)

/-- The actual canonical bundle has no positive finite holomorphic
tensor order.  This uses the proved vanishing in every positive degree. -/
theorem canonical_not_torsion :
    ¬ ∃ n : ℕ, 0 < n ∧ HolomorphicallyTrivial IF (canonicalData.power n) := by
  rintro ⟨n, hn, htriv⟩
  exact canonical_power_not_holomorphicallyTrivial n hn htriv

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Powers
