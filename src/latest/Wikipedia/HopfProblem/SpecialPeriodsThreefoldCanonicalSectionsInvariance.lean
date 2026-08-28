import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUpstairs
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsIterates
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDerivatives
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsUnit

/-!
# The actual invariant ambient elliptic canonical forms

The explicit period unit corrects the genuine derivative multiplier of
the affine generator.  Hence the weighted native canonical section is
invariant under derivative pullback by every element of the actual cyclic
action, not merely under a scalar action assigned to a formal line.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalSections

open SpecialPeriods TrianglePeriodFamily.Canonical SpecialPeriods.Threefold.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j)

local instance sectionsFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance sectionsFamilyManifold : IsManifold I₃ ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

/-- The native upstairs ambient canonical bundle of the actual family. -/
abbrev upstairsBundle := familyCanonicalBundle D.periods

/-- The source's corrected ambient three-form, with an explicit holomorphic unit. -/
def upstairsSection (x : D.TotalSpace) : (upstairsBundle D).Fiber x :=
  SectionsUpstairs.weightedSection D.periods (SectionsUnit.coefficient D) x

def upstairsSectionMap (x : D.TotalSpace) : (upstairsBundle D).TotalSpace :=
  ⟨x, upstairsSection D x⟩

@[simp] theorem upstairsSectionMap_proj (x : D.TotalSpace) :
    (upstairsSectionMap D x).proj = x := rfl

theorem upstairsSectionMap_holomorphic :
    ContMDiff I₃ ((I₃).prod I₁) ω (upstairsSectionMap D) :=
  SectionsUpstairs.sectionMap_holomorphic D.periods (SectionsUnit.coefficient D)
    (SectionsUnit.coefficient_holomorphic D)

def upstairsHolomorphicSection : ContMDiffSection I₃ ℂ ω (upstairsBundle D).Fiber :=
  SectionsUpstairs.holomorphicSection D.periods (SectionsUnit.coefficient D)
    (SectionsUnit.coefficient_holomorphic D)

@[simp] theorem upstairsHolomorphicSection_apply (x : D.TotalSpace) :
    upstairsHolomorphicSection D x = upstairsSection D x := rfl

theorem upstairsSection_eq_zero_iff (x : D.TotalSpace) :
    upstairsSection D x = 0 ↔ SectionsUnit.vanishingOrder j ≠ 0 ∧ (x.1 : ℂ) = 0 :=
  (SectionsUpstairs.section_eq_zero_iff D.periods (SectionsUnit.coefficient D) x).trans
    (SectionsUnit.coefficient_eq_zero_iff D x.1)

theorem upstairsSection_ne_zero_iff (x : D.TotalSpace) :
    upstairsSection D x ≠ 0 ↔ SectionsUnit.vanishingOrder j = 0 ∨ (x.1 : ℂ) ≠ 0 :=
  (SectionsUpstairs.section_ne_zero_iff D.periods (SectionsUnit.coefficient D) x).trans
    (SectionsUnit.coefficient_ne_zero_iff D x.1)

/-- Invariance under the actual affine generator's native manifold derivative. -/
theorem generator_pullback (v : Lattice) (x : D.TotalSpace) :
    Pullback.pullbackLinear (D.permutation v) x (upstairsSection D (D.permutation v x)) =
      upstairsSection D x := by
  change Pullback.pullbackLinear (D.permutation v) x
      (SectionsUnit.coefficient D (D.permutation v x).1 •
        familyCanonicalVolume D.periods (D.permutation v x)) =
    SectionsUnit.coefficient D x.1 • familyCanonicalVolume D.periods x
  rw [Canonical.permutation_weightedVolume_pullback, SectionsUnit.coefficient_covariance]

/-- All actual cyclic deck transformations preserve the genuine form. -/
theorem action_pullbackLinear (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    Pullback.pullbackLinear (fun y : D.TotalSpace => g • y) x
      (upstairsSection D (g • x)) = upstairsSection D x := by
  let := D.action v hv
  exact SectionsIterates.cyclic_pullbackLinear_invariant (D.permutation v)
    (D.permutation_pow_order v hv) (D.permutation_holomorphic v)
    (upstairsSection D) (generator_pullback D v) g x

/-- Equivalent invariance using the genuine invertible fibre pullback. -/
theorem action_pullbackEquiv (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    Pullback.pullbackEquiv (D.actionBiholomorph v hv g).isLocalDiffeomorph x
      (upstairsSection D (g • x)) = upstairsSection D x :=
  action_pullbackLinear D v hv g x

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.CanonicalSections
