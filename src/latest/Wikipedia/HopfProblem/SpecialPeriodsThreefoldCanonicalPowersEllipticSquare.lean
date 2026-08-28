import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisor
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor

/-!
# The actual tensor square of the elliptic divisor line and its section

The source bundle is the existing native tensor construction on the
paired original cover.  Its section is the tensor square of the actual
effective-divisor section under the full fibre tensor equivalence.
Its local coefficients are products of the two actual original
coefficients, and its nonzero set is the proved dense complement of S2.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

abbrev SquareIndex := GlobalEllipticDivisor.Index × GlobalEllipticDivisor.Index

/-- The actual paired-cover native tensor bundle, not a formal power label. -/
def squareData : HolomorphicCharacterBundle.TransitionData Threefold.Space SquareIndex :=
  tensor GlobalEllipticDivisor.transitions GlobalEllipticDivisor.transitions

instance squareData_isHolomorphic : squareData.IsHolomorphic IF :=
  tensor_isHolomorphic GlobalEllipticDivisor.transitions GlobalEllipticDivisor.transitions IF

abbrev squareBundle := squareData.core

def squareSection (x : Threefold.Space) : squareBundle.Fiber x :=
  id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) *
    id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x)

/-- The section is exactly the tensor square under the actual full
complex-linear tensor-fibre identification. -/
theorem squareSection_eq_tensor (x : Threefold.Space) :
    squareSection x = fibreTensorEquiv
      GlobalEllipticDivisor.transitions GlobalEllipticDivisor.transitions x
        (GlobalEllipticDivisor.canonicalSection x ⊗ₜ[ℂ]
          GlobalEllipticDivisor.canonicalSection x) :=
  (fibreTensorEquiv_tmul GlobalEllipticDivisor.transitions GlobalEllipticDivisor.transitions x
    (GlobalEllipticDivisor.canonicalSection x) (GlobalEllipticDivisor.canonicalSection x)).symm

def squareSectionMap (x : Threefold.Space) : squareBundle.TotalSpace := ⟨x, squareSection x⟩

/-- Actual paired-chart coefficients multiply in the genuine tensor bundle. -/
theorem squareSection_localCoefficient (i : SquareIndex) (x : Threefold.Space) :
    squareData.localCoefficient squareSection i x =
      GlobalEllipticDivisor.transitions.localCoefficient GlobalEllipticDivisor.canonicalSection
          i.1 x *
        GlobalEllipticDivisor.transitions.localCoefficient GlobalEllipticDivisor.canonicalSection
          i.2 x := by
  change ((GlobalEllipticDivisor.transitions.transition
      (GlobalEllipticDivisor.transitions.indexAt x) i.1 x : ℂ) *
    (GlobalEllipticDivisor.transitions.transition
      (GlobalEllipticDivisor.transitions.indexAt x) i.2 x : ℂ)) *
      (id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) *
        id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x)) =
    ((GlobalEllipticDivisor.transitions.transition
      (GlobalEllipticDivisor.transitions.indexAt x) i.1 x : ℂ) *
        id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x)) *
      ((GlobalEllipticDivisor.transitions.transition
        (GlobalEllipticDivisor.transitions.indexAt x) i.2 x : ℂ) *
          id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x))
  ring

theorem squareSection_localCoefficient_self (i : GlobalEllipticDivisor.Index)
    (x : Threefold.Space) :
    squareData.localCoefficient squareSection (i, i) x =
      GlobalEllipticDivisor.transitions.localCoefficient
        GlobalEllipticDivisor.canonicalSection i x ^ 2 := by
  rw [squareSection_localCoefficient, pow_two]

theorem squareSectionMap_holomorphic :
    ContMDiff IF ((IF).prod (modelWithCornersSelf ℂ ℂ)) ω squareSectionMap := by
  apply (squareData.section_holomorphic_iff_localCoefficients IF squareSection).mpr
  intro i
  have h₁ := GlobalEllipticDivisor.transitions.localCoefficient_holomorphic IF
    GlobalEllipticDivisor.canonicalSection GlobalEllipticDivisor.canonicalSectionMap_holomorphic i.1
  have h₂ := GlobalEllipticDivisor.transitions.localCoefficient_holomorphic IF
    GlobalEllipticDivisor.canonicalSection GlobalEllipticDivisor.canonicalSectionMap_holomorphic i.2
  exact ((h₁.mono inter_subset_left).mul (h₂.mono inter_subset_right)).congr
    (fun x _ => squareSection_localCoefficient i x)

theorem squareSection_ne_zero {x : Threefold.Space} (hx : x ∈ GlobalEllipticDivisor.outside) :
    squareSection x ≠ 0 := by
  change id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) *
    id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) ≠ 0
  exact mul_ne_zero ((GlobalEllipticDivisor.canonicalSection_ne_zero_iff x).mpr hx)
    ((GlobalEllipticDivisor.canonicalSection_ne_zero_iff x).mpr hx)

theorem squareSection_outside_coefficient {x : Threefold.Space}
    (hx : x ∈ GlobalEllipticDivisor.outside) :
    squareData.localCoefficient squareSection (none, none) x = 1 := by
  rw [squareSection_localCoefficient_self,
    GlobalEllipticDivisor.canonicalSection_localCoefficient none hx]
  norm_num [GlobalEllipticDivisor.localEquation]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic
