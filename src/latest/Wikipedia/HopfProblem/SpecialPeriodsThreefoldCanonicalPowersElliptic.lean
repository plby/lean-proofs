import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersEllipticLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsSectionDivisor

/-!
# The actual quartic elliptic divisor bundle comparison

The tensor square of the genuine effective Cartier line of `2 * S₂`
is holomorphically isomorphic to the actual pullback of the point line
at `1` on the sphere.  The comparison is obtained from the proved
quartic native-chart equations, glued using the dense complement of
the central surface.  It sends the tensor square of the actual divisor
section to the actual pulled-back point section, including on the
central surface.  Both total spaces retain their original native
bundle charts, and the fibre map identifies the full tensor product.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic

open TrianglePeriodFamily.Canonical CanonicalGlobalLineBundle

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "IT" =>
  ModelWithCorners.prod (modelWithCornersSelf ℂ Model) (modelWithCornersSelf ℂ ℂ)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The unconditional native cross-cover comparison.  Every local
unit equation and their agreement across the central surface have
been proved from the actual sections and charts. -/
def comparison : CrossGauge IF squareData PowersBase.pullbackData :=
  SectionDivisorComparison.crossGaugeOfLocal IF squareData PowersBase.pullbackData
    squareSection PowersBase.pullbackSection GlobalEllipticDivisor.outside
    GlobalEllipticDivisor.outside_dense (fun _ hx => squareSection_ne_zero hx)
    localComparison_exists

theorem comparison_fiberEquiv_section (x : Threefold.Space) :
    comparison.fiberEquiv x (squareSection x) = PowersBase.pullbackSection x :=
  SectionDivisorComparison.crossGaugeOfLocal_fiberEquiv_section IF squareData
    PowersBase.pullbackData squareSection PowersBase.pullbackSection
    GlobalEllipticDivisor.outside GlobalEllipticDivisor.outside_dense
    (fun _ hx => squareSection_ne_zero hx) localComparison_exists x

/-- A genuine holomorphic, base-preserving isomorphism of the original
tensor-square bundle with the independently constructed pulled-back
point line. -/
def bundleBiholomorph :
    Diffeomorph IT IT squareBundle.TotalSpace PowersBase.pullbackBundle.TotalSpace ω :=
  comparison.diffeomorph

def fiberEquiv (x : Threefold.Space) :
    squareBundle.Fiber x ≃L[ℂ] PowersBase.pullbackBundle.Fiber x :=
  comparison.fiberEquiv x

@[simp] theorem bundleBiholomorph_proj (p : squareBundle.TotalSpace) :
    (bundleBiholomorph p).proj = p.proj := rfl

@[simp] theorem bundleBiholomorph_symm_proj (p : PowersBase.pullbackBundle.TotalSpace) :
    (bundleBiholomorph.symm p).proj = p.proj := rfl

theorem bundleBiholomorph_mk (x : Threefold.Space) (v : squareBundle.Fiber x) :
    bundleBiholomorph ⟨x, v⟩ = ⟨x, fiberEquiv x v⟩ := rfl

theorem bundleBiholomorph_add (x : Threefold.Space) (v w : squareBundle.Fiber x) :
    id (α := PowersBase.pullbackBundle.Fiber x) (bundleBiholomorph ⟨x, v + w⟩).2 =
      id (α := PowersBase.pullbackBundle.Fiber x) (bundleBiholomorph ⟨x, v⟩).2 +
        id (α := PowersBase.pullbackBundle.Fiber x) (bundleBiholomorph ⟨x, w⟩).2 :=
  (fiberEquiv x).map_add v w

theorem bundleBiholomorph_smul (x : Threefold.Space) (c : ℂ) (v : squareBundle.Fiber x) :
    id (α := PowersBase.pullbackBundle.Fiber x) (bundleBiholomorph ⟨x, c • v⟩).2 =
      c • id (α := PowersBase.pullbackBundle.Fiber x) (bundleBiholomorph ⟨x, v⟩).2 :=
  (fiberEquiv x).map_smul c v

/-- The actual section is transported at every point, not only off its zeros. -/
theorem bundleBiholomorph_section (x : Threefold.Space) :
    bundleBiholomorph (squareSectionMap x) = PowersBase.pullbackSectionMap x :=
  SectionDivisorComparison.crossGaugeOfLocal_diffeomorph_section IF squareData
    PowersBase.pullbackData squareSection PowersBase.pullbackSection
    GlobalEllipticDivisor.outside GlobalEllipticDivisor.outside_dense
    (fun _ hx => squareSection_ne_zero hx) localComparison_exists x

/-- The induced equivalence is on the full tensor product of the two
actual Cartier fibres, not a formal identification of power labels. -/
def fiberTensorEquiv (x : Threefold.Space) :
    GlobalEllipticDivisor.divisorBundle.Fiber x ⊗[ℂ]
        GlobalEllipticDivisor.divisorBundle.Fiber x ≃ₗ[ℂ]
      PowersBase.pullbackBundle.Fiber x :=
  (fibreTensorEquiv GlobalEllipticDivisor.transitions
    GlobalEllipticDivisor.transitions x).trans (fiberEquiv x).toLinearEquiv

theorem fiberTensorEquiv_section (x : Threefold.Space) :
    fiberTensorEquiv x (GlobalEllipticDivisor.canonicalSection x ⊗ₜ[ℂ]
      GlobalEllipticDivisor.canonicalSection x) = PowersBase.pullbackSection x := by
  change comparison.fiberEquiv x (fibreTensorEquiv
    GlobalEllipticDivisor.transitions GlobalEllipticDivisor.transitions x
      (GlobalEllipticDivisor.canonicalSection x ⊗ₜ[ℂ]
        GlobalEllipticDivisor.canonicalSection x)) = _
  rw [← squareSection_eq_tensor, comparison_fiberEquiv_section]

/-- The tensor-fibre identification and the genuine total-space map
are literally compatible for every tensor, not only decomposable ones. -/
theorem bundleBiholomorph_tensor (x : Threefold.Space)
    (v : GlobalEllipticDivisor.divisorBundle.Fiber x ⊗[ℂ]
      GlobalEllipticDivisor.divisorBundle.Fiber x) :
    bundleBiholomorph ⟨x, fibreTensorEquiv GlobalEllipticDivisor.transitions
      GlobalEllipticDivisor.transitions x v⟩ = ⟨x, fiberTensorEquiv x v⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersElliptic
