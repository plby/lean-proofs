import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorTransitions
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartier

/-!
# The actual effective Cartier divisor twice the elliptic central surface

The presentation uses the genuine order-four elliptic canonical section
on its full patch and the constant local equation one off the actual
central surface.  Its unit transitions are the proved clutching cocycle,
its denominator is one, and its generic set is the proved dense open
complement of that surface.  The associated line bundle is the existing
holomorphic transition-data core, with a genuine global holomorphic
section whose zero set is precisely the central surface.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor

open TrianglePeriodFamily.Canonical

local notation "I" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace

local instance divisorManifold : IsManifold I ω Threefold.Space := Threefold.space_isManifold

/-- A genuine effective Cartier presentation by the actual local section
coefficients, with denominator one and the actual dense nonzero locus. -/
def cartierData : CanonicalGlobal.CartierData I Threefold.Space Index where
  transitions := transitions
  isHolomorphic := transitions_isHolomorphic
  numerator := localEquation
  denominator _ _ := 1
  numerator_holomorphic := localEquation_holomorphicOn
  denominator_holomorphic _ := contMDiffOn_const
  genericSet := outside
  genericSet_dense := outside_dense
  numerator_ne_zero i _ hi hg := localEquation_ne_zero_on_outside i hi hg
  denominator_ne_zero _ _ _ _ := one_ne_zero
  ratio i j x hij := by
    change localEquation j x * 1 = (transition i j x : ℂ) * localEquation i x * 1
    rw [mul_one, mul_one]
    exact (localEquation_change i j hij).symm

/-- The associated analytic line bundle is constructed from the actual
Cartier unit cocycle, rather than assigned a divisor name. -/
abbrev divisorBundle := cartierData.associatedBundle

theorem divisorBundle_holomorphic : ContMDiffVectorBundle ω ℂ divisorBundle.Fiber I :=
  cartierData.associatedBundle_contMDiffVectorBundle

theorem divisorBundle_fibre_rank_one (x : Threefold.Space) :
    Module.finrank ℂ (divisorBundle.Fiber x) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

@[simp] theorem denominator_eq_one (i : Index) (x : Threefold.Space) :
    cartierData.denominator i x = 1 := rfl

theorem localFraction_eq_localEquation (i : Index) (x : Threefold.Space) :
    cartierData.localFraction i x = localEquation i x := div_one _

theorem localEquation_compatible : transitions.IsCompatible localEquation :=
  fun i j _ hx => localEquation_change i j hx

/-- The actual global section is glued from the proved local equations
in the independently constructed bundle's actual trivializations. -/
def canonicalSection (x : Threefold.Space) : divisorBundle.Fiber x :=
  transitions.sectionFromLocal localEquation x

def canonicalSectionMap (x : Threefold.Space) : divisorBundle.TotalSpace :=
  ⟨x, canonicalSection x⟩

@[simp] theorem canonicalSectionMap_proj (x : Threefold.Space) :
    (canonicalSectionMap x).proj = x := rfl

theorem canonicalSectionMap_holomorphic :
    ContMDiff I ((I).prod I₁) ω canonicalSectionMap :=
  transitions.sectionFromLocal_holomorphic I localEquation localEquation_compatible
    localEquation_holomorphicOn

def canonicalHolomorphicSection : ContMDiffSection I ℂ ω divisorBundle.Fiber where
  toFun := canonicalSection
  contMDiff_toFun := canonicalSectionMap_holomorphic

/-- The meromorphic section supplied by the Cartier fractions is here
the genuine holomorphic section on the whole threefold. -/
theorem cartierRawSection_eq : cartierData.rawSection = canonicalSection := by
  funext x
  exact localFraction_eq_localEquation (indexAt x) x

theorem canonicalSection_localCoefficient (i : Index) {x : Threefold.Space}
    (hx : x ∈ baseSet i) :
    transitions.localCoefficient canonicalSection i x = localEquation i x :=
  transitions.localCoefficient_sectionFromLocal localEquation localEquation_compatible i hx

/-- Each actual defining equation cuts out exactly the central support
inside its own chart; the outside defining equation has no zeros. -/
theorem localEquation_eq_zero_iff (i : Index) {x : Threefold.Space}
    (hx : x ∈ baseSet i) : localEquation i x = 0 ↔ x ∈ support := by
  cases i with
  | none => exact iff_of_false one_ne_zero hx
  | some i => exact patchCoefficient_eq_zero_iff i hx.1 hx.2

theorem canonicalSection_eq_zero_iff (x : Threefold.Space) :
    canonicalSection x = 0 ↔ x ∈ support :=
  localEquation_eq_zero_iff (indexAt x) (mem_baseSet_at x)

theorem canonicalSection_ne_zero_iff (x : Threefold.Space) :
    canonicalSection x ≠ 0 ↔ x ∈ outside :=
  (canonicalSection_eq_zero_iff x).not

theorem canonicalSection_zeroSet : {x | canonicalSection x = 0} = support := by
  ext x
  exact canonicalSection_eq_zero_iff x

/-- The support is the literal global sphere fibre at one. -/
theorem canonicalSection_zeroSet_projection :
    {x | canonicalSection x = 0} =
      Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)} :=
  canonicalSection_zeroSet

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalEllipticDivisor
