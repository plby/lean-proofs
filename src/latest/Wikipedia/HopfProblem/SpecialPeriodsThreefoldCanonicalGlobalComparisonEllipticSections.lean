import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalComparisonEllipticHolomorphic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticComparisonCompatibility

/-!
# Exact section transport by the actual elliptic bundle comparison

The prescribed Cartier section is mapped to the genuine elliptic
extension of the regular canonical form on the entire order-four patch.
The equality uses the finite base frame and the independently proved
effective-divisor section comparison.  It therefore remains valid on
the central surface, where the sections vanish; no division by either
section is used.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonElliptic

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace

local instance ellipticComparisonSectionsManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- In the actual preferred finite frame the prescribed section is the
effective-divisor section, including at its central zeros. -/
theorem rawSection_preferred_eq_divisor {x : Threefold.Space} (hx : x ∈ patch) :
    id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x) =
      id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x) := by
  change GlobalPrescribedDivisor.cartier.localFraction (sourceData.indexAt x) x = _
  rw [source_indexAt_of_mem hx, GlobalPrescribedDivisor.localFraction_finite]
  rfl

/-- The exact preferred-coordinate equality used in the global gluing
argument.  The target is the actual elliptic canonical section pushed
through the genuine native-presentation fibre equivalence. -/
theorem preferredUnit_rawSection (x : patch) :
    (preferredUnit x.val : ℂ) * id (α := ℂ) (GlobalPrescribedDivisor.cartier.rawSection x.val) =
      id (α := ℂ) (NativePresentation.fiberEquiv x.val
        (GlobalEllipticComparison.extendedSection .four x)) := by
  rw [preferredUnit_val_of_mem x.property, rawSection_preferred_eq_divisor x.property,
    ratioExtension_of_mem x.property, mul_assoc]
  change GlobalEllipticComparison.patchRatio .four x *
      ((GlobalEllipticDivisor.patchWeight x.val : ℂ) *
        id (α := ℂ) (GlobalEllipticDivisor.canonicalSection x.val)) =
    GlobalEllipticComparison.patchRatio .four x * id (α := ℂ) (Sections.patchSection .four x)
  exact congrArg (fun c : ℂ => GlobalEllipticComparison.patchRatio .four x * c)
    (GlobalEllipticDivisor.patchFiberEquiv_canonicalSection x)

/-- This is an equality in the actual target bundle fibre. -/
theorem fiberEquiv_rawSection (x : patch) :
    fiberEquiv x.val (GlobalPrescribedDivisor.cartier.rawSection x.val) =
      NativePresentation.fiberEquiv x.val (GlobalEllipticComparison.extendedSection .four x) :=
  preferredUnit_rawSection x

/-- The actual total-space map takes the prescribed Cartier section to
the original elliptic extension in the native canonical presentation. -/
theorem totalMap_rawSection (x : patch) :
    totalMap (GlobalPrescribedDivisor.cartier.rawSectionMap x.val) =
      NativePresentation.bundleBiholomorph
        (GlobalEllipticComparison.extendedSectionMap .four x) :=
  congrArg (fun c : ℂ => (⟨x.val, c⟩ : targetBundle.TotalSpace)) (preferredUnit_rawSection x)

/-- The equality in the original intrinsic canonical fibre, not merely
in the transition-data presentation. -/
theorem nativeFiberEquiv_rawSection (x : patch) :
    nativeFiberEquiv x.val (GlobalPrescribedDivisor.cartier.rawSection x.val) =
      GlobalEllipticComparison.extendedSection .four x :=
  preferredUnit_rawSection x

theorem nativeTotalMap_rawSection (x : patch) :
    nativeTotalMap (GlobalPrescribedDivisor.cartier.rawSectionMap x.val) =
      GlobalEllipticComparison.extendedSectionMap .four x := by
  rw [nativeTotalMap, totalMap_rawSection,
    NativePresentation.bundleBiholomorph.symm_apply_apply]

/-- On the punctured overlap this is the already constructed regular
canonical form, by the proved actual-cover compatibility theorem. -/
theorem nativeFiberEquiv_rawSection_regular (x : patch) (hx : x.val ∈ regularLocus) :
    nativeFiberEquiv x.val (GlobalPrescribedDivisor.cartier.rawSection x.val) =
      GlobalRegular.globalSection ⟨x.val, hx⟩ :=
  (nativeFiberEquiv_rawSection x).trans
    (GlobalEllipticComparison.globalSection_eq_extendedSection .four x hx).symm

theorem totalMap_rawSection_regular (x : patch) (hx : x.val ∈ regularLocus) :
    totalMap (GlobalPrescribedDivisor.cartier.rawSectionMap x.val) =
      NativePresentation.bundleBiholomorph
        (⟨x.val, GlobalRegular.globalSection ⟨x.val, hx⟩⟩ :
          Threefold.Canonical.bundle.TotalSpace) := by
  rw [totalMap_rawSection]
  apply congrArg NativePresentation.bundleBiholomorph
  exact congrArg (fun v : Threefold.Canonical.bundle.Fiber x.val =>
      (⟨x.val, v⟩ : Threefold.Canonical.bundle.TotalSpace))
    (GlobalEllipticComparison.globalSection_eq_extendedSection .four x hx).symm

/-- Full intrinsic alternating three-covectors are preserved in the
section comparison, on every point of the entire elliptic patch. -/
theorem rawSection_intrinsic (x : patch) :
    Threefold.Canonical.intrinsicEquiv x.val
      (nativeFiberEquiv x.val (GlobalPrescribedDivisor.cartier.rawSection x.val)) =
    Threefold.Canonical.intrinsicEquiv x.val (GlobalEllipticComparison.extendedSection .four x) :=
  congrArg (Threefold.Canonical.intrinsicEquiv x.val) (nativeFiberEquiv_rawSection x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparisonElliptic
