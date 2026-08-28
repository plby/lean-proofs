import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBaseCartier
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBasePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorBase

/-!
# The pulled-back point-divisor presentation

The generic open set is the actual complement of the fibre over `1`.
Its density is supplied by the existing genuine elliptic power charts.
The Cartier presentation, native dual bundle, and globally holomorphic
pulled-back section agree literally.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

theorem data_indexAt_finite {p : RiemannSphere} (hp : p ∈ finiteChart) :
    data.indexAt p = false := by
  change CanonicalGlobal.BaseTwist.indexAt p = false
  simp only [CanonicalGlobal.BaseTwist.indexAt, if_neg ((mem_finiteChart p).mp hp)]

theorem pullbackData_indexAt_finite {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ∈ finiteChart) :
    pullbackData.indexAt x = false :=
  data_indexAt_finite hx

theorem pointOutside_preimage_eq :
    Threefold.projectionSphere ⁻¹' (pointOutside : Set RiemannSphere) =
      (GlobalEllipticDivisor.outside : Set Threefold.Space) := rfl

theorem pointOutside_preimage_dense :
    Dense (Threefold.projectionSphere ⁻¹' (pointOutside : Set RiemannSphere)) := by
  rw [pointOutside_preimage_eq]
  exact GlobalEllipticDivisor.outside_dense

/-- The actual holomorphic pullback of the positive point Cartier data. -/
def pullbackCartier : CanonicalGlobal.CartierData IF Threefold.Space Bool :=
  cartier.pullback Threefold.projectionSphere Threefold.projectionSphere_holomorphic
    pointOutside_preimage_dense

@[simp] theorem pullbackCartier_transitions :
    pullbackCartier.transitions = pullbackData := rfl

@[simp] theorem pullbackCartier_genericSet :
    (pullbackCartier.genericSet : Set Threefold.Space) =
      (GlobalEllipticDivisor.outside : Set Threefold.Space) := rfl

@[simp] theorem pullbackCartier_localFraction (b : Bool) (x : Threefold.Space) :
    pullbackCartier.localFraction b x = pullbackCoefficient b x :=
  cartier_localFraction b (Threefold.projectionSphere x)

@[simp] theorem pullbackCartier_rawSection (x : Threefold.Space) :
    pullbackCartier.rawSection x = pullbackSection x :=
  cartier_rawSection (Threefold.projectionSphere x)

theorem pullbackCartier_rawSectionMap :
    pullbackCartier.rawSectionMap = pullbackSectionMap := by
  funext x
  change (⟨x, pullbackCartier.rawSection x⟩ : pullbackBundle.TotalSpace) =
    ⟨x, pullbackSection x⟩
  rw [pullbackCartier_rawSection]

theorem pullbackCartier_rawSectionMap_holomorphic :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω pullbackCartier.rawSectionMap := by
  rw [pullbackCartier_rawSectionMap]
  exact pullbackSectionMap_holomorphic

/-- Its zero support is the literal order-four elliptic fibre of the constructed projection. -/
theorem pullbackCartier_zeroSupport :
    {x : Threefold.Space | pullbackCartier.rawSection x = 0} =
      GlobalEllipticDivisor.support := by
  ext x
  change pullbackCartier.rawSection x = 0 ↔ x ∈ GlobalEllipticDivisor.support
  rw [pullbackCartier_rawSection]
  exact pullbackSection_eq_zero_iff x

theorem pullbackSection_eq_zero_iff_support (x : Threefold.Space) :
    pullbackSection x = 0 ↔ x ∈ GlobalEllipticDivisor.support :=
  pullbackSection_eq_zero_iff x

theorem pullbackCartier_dual_base :
    pullbackCartier.transitions =
      CanonicalGlobalLineBundle.dual GlobalBasePullback.cartier.transitions := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase
