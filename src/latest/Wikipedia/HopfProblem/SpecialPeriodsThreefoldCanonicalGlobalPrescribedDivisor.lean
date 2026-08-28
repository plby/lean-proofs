import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBasePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalEllipticDivisorOrders
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCartierSections

/-!
# The genuine divisor line prescribed by the canonical formula

This constructs the tensor product of the actual pulled-back ideal line
`f* O(-infinity)` and the independently clutched effective divisor line
`O(2 S2)`.  Its transitions, local meromorphic fractions, and native
tensor-section coefficients are explicit.  Its identification with the
intrinsic canonical bundle is a separate gluing theorem, not an input to
this construction.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalPrescribedDivisor

open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace CuspGeometry.nativeChartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

abbrev Index := Bool × GlobalEllipticDivisor.Index

/-- The actual tensor Cartier presentation of the two constructed lines. -/
def cartier : CanonicalGlobal.CartierData IF Threefold.Space Index :=
  GlobalBasePullback.cartier.tensor GlobalEllipticDivisor.cartierData

abbrev bundle := cartier.associatedBundle

theorem bundle_holomorphic : ContMDiffVectorBundle ω ℂ bundle.Fiber IF :=
  cartier.associatedBundle_contMDiffVectorBundle

/-- Full fibre tensor identification, not just multiplication of labels. -/
def fiberTensorEquiv (x : Threefold.Space) :
    GlobalBasePullback.bundle.Fiber x ⊗[ℂ] GlobalEllipticDivisor.divisorBundle.Fiber x ≃ₗ[ℂ]
      bundle.Fiber x :=
  GlobalBasePullback.cartier.tensorFiberEquiv GlobalEllipticDivisor.cartierData x

theorem transition_eq (i j : Index) (x : Threefold.Space) :
    cartier.transitions.transition i j x =
      CanonicalGlobal.BaseTwist.data.transition i.1 j.1 (Threefold.projectionSphere x) *
        GlobalEllipticDivisor.transitions.transition i.2 j.2 x := rfl

theorem numerator_eq (i : Index) (x : Threefold.Space) :
    cartier.numerator i x = GlobalEllipticDivisor.localEquation i.2 x :=
  one_mul _

theorem denominator_eq (i : Index) (x : Threefold.Space) :
    cartier.denominator i x = GlobalBasePullback.cartier.denominator i.1 x :=
  mul_one _

/-- The generic set removes the actual second elliptic fibre and the
actual cusp fibre, and no other points. -/
@[simp] theorem mem_genericSet (x : Threefold.Space) :
    x ∈ cartier.genericSet ↔ Threefold.projectionSphere x ≠ (∞ : RiemannSphere) ∧
      Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere) := by
  change (Threefold.projectionSphere x ∈ finiteChart ∧
      Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere)) ↔ _
  rw [mem_finiteChart]

theorem genericSet_dense : Dense (cartier.genericSet : Set Threefold.Space) :=
  cartier.genericSet_dense

/-- A genuine nonzero holomorphic section on the actual dense open. -/
theorem meromorphicSectionMap_holomorphic :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω cartier.meromorphicSectionMap :=
  cartier.meromorphicSectionMap_holomorphic

theorem meromorphicSection_ne_zero (x : cartier.genericSet) :
    cartier.meromorphicSection x ≠ 0 := cartier.meromorphicSection_ne_zero x

theorem rawSection_tensor (x : Threefold.Space) :
    cartier.rawSection x = fiberTensorEquiv x
      (GlobalBasePullback.cartier.rawSection x ⊗ₜ[ℂ]
        GlobalEllipticDivisor.cartierData.rawSection x) :=
  GlobalBasePullback.cartier.tensor_rawSection GlobalEllipticDivisor.cartierData x

/-- On the finite sphere chart the local fraction is the actual defining
equation of the effective elliptic divisor. -/
theorem localFraction_finite (i : GlobalEllipticDivisor.Index) (x : Threefold.Space) :
    cartier.localFraction (false, i) x = GlobalEllipticDivisor.localEquation i x := by
  change (GlobalBasePullback.cartier.tensor GlobalEllipticDivisor.cartierData).localFraction
    (false, i) x = _
  rw [CanonicalGlobal.CartierData.tensor_localFraction, GlobalBasePullback.localFraction_finite,
    one_mul, GlobalEllipticDivisor.localFraction_eq_localEquation]

/-- Off the elliptic surface the only factor is the actual pulled-back
base fraction.  This includes a full neighborhood of the cusp fibre. -/
theorem localFraction_outside (b : Bool) (x : Threefold.Space) :
    cartier.localFraction (b, none) x = GlobalBasePullback.cartier.localFraction b x := by
  change (GlobalBasePullback.cartier.tensor GlobalEllipticDivisor.cartierData).localFraction
    (b, none) x = _
  rw [CanonicalGlobal.CartierData.tensor_localFraction,
    GlobalEllipticDivisor.localFraction_eq_localEquation]
  exact mul_one _

/-- This equality concerns the actual native bundle local trivialization. -/
theorem rawSection_localCoefficient (i : Index) {x : Threefold.Space}
    (hi : x ∈ cartier.transitions.baseSet i) (hx : x ∈ cartier.genericSet) :
    cartier.transitions.localCoefficient cartier.rawSection i x = cartier.localFraction i x :=
  cartier.rawSection_localCoefficient i hi hx

/-- The actual numerator in the cusp defining chart is the unit one. -/
@[simp] theorem numerator_cusp (x : Threefold.Space) : cartier.numerator (true, none) x = 1 :=
  one_mul 1

/-- The true pulled-back cusp denominator has one factor for each
distinct branch, and the remaining factor is an analytic unit. -/
theorem cusp_fraction_normalCrossingChart (x : CuspGeometry.LocalSpace)
    (hx : CuspGeometry.parameter x = 0) :
    ∃ J : Finset (Fin 3),
      ∃ e : PartialDiffeomorph IF (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
          Threefold.Space (ToricCharts.CoordinateSpace 3) ω,
      J.Nonempty ∧ CuspGeometry.inclusion x ∈ e.source ∧
      e (CuspGeometry.inclusion x) = 0 ∧
      AnalyticAt ℂ (GlobalCusp.branchUnit J) 0 ∧ GlobalCusp.branchUnit J 0 ≠ 0 ∧
      ∀ w ∈ e.target, cartier.localFraction (true, none) (e.symm w) =
        (GlobalCusp.branchProduct J w * GlobalCusp.branchUnit J w)⁻¹ := by
  obtain ⟨J, e, hJ, hxs, hzero, ha, hn, he⟩ :=
    GlobalBasePullback.denominator_reduced_normalCrossingChart x hx
  refine ⟨J, e, hJ, hxs, hzero, ha, hn, ?_⟩
  intro w hw
  calc
    cartier.localFraction (true, none) (e.symm w) =
        GlobalBasePullback.cartier.localFraction true (e.symm w) := localFraction_outside _ _
    _ = (GlobalBasePullback.cartier.denominator true (e.symm w))⁻¹ := one_div _
    _ = _ := congrArg Inv.inv (he w hw)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalPrescribedDivisor
