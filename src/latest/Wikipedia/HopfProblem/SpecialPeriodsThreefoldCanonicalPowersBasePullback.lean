import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersBasePoint
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBasePullback

/-!
# Pullback of the actual positive point line

The unchanged two-chart dual line and its holomorphic section are pulled
back along the actual sphere projection of the constructed threefold.
The resulting transition data are literally the dual of the previously
constructed pulled-back ideal line, with their genuine native atlases.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase

open CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

local instance powersBasePullbackManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- The genuine inverse-image cocycle of the original positive point line. -/
def pullbackData : HolomorphicCharacterBundle.TransitionData Threefold.Space Bool :=
  pullback data Threefold.projectionSphere Threefold.projectionSphere_holomorphic.continuous

@[simp] theorem pullbackData_baseSet (b : Bool) :
    pullbackData.baseSet b = Threefold.projectionSphere ⁻¹'
      (frameChart b : Set RiemannSphere) := rfl

@[simp] theorem pullbackData_transition (a b : Bool) (x : Threefold.Space) :
    pullbackData.transition a b x = data.transition a b (Threefold.projectionSphere x) := rfl

/-- Dualization and this actual pullback give identical native transition data. -/
theorem pullbackData_eq_dual_base :
    pullbackData = dual GlobalBasePullback.cartier.transitions := rfl

instance pullbackData_isHolomorphic : pullbackData.IsHolomorphic IF :=
  pullback_isHolomorphic data Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic.continuous IF 𝓘(ℂ)
    Threefold.projectionSphere_holomorphic

abbrev pullbackBundle := pullbackData.core

theorem pullbackBundle_holomorphic :
    ContMDiffVectorBundle ω ℂ pullbackBundle.Fiber IF :=
  pullbackData.core_contMDiffVectorBundle IF

/-- The pullback fibre is the actual continuous dual of the pulled-back ideal fibre. -/
def pullbackFiberDualEquiv (x : Threefold.Space) :
    pullbackBundle.Fiber x ≃L[ℂ] (GlobalBasePullback.bundle.Fiber x →L[ℂ] ℂ) :=
  dualFiberEquiv GlobalBasePullback.cartier.transitions x

theorem pullbackFiberDualEquiv_localTriv (b : Bool) (x : Threefold.Space)
    (c : pullbackBundle.Fiber x) (v : GlobalBasePullback.bundle.Fiber x) :
    pullbackFiberDualEquiv x c v =
      (pullbackBundle.localTriv b ⟨x, c⟩).2 *
        (GlobalBasePullback.bundle.localTriv b ⟨x, v⟩).2 :=
  dualFiberEquiv_localTriv GlobalBasePullback.cartier.transitions b x c v

/-- The genuine pullback identification with the original sphere fibre. -/
def fiberPullbackEquiv (x : Threefold.Space) :
    pullbackBundle.Fiber x ≃L[ℂ] bundle.Fiber (Threefold.projectionSphere x) :=
  pullbackFiberEquiv data Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic.continuous x

/-- The actual native total-space map covering the sphere projection. -/
def pullbackToBase : pullbackBundle.TotalSpace → bundle.TotalSpace :=
  pullbackTotalMap data Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic.continuous

theorem pullbackToBase_holomorphic :
    ContMDiff ((IF).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω pullbackToBase :=
  pullbackTotalMap_holomorphic data Threefold.projectionSphere
    Threefold.projectionSphere_holomorphic.continuous IF 𝓘(ℂ)
    Threefold.projectionSphere_holomorphic

theorem pullbackToBase_localTriv (b : Bool) (p : pullbackBundle.TotalSpace) :
    bundle.localTriv b (pullbackToBase p) =
      (Threefold.projectionSphere p.proj, (pullbackBundle.localTriv b p).2) := rfl

/-- The local coefficients are literal compositions, not newly assigned divisor labels. -/
def pullbackCoefficient (b : Bool) (x : Threefold.Space) : ℂ :=
  pointCoefficient b (Threefold.projectionSphere x)

@[simp] theorem pullbackCoefficient_false (x : Threefold.Space) :
    pullbackCoefficient false x =
      CanonicalGlobal.BaseTwist.finiteCoordinate (Threefold.projectionSphere x) - 1 := rfl

@[simp] theorem pullbackCoefficient_true (x : Threefold.Space) :
    pullbackCoefficient true x =
      1 - CanonicalGlobal.BaseTwist.infinityCoordinate (Threefold.projectionSphere x) := rfl

theorem pullbackCoefficient_compatible : pullbackData.IsCompatible pullbackCoefficient :=
  fun a b x hx => pointCoefficient_compatible a b (Threefold.projectionSphere x) hx

theorem pullbackCoefficient_holomorphic (b : Bool) :
    ContMDiffOn IF 𝓘(ℂ) ω (pullbackCoefficient b) (pullbackData.baseSet b) :=
  (pointCoefficient_holomorphic b).comp Threefold.projectionSphere_holomorphic.contMDiffOn
    (fun _ hx => hx)

/-- The globally holomorphic native section of the pulled-back point line. -/
def pullbackSection : ∀ x : Threefold.Space, pullbackBundle.Fiber x :=
  pullbackData.sectionFromLocal pullbackCoefficient

def pullbackSectionMap (x : Threefold.Space) : pullbackBundle.TotalSpace :=
  ⟨x, pullbackSection x⟩

theorem pullbackSectionMap_holomorphic :
    ContMDiff IF ((IF).prod 𝓘(ℂ)) ω pullbackSectionMap :=
  pullbackData.sectionFromLocal_holomorphic IF pullbackCoefficient
    pullbackCoefficient_compatible pullbackCoefficient_holomorphic

theorem pullbackSection_localCoefficient (b : Bool) {x : Threefold.Space}
    (hx : x ∈ pullbackData.baseSet b) :
    pullbackData.localCoefficient pullbackSection b x = pullbackCoefficient b x :=
  pullbackData.localCoefficient_sectionFromLocal pullbackCoefficient
    pullbackCoefficient_compatible b hx

theorem pullbackSection_finite_coefficient {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ∈ finiteChart) :
    pullbackData.localCoefficient pullbackSection false x =
      CanonicalGlobal.BaseTwist.finiteCoordinate (Threefold.projectionSphere x) - 1 :=
  pullbackSection_localCoefficient false hx

theorem pullbackSection_infinity_coefficient {x : Threefold.Space}
    (hx : Threefold.projectionSphere x ∈ infinityChart) :
    pullbackData.localCoefficient pullbackSection true x =
      1 - CanonicalGlobal.BaseTwist.infinityCoordinate (Threefold.projectionSphere x) :=
  pullbackSection_localCoefficient true hx

/-- The fibrewise pullback map takes the actual section to the original point section. -/
theorem fiberPullbackEquiv_section (x : Threefold.Space) :
    fiberPullbackEquiv x (pullbackSection x) =
      pointSection (Threefold.projectionSphere x) := rfl

theorem pullbackToBase_section (x : Threefold.Space) :
    pullbackToBase (pullbackSectionMap x) =
      pointSectionMap (Threefold.projectionSphere x) := rfl

/-- Exact zero set of the actual holomorphic pullback section. -/
theorem pullbackSection_eq_zero_iff (x : Threefold.Space) :
    pullbackSection x = 0 ↔
      Threefold.projectionSphere x = ((1 : ℂ) : RiemannSphere) :=
  pointSection_eq_zero_iff (Threefold.projectionSphere x)

theorem pullbackSection_ne_zero_iff (x : Threefold.Space) :
    pullbackSection x ≠ 0 ↔
      Threefold.projectionSphere x ≠ ((1 : ℂ) : RiemannSphere) :=
  not_congr (pullbackSection_eq_zero_iff x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase
