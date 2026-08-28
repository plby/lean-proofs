import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwist
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleDual

/-!
# The actual positive point line on the original sphere

The line is the genuine dual of the existing ideal line `O(-infinity)`.
In its original finite and reciprocal charts the coefficients `t - 1`
and `1 - w` glue to a holomorphic section. Its only zero is the actual
sphere point `1`, and its finite-coordinate vanishing order there is one.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase

open CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

/-- The actual dual cocycle of the fixed sphere ideal line, on its unchanged cover. -/
def data : HolomorphicCharacterBundle.TransitionData RiemannSphere Bool :=
  dual CanonicalGlobal.BaseTwist.data

@[simp] theorem data_baseSet (b : Bool) :
    data.baseSet b = (frameChart b : Set RiemannSphere) := rfl

@[simp] theorem data_transition (a b : Bool) (p : RiemannSphere) :
    data.transition a b p = (CanonicalGlobal.BaseTwist.data.transition a b p)⁻¹ := rfl

instance data_isHolomorphic : data.IsHolomorphic 𝓘(ℂ) :=
  dual_isHolomorphic CanonicalGlobal.BaseTwist.data 𝓘(ℂ)

/-- The original native bundle obtained from the dual cocycle. -/
abbrev bundle := data.core

theorem bundle_holomorphic : ContMDiffVectorBundle ω ℂ bundle.Fiber 𝓘(ℂ) :=
  data.core_contMDiffVectorBundle 𝓘(ℂ)

/-- Every fibre is the full continuous complex-linear dual, not a formal inverse label. -/
def fiberDualEquiv (p : RiemannSphere) :
    bundle.Fiber p ≃L[ℂ] (CanonicalGlobal.BaseTwist.bundle.Fiber p →L[ℂ] ℂ) :=
  dualFiberEquiv CanonicalGlobal.BaseTwist.data p

theorem fiberDualEquiv_localTriv (b : Bool) (p : RiemannSphere)
    (c : bundle.Fiber p) (v : CanonicalGlobal.BaseTwist.bundle.Fiber p) :
    fiberDualEquiv p c v =
      (bundle.localTriv b ⟨p, c⟩).2 * (CanonicalGlobal.BaseTwist.bundle.localTriv b ⟨p, v⟩).2 :=
  dualFiberEquiv_localTriv CanonicalGlobal.BaseTwist.data b p c v

theorem transition_false_true {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (data.transition false true p : ℂ) = CanonicalGlobal.BaseTwist.infinityCoordinate p := by
  rw [data_transition, Units.val_inv_eq_inv_val,
    CanonicalGlobal.BaseTwist.data_transition_false_true hp]
  exact (CanonicalGlobal.BaseTwist.infinityCoordinate_eq_inv_finiteCoordinate p).symm

theorem transition_true_false {p : RiemannSphere} (hp : p ∈ chartOverlap) :
    (data.transition true false p : ℂ) = CanonicalGlobal.BaseTwist.finiteCoordinate p := by
  rw [data_transition, Units.val_inv_eq_inv_val,
    CanonicalGlobal.BaseTwist.data_transition_true_false hp,
    CanonicalGlobal.BaseTwist.infinityCoordinate_eq_inv_finiteCoordinate, inv_inv]

/-- Local coefficients of the positive point-divisor section. -/
def pointCoefficient : Bool → RiemannSphere → ℂ
  | false, p => CanonicalGlobal.BaseTwist.finiteCoordinate p - 1
  | true, p => 1 - CanonicalGlobal.BaseTwist.infinityCoordinate p

theorem pointCoefficient_holomorphic (b : Bool) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (pointCoefficient b) (data.baseSet b) := by
  cases b
  · exact CanonicalGlobal.BaseTwist.finiteCoordinate_holomorphicOn.sub contMDiffOn_const
  · exact contMDiffOn_const.sub CanonicalGlobal.BaseTwist.infinityCoordinate_holomorphicOn

/-- Compatibility follows from the actual reciprocal-coordinate transition on the sphere. -/
theorem pointCoefficient_compatible : data.IsCompatible pointCoefficient := by
  intro a b p hp
  cases a <;> cases b
  · change (↑((CanonicalGlobal.BaseTwist.data.transition false false p)⁻¹) : ℂ) *
      pointCoefficient false p = pointCoefficient false p
    simp only [CanonicalGlobal.BaseTwist.data_transition,
      CanonicalGlobal.BaseTwist.transition_self, inv_one, Units.val_one, one_mul]
  · rw [transition_false_true hp]
    change CanonicalGlobal.BaseTwist.infinityCoordinate p *
      (CanonicalGlobal.BaseTwist.finiteCoordinate p - 1) =
        1 - CanonicalGlobal.BaseTwist.infinityCoordinate p
    rw [mul_sub, CanonicalGlobal.BaseTwist.infinityCoordinate_mul_finiteCoordinate hp, mul_one]
  · rw [transition_true_false ⟨hp.2, hp.1⟩]
    change CanonicalGlobal.BaseTwist.finiteCoordinate p *
      (1 - CanonicalGlobal.BaseTwist.infinityCoordinate p) =
        CanonicalGlobal.BaseTwist.finiteCoordinate p - 1
    rw [mul_sub, mul_one,
      CanonicalGlobal.BaseTwist.finiteCoordinate_mul_infinityCoordinate ⟨hp.2, hp.1⟩]
  · change (↑((CanonicalGlobal.BaseTwist.data.transition true true p)⁻¹) : ℂ) *
      pointCoefficient true p = pointCoefficient true p
    simp only [CanonicalGlobal.BaseTwist.data_transition,
      CanonicalGlobal.BaseTwist.transition_self, inv_one, Units.val_one, one_mul]

/-- The point divisor is detected by the actual coordinate values, including at infinity. -/
theorem pointCoefficient_eq_zero_iff (b : Bool) (p : RiemannSphere) :
    pointCoefficient b p = 0 ↔ p = ((1 : ℂ) : RiemannSphere) := by
  cases b <;> induction p using OnePoint.rec with
  | infty => simp [pointCoefficient]
  | coe z =>
    simp only [pointCoefficient, CanonicalGlobal.BaseTwist.finiteCoordinate_coe,
      CanonicalGlobal.BaseTwist.infinityCoordinate_coe, sub_eq_zero]
    simp

/-- The genuine globally holomorphic point-divisor section of the dual bundle. -/
def pointSection : ∀ p : RiemannSphere, bundle.Fiber p :=
  data.sectionFromLocal pointCoefficient

def pointSectionMap (p : RiemannSphere) : bundle.TotalSpace := ⟨p, pointSection p⟩

theorem pointSectionMap_holomorphic :
    ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ)) ω pointSectionMap :=
  data.sectionFromLocal_holomorphic 𝓘(ℂ) pointCoefficient pointCoefficient_compatible
    pointCoefficient_holomorphic

theorem pointSection_localCoefficient (b : Bool) {p : RiemannSphere}
    (hp : p ∈ data.baseSet b) :
    data.localCoefficient pointSection b p = pointCoefficient b p :=
  data.localCoefficient_sectionFromLocal pointCoefficient pointCoefficient_compatible b hp

/-- Exact zero locus of the actual native bundle section. -/
theorem pointSection_eq_zero_iff (p : RiemannSphere) :
    pointSection p = 0 ↔ p = ((1 : ℂ) : RiemannSphere) :=
  pointCoefficient_eq_zero_iff (data.indexAt p) p

theorem pointSection_ne_zero_iff (p : RiemannSphere) :
    pointSection p ≠ 0 ↔ p ≠ ((1 : ℂ) : RiemannSphere) :=
  not_congr (pointSection_eq_zero_iff p)

theorem pointSection_finite_coefficient (z : ℂ) :
    data.localCoefficient pointSection false (z : RiemannSphere) = z - 1 := by
  rw [pointSection_localCoefficient false (coe_mem_finiteChart z)]
  rfl

theorem pointSection_infinity_coefficient (w : ℂ) :
    data.localCoefficient pointSection true (RiemannSphere.infinityParametrization w) = 1 - w := by
  rw [pointSection_localCoefficient true (infinityParametrization_mem w)]
  exact congrArg (fun u : ℂ => 1 - u)
    (CanonicalGlobal.BaseTwist.infinityCoordinate_infinityParametrization w)

/-- The actual finite-chart coefficient in the coordinate centered at `1`. -/
def pointTransverseCoefficient (z : ℂ) : ℂ :=
  data.localCoefficient pointSection false (((1 + z : ℂ)) : RiemannSphere)

theorem pointTransverseCoefficient_eq : pointTransverseCoefficient = id := by
  funext z
  change data.localCoefficient pointSection false (((1 + z : ℂ)) : RiemannSphere) = z
  rw [pointSection_finite_coefficient]
  ring

theorem pointTransverseCoefficient_analyticAt : AnalyticAt ℂ pointTransverseCoefficient 0 := by
  rw [pointTransverseCoefficient_eq]
  exact analyticAt_id

/-- The zero is genuinely simple in the original sphere chart. -/
theorem pointTransverseCoefficient_order_one :
    analyticOrderAt pointTransverseCoefficient 0 = 1 := by
  rw [pointTransverseCoefficient_eq]
  exact analyticOrderAt_id

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.PowersBase
