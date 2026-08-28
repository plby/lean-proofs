import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSphere
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleDual
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundlePullback
import Wikipedia.HopfProblem.SpecialPeriodsThreefold

/-!
# The actual inverse sphere-canonical factor and its pullback

The dual of the square infinity-ideal cocycle is identified fibrewise
with the full continuous complex-linear dual of the sphere's native
cotangent space.  The identification is induced by the proved native
canonical comparison and retains its reciprocal-chart minus sign.
Pullback uses the original sphere projection and its original analytic
atlas, with exact local-trivialization and evaluation formulas.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle

open CanonicalGlobalLineBundle
open CanonicalGlobal.SphereCanonical
open RiemannSphere.HolomorphicVectorFields

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual dual of the square ideal-line cocycle on the sphere. -/
def relativeBaseData : HolomorphicCharacterBundle.TransitionData RiemannSphere Bool :=
  dual (CanonicalGlobal.BaseTwist.data.power 2)

abbrev baseData := relativeBaseData

abbrev baseBundle := baseData.core

instance baseData_isHolomorphic : baseData.IsHolomorphic 𝓘(ℂ) := by
  unfold baseData relativeBaseData
  infer_instance

theorem baseBundle_holomorphicVectorBundle :
    ContMDiffVectorBundle ω ℂ baseBundle.Fiber 𝓘(ℂ) := inferInstance

theorem baseBundle_isManifold :
    IsManifold (𝓘(ℂ).prod 𝓘(ℂ)) ω baseBundle.TotalSpace := inferInstance

/-- The full intrinsic dual fibre, obtained by precomposing with the
actual canonical-fibre equivalence, not by assigning a line label. -/
def baseIntrinsicEquiv (p : RiemannSphere) :
    baseBundle.Fiber p ≃L[ℂ] (CotangentSpace p →L[ℂ] ℂ) :=
  (dualFiberEquiv (CanonicalGlobal.BaseTwist.data.power 2) p).trans
    ((canonicalFiberEquiv p).symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ))

@[simp] theorem baseIntrinsicEquiv_apply (p : RiemannSphere)
    (c : baseBundle.Fiber p) (α : CotangentSpace p) :
    baseIntrinsicEquiv p c α =
      dualFiberEquiv (CanonicalGlobal.BaseTwist.data.power 2) p c
        (canonicalFiberEquiv p α) := rfl

/-- Evaluation in every valid native chart, including the original sign gauge. -/
theorem baseIntrinsicEquiv_localCoefficient (b : Bool) (p : RiemannSphere)
    (hp : p ∈ baseData.baseSet b) (c : baseBundle.Fiber p) (α : CotangentSpace p) :
    baseIntrinsicEquiv p c α =
      (baseBundle.localTriv b ⟨p, c⟩).2 * (chartSign b : ℂ) *
        cotangentCoefficient b p α := by
  have hc : ((CanonicalGlobal.BaseTwist.data.power 2).core.localTriv b
      ⟨p, canonicalFiberEquiv p α⟩).2 =
      (chartSign b : ℂ) * cotangentCoefficient b p α :=
    canonicalDiffeomorph_localCoefficient b ⟨p, α⟩ hp
  exact (baseIntrinsicEquiv_apply p c α).trans
    ((dualFiberEquiv_localTriv (CanonicalGlobal.BaseTwist.data.power 2) b p c
      (canonicalFiberEquiv p α)).trans
        ((congrArg (fun a : ℂ => (baseBundle.localTriv b ⟨p, c⟩).2 * a) hc).trans
          (mul_assoc _ _ _).symm))

/-- The intrinsic functional evaluated on an actual coordinate differential frame. -/
theorem baseIntrinsicEquiv_differentialFrame (b : Bool) (p : RiemannSphere)
    (hp : p ∈ baseData.baseSet b) (c : baseBundle.Fiber p) (a : ℂ) :
    baseIntrinsicEquiv p c (cotangentFrameEquiv b p (mem_chartOpen_of_data hp) a) =
      (baseBundle.localTriv b ⟨p, c⟩).2 * (chartSign b : ℂ) * a := by
  rw [baseIntrinsicEquiv_localCoefficient b p hp, cotangentCoefficient_frame]

/-- The finite differential evaluates with sign one, the reciprocal differential with minus one. -/
theorem baseIntrinsicEquiv_mfderiv (b : Bool) (p : RiemannSphere)
    (hp : p ∈ baseData.baseSet b) (c : baseBundle.Fiber p) :
    baseIntrinsicEquiv p c (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (chartCenter b)) p) =
      (baseBundle.localTriv b ⟨p, c⟩).2 * (chartSign b : ℂ) := by
  rw [← cotangentFrameEquiv_one_eq_mfderiv b p (mem_chartOpen_of_data hp),
    baseIntrinsicEquiv_differentialFrame b p hp c 1, mul_one]

theorem baseBundle_coordChange_apply (i j : Bool) (p : RiemannSphere) (c : ℂ) :
    baseBundle.coordChange i j p c =
      ((CanonicalGlobal.BaseTwist.data.transition i j p : ℂ) ^ 2)⁻¹ * c :=
  dual_core_coordChange_apply (CanonicalGlobal.BaseTwist.data.power 2) i j p c

/-- The original inverse-square coordinate change acts on the full intrinsic dual fibre. -/
theorem baseIntrinsicEquiv_coordChange (i j : Bool) (p : RiemannSphere) (c : ℂ) :
    baseIntrinsicEquiv p (baseBundle.coordChange i j p c) =
      ((CanonicalGlobal.BaseTwist.data.transition i j p : ℂ) ^ 2)⁻¹ •
        baseIntrinsicEquiv p c := by
  rw [baseBundle_coordChange_apply]
  exact (baseIntrinsicEquiv p).map_smul _ c

/-- The genuine inverse-image cocycle along the constructed holomorphic sphere map. -/
def pullbackData : HolomorphicCharacterBundle.TransitionData Threefold.Space Bool :=
  pullback baseData Threefold.projectionSphere Threefold.projectionSphere_continuous

abbrev pullbackBundle := pullbackData.core

instance pullbackData_isHolomorphic : pullbackData.IsHolomorphic IF :=
  pullback_isHolomorphic baseData Threefold.projectionSphere
    Threefold.projectionSphere_continuous IF 𝓘(ℂ) Threefold.projectionSphere_holomorphic

theorem pullbackBundle_holomorphicVectorBundle :
    ContMDiffVectorBundle ω ℂ pullbackBundle.Fiber IF := inferInstance

theorem pullbackBundle_isManifold :
    IsManifold ((IF).prod 𝓘(ℂ)) ω pullbackBundle.TotalSpace := inferInstance

@[simp] theorem pullbackData_baseSet (b : Bool) :
    pullbackData.baseSet b = Threefold.projectionSphere ⁻¹' baseData.baseSet b := rfl

@[simp] theorem pullbackData_transition (i j : Bool) (x : Threefold.Space) :
    pullbackData.transition i j x = baseData.transition i j (Threefold.projectionSphere x) := rfl

/-- The actual pullback fibre over `x` is the original base fibre over its image. -/
def fiberPullbackEquiv (x : Threefold.Space) :
    pullbackBundle.Fiber x ≃L[ℂ] baseBundle.Fiber (Threefold.projectionSphere x) :=
  pullbackFiberEquiv baseData Threefold.projectionSphere
    Threefold.projectionSphere_continuous x

@[simp] theorem fiberPullbackEquiv_apply (x : Threefold.Space) (c : pullbackBundle.Fiber x) :
    fiberPullbackEquiv x c = id (α := ℂ) c := rfl

/-- Pullback preserves the full original local fibre coefficient. -/
theorem fiberPullbackEquiv_localCoefficient (b : Bool) (x : Threefold.Space)
    (c : pullbackBundle.Fiber x) :
    (baseBundle.localTriv b ⟨Threefold.projectionSphere x, fiberPullbackEquiv x c⟩).2 =
      (pullbackBundle.localTriv b ⟨x, c⟩).2 := rfl

theorem fiberPullbackEquiv_coordChange (i j : Bool) (x : Threefold.Space) (c : ℂ) :
    fiberPullbackEquiv x (pullbackBundle.coordChange i j x c) =
      baseBundle.coordChange i j (Threefold.projectionSphere x) (fiberPullbackEquiv x c) := rfl

/-- The native total-space map for this actual pullback. -/
def pullbackMap : pullbackBundle.TotalSpace → baseBundle.TotalSpace :=
  pullbackTotalMap baseData Threefold.projectionSphere Threefold.projectionSphere_continuous

@[simp] theorem pullbackMap_mk (x : Threefold.Space) (c : pullbackBundle.Fiber x) :
    pullbackMap ⟨x, c⟩ = ⟨Threefold.projectionSphere x, fiberPullbackEquiv x c⟩ := rfl

@[simp] theorem pullbackMap_proj (q : pullbackBundle.TotalSpace) :
    (pullbackMap q).proj = Threefold.projectionSphere q.proj := rfl

theorem pullbackMap_localTriv (b : Bool) (q : pullbackBundle.TotalSpace) :
    baseBundle.localTriv b (pullbackMap q) =
      (Threefold.projectionSphere q.proj, (pullbackBundle.localTriv b q).2) := rfl

theorem pullbackMap_holomorphic :
    ContMDiff ((IF).prod 𝓘(ℂ)) (𝓘(ℂ).prod 𝓘(ℂ)) ω pullbackMap :=
  pullbackTotalMap_holomorphic baseData Threefold.projectionSphere
    Threefold.projectionSphere_continuous IF 𝓘(ℂ) Threefold.projectionSphere_holomorphic

/-- The pulled-back inverse-canonical fibre is the full dual of the actual base cotangent fibre. -/
def pullbackIntrinsicEquiv (x : Threefold.Space) :
    pullbackBundle.Fiber x ≃L[ℂ] (CotangentSpace (Threefold.projectionSphere x) →L[ℂ] ℂ) :=
  (fiberPullbackEquiv x).trans (baseIntrinsicEquiv (Threefold.projectionSphere x))

@[simp] theorem pullbackIntrinsicEquiv_apply (x : Threefold.Space)
    (c : pullbackBundle.Fiber x) (α : CotangentSpace (Threefold.projectionSphere x)) :
    pullbackIntrinsicEquiv x c α =
      baseIntrinsicEquiv (Threefold.projectionSphere x) (fiberPullbackEquiv x c) α := rfl

theorem pullbackIntrinsicEquiv_dual_apply (x : Threefold.Space)
    (c : pullbackBundle.Fiber x) (α : CotangentSpace (Threefold.projectionSphere x)) :
    pullbackIntrinsicEquiv x c α =
      dualFiberEquiv (CanonicalGlobal.BaseTwist.data.power 2) (Threefold.projectionSphere x)
        (fiberPullbackEquiv x c) (canonicalFiberEquiv (Threefold.projectionSphere x) α) := rfl

/-- Evaluation after pullback uses the actual native total-space coefficient and sign. -/
theorem pullbackIntrinsicEquiv_localCoefficient (b : Bool) (x : Threefold.Space)
    (hx : x ∈ pullbackData.baseSet b) (c : pullbackBundle.Fiber x)
    (α : CotangentSpace (Threefold.projectionSphere x)) :
    pullbackIntrinsicEquiv x c α =
      (pullbackBundle.localTriv b ⟨x, c⟩).2 * (chartSign b : ℂ) *
        cotangentCoefficient b (Threefold.projectionSphere x) α := by
  rw [pullbackIntrinsicEquiv_apply,
    baseIntrinsicEquiv_localCoefficient b (Threefold.projectionSphere x) hx,
    fiberPullbackEquiv_localCoefficient]

theorem pullbackIntrinsicEquiv_differentialFrame (b : Bool) (x : Threefold.Space)
    (hx : x ∈ pullbackData.baseSet b) (c : pullbackBundle.Fiber x) (a : ℂ) :
    pullbackIntrinsicEquiv x c
      (cotangentFrameEquiv b (Threefold.projectionSphere x) (mem_chartOpen_of_data hx) a) =
      (pullbackBundle.localTriv b ⟨x, c⟩).2 * (chartSign b : ℂ) * a := by
  rw [pullbackIntrinsicEquiv_localCoefficient b x hx, cotangentCoefficient_frame]

theorem pullbackIntrinsicEquiv_mfderiv (b : Bool) (x : Threefold.Space)
    (hx : x ∈ pullbackData.baseSet b) (c : pullbackBundle.Fiber x) :
    pullbackIntrinsicEquiv x c
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (chartCenter b)) (Threefold.projectionSphere x)) =
      (pullbackBundle.localTriv b ⟨x, c⟩).2 * (chartSign b : ℂ) := by
  rw [← cotangentFrameEquiv_one_eq_mfderiv b (Threefold.projectionSphere x)
    (mem_chartOpen_of_data hx), pullbackIntrinsicEquiv_differentialFrame b x hx c 1, mul_one]

theorem pullbackBundle_coordChange_apply (i j : Bool) (x : Threefold.Space) (c : ℂ) :
    pullbackBundle.coordChange i j x c =
      ((CanonicalGlobal.BaseTwist.data.transition i j (Threefold.projectionSphere x) : ℂ) ^
        2)⁻¹ * c := baseBundle_coordChange_apply i j (Threefold.projectionSphere x) c

theorem pullbackIntrinsicEquiv_coordChange (i j : Bool) (x : Threefold.Space) (c : ℂ) :
    pullbackIntrinsicEquiv x (pullbackBundle.coordChange i j x c) =
      ((CanonicalGlobal.BaseTwist.data.transition i j (Threefold.projectionSphere x) : ℂ) ^
        2)⁻¹ • pullbackIntrinsicEquiv x c := by
  rw [pullbackBundle_coordChange_apply]
  exact (pullbackIntrinsicEquiv x).map_smul _ c

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle
