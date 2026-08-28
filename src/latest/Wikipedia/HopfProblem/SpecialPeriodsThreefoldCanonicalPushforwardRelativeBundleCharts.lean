import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeBundleIntrinsic

/-!
# Actual intrinsic chart coordinates of the relative canonical bundle

Both factors are changed by their genuine native chart maps: the full
three-covector is pulled back by the actual tangent chart differential,
and the dual cotangent functional is precomposed with the actual sphere
coordinate differential frame.  Their tensor product agrees with the
original relative-bundle local trivialization on the entire fibre.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle

open TrianglePeriodFamily.Canonical
open CanonicalGlobal.SphereCanonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

/-- The full tensor product of the two native model covector spaces. -/
abbrev CoordinateFiber := TopCovector ⊗[ℂ] (ℂ →L[ℂ] ℂ)

/-- Pullback by the actual threefold tangent coordinate change. -/
def topChartMap (i : atlas Model Threefold.Space) (x : Threefold.Space) :
    Threefold.Canonical.IntrinsicTopCovector x →ₗ[ℂ] TopCovector :=
  ContinuousAlternatingMap.compContinuousLinearMapₗ
    ((tangentBundleCore IF Threefold.Space).coordChange i (achart Model x) x)

@[simp] theorem topChartMap_apply (i : atlas Model Threefold.Space) (x : Threefold.Space)
    (α : Threefold.Canonical.IntrinsicTopCovector x) :
    topChartMap i x α = α.compContinuousLinearMap
      ((tangentBundleCore IF Threefold.Space).coordChange i (achart Model x) x) := rfl

/-- This is the literal derivative of the original chart transition. -/
theorem topChartMap_eq_fderiv (i : atlas Model Threefold.Space) (x : Threefold.Space)
    (α : Threefold.Canonical.IntrinsicTopCovector x) :
    topChartMap i x α =
      α.compContinuousLinearMap (fderiv ℂ (chartAt Model x ∘ i.val.symm) (i.val x)) :=
  congrArg (fun L : Model →L[ℂ] Model => α.compContinuousLinearMap L)
    (Atlas.tangentCore_coordChange Threefold.Space i (achart Model x) x)

/-- The actual transition presentation preserves the original top-covector coordinates. -/
theorem topChartMap_dataIntrinsicEquiv (i : atlas Model Threefold.Space)
    (x : Threefold.Space) (hx : x ∈ i.val.source)
    (a : NativePresentation.transitionBundle.Fiber x) :
    topChartMap i x (NativePresentation.dataIntrinsicEquiv x a) =
      NativePresentation.dataInCoordinates i x a :=
  (NativePresentation.dataInCoordinates_eq_intrinsic_pullback i hx a).symm

theorem topChartMap_nativeIntrinsicEquiv (i : atlas Model Threefold.Space)
    (x : Threefold.Space) (a : Threefold.Canonical.bundle.Fiber x) :
    topChartMap i x (Threefold.Canonical.intrinsicEquiv x a) =
      Threefold.Canonical.inCoordinates i x a :=
  (Threefold.Canonical.inCoordinates_eq_intrinsic_pullback i x a).symm

/-- A functional on the actual sphere cotangent fibre is read in its actual differential frame. -/
def baseChartMap (b : Bool) (x : Threefold.Space) (hx : x ∈ pullbackData.baseSet b) :
    (CotangentSpace (Threefold.projectionSphere x) →L[ℂ] ℂ) →ₗ[ℂ] (ℂ →L[ℂ] ℂ) where
  toFun ℓ := ℓ.comp (cotangentFrameEquiv b (Threefold.projectionSphere x)
    (mem_chartOpen_of_data hx)).toContinuousLinearMap
  map_add' _ _ := by
    apply ContinuousLinearMap.ext
    intro c
    rfl
  map_smul' _ _ := by
    apply ContinuousLinearMap.ext
    intro c
    rfl

@[simp] theorem baseChartMap_apply (b : Bool) (x : Threefold.Space)
    (hx : x ∈ pullbackData.baseSet b)
    (ℓ : CotangentSpace (Threefold.projectionSphere x) →L[ℂ] ℂ) (c : ℂ) :
    baseChartMap b x hx ℓ c =
      ℓ (cotangentFrameEquiv b (Threefold.projectionSphere x) (mem_chartOpen_of_data hx) c) :=
  rfl

/-- The actual reciprocal differential contributes its proved minus sign. -/
theorem baseChartMap_pullbackIntrinsicEquiv (b : Bool) (x : Threefold.Space)
    (hx : x ∈ pullbackData.baseSet b) (c : pullbackBundle.Fiber x) :
    baseChartMap b x hx (pullbackIntrinsicEquiv x c) =
      ((pullbackBundle.localTriv b ⟨x, c⟩).2 * (chartSign b : ℂ)) •
        ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext
  intro a
  exact pullbackIntrinsicEquiv_differentialFrame b x hx c a

/-- The complete intrinsic chart map is the tensor of the two genuine chart maps. -/
def intrinsicCoordinates (i : Index) (x : Threefold.Space) (hx : x ∈ data.baseSet i) :
    IntrinsicFiber x →ₗ[ℂ] CoordinateFiber :=
  TensorProduct.map (topChartMap i.1 x) (baseChartMap i.2 x hx.2)

@[simp] theorem intrinsicCoordinates_tmul (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) (α : Threefold.Canonical.IntrinsicTopCovector x)
    (ℓ : CotangentSpace (Threefold.projectionSphere x) →L[ℂ] ℂ) :
    intrinsicCoordinates i x hx (α ⊗ₜ[ℂ] ℓ) =
      topChartMap i.1 x α ⊗ₜ[ℂ] baseChartMap i.2 x hx.2 ℓ :=
  TensorProduct.map_tmul _ _ _ _

/-- Actual relative-bundle coordinates, as a linear map on its whole native fibre. -/
def inCoordinates (i : Index) (x : Threefold.Space) (hx : x ∈ data.baseSet i) :
    bundle.Fiber x →ₗ[ℂ] CoordinateFiber :=
  (intrinsicCoordinates i x hx).comp (fiberIntrinsicEquiv x).toLinearMap

theorem inCoordinates_fiberTensorEquiv_tmul (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) (a : NativePresentation.transitionBundle.Fiber x)
    (b : pullbackBundle.Fiber x) :
    inCoordinates i x hx (fiberTensorEquiv x (a ⊗ₜ[ℂ] b)) =
      NativePresentation.dataInCoordinates i.1 x a ⊗ₜ[ℂ]
        (((pullbackBundle.localTriv i.2 ⟨x, b⟩).2 * (chartSign i.2 : ℂ)) •
          ContinuousLinearMap.id ℂ ℂ) := by
  change intrinsicCoordinates i x hx
    (fiberIntrinsicEquiv x (fiberTensorEquiv x (a ⊗ₜ[ℂ] b))) = _
  rw [fiberIntrinsicEquiv_tmul, intrinsicCoordinates_tmul,
    topChartMap_dataIntrinsicEquiv i.1 x hx.1, baseChartMap_pullbackIntrinsicEquiv]

theorem inCoordinates_nativeTensorEquiv_tmul (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) (a : Threefold.Canonical.bundle.Fiber x)
    (b : pullbackBundle.Fiber x) :
    inCoordinates i x hx (nativeTensorEquiv x (a ⊗ₜ[ℂ] b)) =
      Threefold.Canonical.inCoordinates i.1 x a ⊗ₜ[ℂ]
        (((pullbackBundle.localTriv i.2 ⟨x, b⟩).2 * (chartSign i.2 : ℂ)) •
          ContinuousLinearMap.id ℂ ℂ) := by
  change intrinsicCoordinates i x hx
    (fiberIntrinsicEquiv x (nativeTensorEquiv x (a ⊗ₜ[ℂ] b))) = _
  rw [fiberIntrinsicEquiv_native_tmul, intrinsicCoordinates_tmul,
    topChartMap_nativeIntrinsicEquiv, baseChartMap_pullbackIntrinsicEquiv]

/-- The standard frame is a genuine tensor of full model covectors. -/
def coordinateFrame : CoordinateFiber := volume ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ ℂ

/-- The native sphere sign gauge, as a linear map on the full scalar coordinate. -/
def signedFrameMap (b : Bool) : ℂ →ₗ[ℂ] CoordinateFiber :=
  (chartSign b : ℂ) • LinearMap.toSpanSingleton ℂ CoordinateFiber coordinateFrame

@[simp] theorem signedFrameMap_apply (b : Bool) (c : ℂ) :
    signedFrameMap b c = ((chartSign b : ℂ) * c) • coordinateFrame := by
  change (chartSign b : ℂ) • (c • coordinateFrame) = _
  rw [smul_smul]

theorem fiberTensorEquiv_localCoefficient (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) (a : NativePresentation.transitionBundle.Fiber x)
    (b : pullbackBundle.Fiber x) :
    (bundle.localTriv i ⟨x, fiberTensorEquiv x (a ⊗ₜ[ℂ] b)⟩).2 =
      (NativePresentation.transitionBundle.localTriv i.1 ⟨x, a⟩).2 *
        (pullbackBundle.localTriv i.2 ⟨x, b⟩).2 := by
  have h := congrArg (fun L => L (a ⊗ₜ[ℂ] b)) (fiberTensorEquiv_localTriv i x hx)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.map_tmul, TensorProduct.lid_tmul, smul_eq_mul] at h
  rw [Trivialization.coe_linearMapAt_of_mem _ hx,
    Trivialization.coe_linearMapAt_of_mem _ hx.1,
    Trivialization.coe_linearMapAt_of_mem _ hx.2] at h
  exact h

/-- Full linear-map compatibility with the original relative-bundle local trivialization. -/
theorem inCoordinates_eq_localTriv (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) :
    inCoordinates i x hx =
      (signedFrameMap i.2).comp ((bundle.localTriv i).linearMapAt ℂ x) := by
  have ht : (inCoordinates i x hx).comp (fiberTensorEquiv x).toLinearMap =
      ((signedFrameMap i.2).comp ((bundle.localTriv i).linearMapAt ℂ x)).comp
        (fiberTensorEquiv x).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    rw [inCoordinates_fiberTensorEquiv_tmul,
      Trivialization.coe_linearMapAt_of_mem _ hx, signedFrameMap_apply]
    dsimp only
    rw [fiberTensorEquiv_localCoefficient i x hx]
    change (((NativePresentation.transitionBundle.localTriv i.1 ⟨x, a⟩).2 • volume) ⊗ₜ[ℂ]
      (((pullbackBundle.localTriv i.2 ⟨x, b⟩).2 * (chartSign i.2 : ℂ)) •
        ContinuousLinearMap.id ℂ ℂ)) = _
    rw [TensorProduct.smul_tmul_smul]
    change (_ * (_ * _)) • coordinateFrame = (_ * (_ * _)) • coordinateFrame
    congr 1
    ring
  apply LinearMap.ext
  intro v
  obtain ⟨t, rfl⟩ := (fiberTensorEquiv x).surjective v
  exact DFunLike.congr_fun ht t

/-- Every vector, not merely every elementary tensor, has its actual signed native coefficient. -/
theorem inCoordinates_localTriv (i : Index) (x : Threefold.Space)
    (hx : x ∈ data.baseSet i) (v : bundle.Fiber x) :
    inCoordinates i x hx v =
      ((chartSign i.2 : ℂ) * (bundle.localTriv i ⟨x, v⟩).2) •
        (volume ⊗ₜ[ℂ] ContinuousLinearMap.id ℂ ℂ) := by
  rw [inCoordinates_eq_localTriv, LinearMap.comp_apply,
    Trivialization.coe_linearMapAt_of_mem _ hx, signedFrameMap_apply]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.RelativeBundle
