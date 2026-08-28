import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGaugeBasic

/-!
# The actual transition identity of a native analytic isomorphism

Writing the original fibrewise linear map in two original pairs of charts
gives `t_b g^V_ab = g^W_ab t_a`. The equation is proved from actual native
linear coordinate changes, and fixes the sign of the ensuing Čech coboundary.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V W : M → Type*)
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]

/-- Multiplying by the original scalar transition changes the actual
native coordinate of any original fibre vector. -/
theorem nativeScalarTransition_mul_coordinate (i j x : M)
    (hi : x ∈ nativeCover M V i) (hj : x ∈ nativeCover M V j) (v : V x) :
    (scalarTransition V i j x : ℂ) * (nativeTriv V i).linearEquivAt ℂ x hi v =
      (nativeTriv V j).linearEquivAt ℂ x hj v := by
  rw [scalarTransition_coe, ← coordChange_apply V i j x,
    Trivialization.coe_coordChangeL _ _ ⟨hi, hj⟩]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The extracted gauge satisfies the actual native transition relation. -/
theorem isoGaugeValue_transition (e : AnalyticBundleIso I V W) (a b : M × M)
    (x : M) (hx : x ∈ isoGaugeCover M V W a ⊓ isoGaugeCover M V W b) :
    isoGaugeValue I M V W e b ⟨x, hx.2⟩ * (scalarTransition V a.1 b.1 x : ℂ) =
      (scalarTransition W a.2 b.2 x : ℂ) * isoGaugeValue I M V W e a ⟨x, hx.1⟩ := by
  let xa : isoGaugeCover M V W a := ⟨x, hx.1⟩
  let xb : isoGaugeCover M V W b := ⟨x, hx.2⟩
  let v : V x := ((nativeTriv V a.1).linearEquivAt ℂ x hx.1.1).symm 1
  have hVb : (nativeTriv V b.1).linearEquivAt ℂ x hx.2.1 v =
      (scalarTransition V a.1 b.1 x : ℂ) := by
    simpa only [v, LinearEquiv.apply_symm_apply, mul_one] using
      (nativeScalarTransition_mul_coordinate M V a.1 b.1 x hx.1.1 hx.2.1 v).symm
  have hWa : (nativeTriv W a.2).linearEquivAt ℂ x hx.1.2 (e.fiberEquiv x v) =
      isoGaugeValue I M V W e a xa := by
    simpa only [xa, v, LinearEquiv.apply_symm_apply, mul_one] using
      isoGaugeValue_coordinate I M V W e a xa v
  change isoGaugeValue I M V W e b xb * (scalarTransition V a.1 b.1 x : ℂ) =
    (scalarTransition W a.2 b.2 x : ℂ) * isoGaugeValue I M V W e a xa
  calc
    _ = isoGaugeValue I M V W e b xb *
        (nativeTriv V b.1).linearEquivAt ℂ x hx.2.1 v := by rw [hVb]
    _ = (nativeTriv W b.2).linearEquivAt ℂ x hx.2.2 (e.fiberEquiv x v) :=
      (isoGaugeValue_coordinate I M V W e b xb v).symm
    _ = (scalarTransition W a.2 b.2 x : ℂ) *
        (nativeTriv W a.2).linearEquivAt ℂ x hx.1.2 (e.fiberEquiv x v) :=
      (nativeScalarTransition_mul_coordinate M W a.2 b.2 x hx.1.2 hx.2.2
        (e.fiberEquiv x v)).symm
    _ = _ := by rw [hWa]

/-- Dividing the actual transition relation gives the original cocycle
ratio as `t_a / t_b`, fixing the required coboundary sign. -/
theorem isoGaugeValue_transition_div (e : AnalyticBundleIso I V W) (a b : M × M)
    (x : M) (hx : x ∈ isoGaugeCover M V W a ⊓ isoGaugeCover M V W b) :
    (scalarTransition V a.1 b.1 x : ℂ) / (scalarTransition W a.2 b.2 x : ℂ) =
      isoGaugeValue I M V W e a ⟨x, hx.1⟩ / isoGaugeValue I M V W e b ⟨x, hx.2⟩ := by
  apply (div_eq_div_iff (scalarTransition W a.2 b.2 x).ne_zero
    (isoGaugeValue_ne_zero I M V W e b ⟨x, hx.2⟩)).mpr
  simpa only [mul_comm] using isoGaugeValue_transition I M V W e a b x hx

end Wikipedia.HopfProblem.HolomorphicPicardNative
