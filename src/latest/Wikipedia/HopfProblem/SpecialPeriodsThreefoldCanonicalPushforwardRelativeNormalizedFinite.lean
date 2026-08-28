import
  Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeNormalizedContraction

/-!
# The literal finite formula for the normalized relative canonical section

On every finite base point the transported section is exactly the
original normalized three-form tensored with the pulled-back inverse
finite-coordinate differential.  The identity holds also on the second
elliptic zero fibre; no cancellation by that vanishing form is used.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold OnePoint TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual finite-chart unit frame of the pulled-back dual sphere-cotangent line. -/
def finitePulledFrame (x : Threefold.Space) : RelativeBundle.pullbackBundle.Fiber x :=
  TensorLocal.pulledFrame RelativeBundle.baseData Threefold.projectionSphere
    Threefold.projectionSphere_continuous false x

/-- Exact finite normalization on every original subopen of the finite sphere chart. -/
theorem normalizedSection_finite_open (U : Opens RiemannSphere) (hU : U ≤ finiteChart)
    (x : Threefold.basePreimage U) :
    normalizedSection U x = RelativeBundle.nativeTensorEquiv x.val
      (GlobalMeromorphicSection.rawSection x.val ⊗ₜ[ℂ]
        TensorLocal.pulledFrame RelativeBundle.baseData Threefold.projectionSphere
          Threefold.projectionSphere_continuous false x.val) := by
  let e := TensorLocal.unTensorFiberEquiv NativePresentation.transitionData
    RelativeBundle.baseData Threefold.projectionSphere
      Threefold.projectionSphere_continuous false x.val
  have he : e (normalizedSection U x) =
      NativePresentation.fiberEquiv x.val (GlobalMeromorphicSection.rawSection x.val) :=
    normalizedSection_sourceContraction_finite_value U hU x
  have h₁ := (e.symm_apply_apply (normalizedSection U x)).symm.trans (congrArg e.symm he)
  have h₂ : e.symm (NativePresentation.fiberEquiv x.val
        (GlobalMeromorphicSection.rawSection x.val)) = RelativeBundle.fiberTensorEquiv x.val
        ((NativePresentation.fiberEquiv x.val (GlobalMeromorphicSection.rawSection x.val)) ⊗ₜ[ℂ]
          finitePulledFrame x.val) :=
    TensorLocal.unTensorFiberEquiv_symm NativePresentation.transitionData
      RelativeBundle.baseData Threefold.projectionSphere
        Threefold.projectionSphere_continuous false x.val (hU x.property) _
  exact h₁.trans (h₂.trans (RelativeBundle.nativeTensorEquiv_tmul x.val
    (GlobalMeromorphicSection.rawSection x.val) (finitePulledFrame x.val)).symm)

/-- The formula holds at every finite point of an arbitrary original base open. -/
theorem normalizedSection_finite (U : Opens RiemannSphere) (x : Threefold.basePreimage U)
    (hx : Threefold.projectionSphere x.val ≠ (∞ : RiemannSphere)) :
    normalizedSection U x = RelativeBundle.nativeTensorEquiv x.val
      (GlobalMeromorphicSection.rawSection x.val ⊗ₜ[ℂ]
        TensorLocal.pulledFrame RelativeBundle.baseData Threefold.projectionSphere
          Threefold.projectionSphere_continuous false x.val) := by
  let V : Opens RiemannSphere := U ⊓ finiteChart
  let y : Threefold.basePreimage V :=
    ⟨x.val, ⟨x.property, (mem_finiteChart _).mpr hx⟩⟩
  have h := congrArg (fun s : Section V => s y)
    (normalizedSection_restrict (U := V) (V := U) inf_le_left)
  exact h.trans (normalizedSection_finite_open V inf_le_right y)

/-- The global actual relative section has the same literal finite normalization. -/
theorem normalizedGlobalSection_finite (x : Threefold.Space)
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    normalizedGlobalSection ⟨x, trivial⟩ = RelativeBundle.nativeTensorEquiv x
      (GlobalMeromorphicSection.rawSection x ⊗ₜ[ℂ] finitePulledFrame x) :=
  normalizedSection_finite ⊤ ⟨x, trivial⟩ hx

/-- This is a genuine native unit frame on exactly the finite chart preimage. -/
theorem finitePulledFrame_localCoefficient (x : Threefold.Space)
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    (RelativeBundle.pullbackBundle.localTriv false ⟨x, finitePulledFrame x⟩).2 = 1 :=
  congrArg Prod.snd (OpenMaps.localFrame_localTriv RelativeBundle.baseData false
    ((mem_finiteChart _).mpr hx))

/-- The dual frame evaluates an arbitrary actual cotangent vector in its finite coordinate. -/
theorem finitePulledFrame_cotangentCoefficient (x : Threefold.Space)
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere))
    (α : CanonicalGlobal.SphereCanonical.CotangentSpace (Threefold.projectionSphere x)) :
    RelativeBundle.pullbackIntrinsicEquiv x (finitePulledFrame x) α =
      CanonicalGlobal.SphereCanonical.cotangentCoefficient false
        (Threefold.projectionSphere x) α := by
  have hp : x ∈ RelativeBundle.pullbackData.baseSet false := (mem_finiteChart _).mpr hx
  have h := RelativeBundle.pullbackIntrinsicEquiv_localCoefficient false x hp
    (finitePulledFrame x) α
  rw [finitePulledFrame_localCoefficient x hx, CanonicalGlobal.SphereCanonical.chartSign_false,
    Units.val_one, one_mul, one_mul] at h
  exact h

/-- In particular the frame is the inverse of the actual finite-coordinate differential. -/
theorem finitePulledFrame_mfderiv (x : Threefold.Space)
    (hx : Threefold.projectionSphere x ≠ (∞ : RiemannSphere)) :
    RelativeBundle.pullbackIntrinsicEquiv x (finitePulledFrame x)
      (mfderiv 𝓘(ℂ) 𝓘(ℂ)
        (chartAt ℂ (RiemannSphere.HolomorphicVectorFields.chartCenter false))
          (Threefold.projectionSphere x)) = 1 := by
  have hp : x ∈ RelativeBundle.pullbackData.baseSet false := (mem_finiteChart _).mpr hx
  have h := RelativeBundle.pullbackIntrinsicEquiv_mfderiv false x hp (finitePulledFrame x)
  rw [finitePulledFrame_localCoefficient x hx, CanonicalGlobal.SphereCanonical.chartSign_false,
    Units.val_one, one_mul] at h
  exact h

/-- The normalization is preserved on the entire intrinsic covector tensor fibre. -/
theorem normalizedSection_intrinsic_finite (U : Opens RiemannSphere)
    (x : Threefold.basePreimage U)
    (hx : Threefold.projectionSphere x.val ≠ (∞ : RiemannSphere)) :
    RelativeBundle.fiberIntrinsicEquiv x.val (normalizedSection U x) =
      Threefold.Canonical.intrinsicEquiv x.val (GlobalMeromorphicSection.rawSection x.val) ⊗ₜ[ℂ]
        RelativeBundle.pullbackIntrinsicEquiv x.val (finitePulledFrame x.val) :=
  (congrArg (RelativeBundle.fiberIntrinsicEquiv x.val) (normalizedSection_finite U x hx)).trans
    (RelativeBundle.fiberIntrinsicEquiv_native_tmul x.val
      (GlobalMeromorphicSection.rawSection x.val) (finitePulledFrame x.val))

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
