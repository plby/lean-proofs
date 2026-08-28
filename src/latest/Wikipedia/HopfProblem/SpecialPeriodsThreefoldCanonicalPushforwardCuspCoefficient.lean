import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardCuspFrame
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGenericRatioBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsNative

/-!
# Descent and vanishing of an arbitrary canonical coefficient at the cusp

An arbitrary holomorphic section of the original canonical bundle can
be divided by the actual full-cusp unit frame. This gives a genuine
holomorphic function on the full inverse image of a base open, hence
descends by the proved holomorphic-function direct-image isomorphism.
Multiplication by the literal reciprocal coordinate gives its coefficient
relative to the original regular canonical form. The coefficient is
holomorphic across infinity and vanishes there.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The genuine holomorphic function obtained by dividing by the native cusp frame. -/
def nativeRatio (U : Opens RiemannSphere) (s : PreimageSection U) :
    Threefold.PreimageSection (localBase U) :=
  NativeBundleSections.ratioSection bundle IF (Threefold.basePreimage (localBase U))
    (restrictedSection U s) (frame U) (frame_ne_zero U)

theorem nativeRatio_smul_frame (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (localBase U)) :
    nativeRatio U s x • frame U x = s (sourcePoint U x) :=
  NativeBundleSections.ratio_smul bundle IF (Threefold.basePreimage (localBase U))
    (restrictedSection U s) (frame U) (frame_ne_zero U) x

/-- Descent uses the actual inverse of holomorphic pullback on the full inverse image. -/
def descendedRatio (U : Opens RiemannSphere) (s : PreimageSection U) :
    Threefold.BaseSection (localBase U) :=
  (Threefold.pullbackSectionEquiv (localBase U)).symm (nativeRatio U s)

theorem descendedRatio_projection (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (localBase U)) :
    descendedRatio U s (Threefold.baseProjection (localBase U) x) = nativeRatio U s x := by
  have h := (Threefold.pullbackSectionEquiv (localBase U)).apply_symm_apply (nativeRatio U s)
  exact congrArg (fun f : Threefold.PreimageSection (localBase U) => f x) h

theorem descendedRatio_smul_frame (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (localBase U)) :
    descendedRatio U s (Threefold.baseProjection (localBase U) x) • frame U x =
      s (sourcePoint U x) := by
  rw [descendedRatio_projection]
  exact nativeRatio_smul_frame U s x

/-- The actual coefficient of the original regular form, holomorphic across the cusp value. -/
def localCoefficient (U : Opens RiemannSphere) (s : PreimageSection U) :
    Threefold.BaseSection (localBase U) :=
  reciprocalSection U * descendedRatio U s

@[simp] theorem localCoefficient_apply (U : Opens RiemannSphere) (s : PreimageSection U)
    (p : localBase U) :
    localCoefficient U s p = reciprocalSection U p * descendedRatio U s p := rfl

theorem localCoefficient_holomorphic (U : Opens RiemannSphere) (s : PreimageSection U) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (localCoefficient U s) :=
  (localCoefficient U s).contMDiff

/-- Every holomorphic canonical section has a coefficient vanishing at the actual infinity. -/
theorem localCoefficient_infty {U : Opens RiemannSphere} (s : PreimageSection U)
    (hU : (∞ : RiemannSphere) ∈ U) :
    localCoefficient U s ⟨∞, infty_mem_localBase hU⟩ = 0 := by
  rw [localCoefficient_apply, reciprocalSection_infty hU, zero_mul]

/-- This coefficient really represents the arbitrary section in the original canonical fibres. -/
theorem localCoefficient_smul_regular (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (localBase U)) (hx : x.val ∈ Threefold.regularLocus) :
    localCoefficient U s (Threefold.baseProjection (localBase U) x) •
      GlobalRegular.globalSection ⟨x.val, hx⟩ = s (sourcePoint U x) := by
  have h := descendedRatio_smul_frame U s x
  rw [frame_regular U x hx, smul_smul] at h
  rw [localCoefficient_apply, mul_comm]
  exact h

theorem localCoefficient_smul_of_ne_infty (U : Opens RiemannSphere) (s : PreimageSection U)
    (x : Threefold.basePreimage (localBase U))
    (hx : Threefold.projectionSphere x.val ≠ (∞ : RiemannSphere)) :
    localCoefficient U s (Threefold.baseProjection (localBase U) x) •
      GlobalRegular.globalSection ⟨x.val, regular_of_projection_ne_infty U x hx⟩ =
        s (sourcePoint U x) :=
  localCoefficient_smul_regular U s x (regular_of_projection_ne_infty U x hx)

/-- The requested local extension is unconditional for every genuine native canonical section. -/
theorem exists_coefficient_near_infty (U : Opens RiemannSphere) (s : PreimageSection U)
    (hU : (∞ : RiemannSphere) ∈ U) :
    ∃ (V : Opens RiemannSphere) (hVU : V ≤ U) (hV : (∞ : RiemannSphere) ∈ V),
      ∃ h : Threefold.BaseSection V, h ⟨∞, hV⟩ = 0 ∧
        ∀ (x : Threefold.basePreimage V) (hx : x.val ∈ Threefold.regularLocus),
          h (Threefold.baseProjection V x) • GlobalRegular.globalSection ⟨x.val, hx⟩ =
            s ⟨x.val, Threefold.basePreimage_mono hVU x.property⟩ := by
  refine ⟨localBase U, localBase_le U, infty_mem_localBase hU,
    localCoefficient U s, localCoefficient_infty s hU, ?_⟩
  intro x hx
  exact localCoefficient_smul_regular U s x hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Cusp
