import Wikipedia.NoExoticSixSphere.SphereTangentRemainderCaps

/-!
# Target-independent formula for the actual reduced resolution remainder

The actual continuous injective-operator map has one specified piecewise
formula depending only on the original source geometry, scale, and opening.
In particular, the target manifold, chart, immersion pair, normal framing,
and ambient dimension cancel. No numerical frame parity is assigned here.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction

def universalTangentRemainder (ε a : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    Vector 3 →L[ℝ] Vector 6 := by
  classical
  exact if hN : 0 ≤ (northRetainedCap.symm x).val 0 then
    northTangentRemainder ε hε ⟨northRetainedCap.symm x, (mem_north_iff _).mpr hN⟩
  else if hS : 0 ≤ (southRetainedCap.symm x).val 0 then
    southTangentRemainder ε hε ⟨southRetainedCap.symm x, (mem_north_iff _).mpr hS⟩
  else middleTangentRemainder ε a hε x

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck SphereHemisphereRetraction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : C(Sphere 3, M)) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
  (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
  (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))

theorem tangentResolutionFrameRemainder_eq_universal (x : Sphere 3) :
    (e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi x).val = universalTangentRemainder ε a hε x := by
  classical
  unfold universalTangentRemainder
  split_ifs with hN hS
  · let y : North := ⟨northRetainedCap.symm x, (mem_north_iff _).mpr hN⟩
    have hy : northRetainedCap y.val = x := northRetainedCap.apply_symm_apply x
    have h := e.tangentResolutionFrameRemainder_north ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi y
    rw [hy] at h
    exact h
  · let y : North := ⟨southRetainedCap.symm x, (mem_north_iff _).mpr hS⟩
    have hy : southRetainedCap y.val = x := southRetainedCap.apply_symm_apply x
    have h := e.tangentResolutionFrameRemainder_south ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi y
    rw [hy] at h
    exact h
  · exact e.tangentResolutionFrameRemainder_middle ν Φ F G hε ha hprod
      hleft hright hF hG hFi hGi x (le_of_not_ge hN) (le_of_not_ge hS)

theorem tangentResolutionFrameRemainder_eq_of_formula
    (R : C(Sphere 3, Monomorphism.Space 6 3))
    (hR : ∀ x, (R x).val = universalTangentRemainder ε a hε x) :
    e.tangentResolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi = R := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact (e.tangentResolutionFrameRemainder_eq_universal ν Φ F G hε ha hprod
    hleft hright hF hG hFi hGi x).trans (hR x).symm

end EuclideanEmbedding

end NoExoticSixSphere
