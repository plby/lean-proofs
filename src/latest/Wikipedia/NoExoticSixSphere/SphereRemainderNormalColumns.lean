import Wikipedia.NoExoticSixSphere.SphereFrameNormalColumns
import Wikipedia.NoExoticSixSphere.SphereResolutionFrameRemainder
import Wikipedia.NoExoticSixSphere.SphereRemainderBasepoint

/-!
# The frame remainder has the normal columns at its actual basepoint

Two matching cap exchanges preserve any pointwise relation between the
corresponding input maps. Apply this to the exact normal-column identities
of the normalized frame and both reference frames. The resulting remainder
has the original normal frame at the constructed chart-contained basepoint.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace HemisphereExchange

open SphereHemisphereRetraction SphereSumNeck

theorem twoCapRemainder_rel {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (R : Y → Z → Prop) (Q F G : C(Sphere 3, Y)) (Q' F' G' : C(Sphere 3, Z))
    (hN : ∀ x : North, Q (northRetainedCap x.val) = F (northRetainedCap x.val))
    (hS : ∀ x : North, Q (southRetainedCap x.val) = G (southRetainedCap x.val))
    (hN' : ∀ x : North, Q' (northRetainedCap x.val) = F' (northRetainedCap x.val))
    (hS' : ∀ x : North, Q' (southRetainedCap x.val) = G' (southRetainedCap x.val))
    (hQ : ∀ x, R (Q x) (Q' x)) (hF : ∀ x, R (F x) (F' x)) (hG : ∀ x, R (G x) (G' x))
    (x : Sphere 3) : R (twoCapRemainder Q F G hN hS x) (twoCapRemainder Q' F' G' hN' hS' x) := by
  by_cases hn : 0 ≤ (northRetainedCap.symm x).val 0
  · let y : North := ⟨northRetainedCap.symm x, (mem_north_iff _).mpr hn⟩
    have he : northRetainedCap y.val = x := northRetainedCap.apply_symm_apply x
    rw [← he, twoCapRemainder_north, twoCapRemainder_north]
    exact hF _
  · by_cases hs : 0 ≤ (southRetainedCap.symm x).val 0
    · let y : North := ⟨southRetainedCap.symm x, (mem_north_iff _).mpr hs⟩
      have he : southRetainedCap y.val = x := southRetainedCap.apply_symm_apply x
      rw [← he, twoCapRemainder_south, twoCapRemainder_south]
      exact hG _
    · rw [twoCapRemainder_middle Q F G hN hS x (le_of_not_ge hn) (le_of_not_ge hs),
        twoCapRemainder_middle Q' F' G' hN' hS' x (le_of_not_ge hn) (le_of_not_ge hs)]
      exact hQ x

end HemisphereExchange

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereSumNeck HemisphereExchange

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

theorem resolutionFrameRemainder_normal (x : Sphere 3) (v : Vector (e.ambientDimension - 6)) :
    (e.resolutionFrameRemainder ν Φ F G hε ha hprod hleft hright hF hG hFi hGi x).val
        (EuclideanSpace.finAddEquivProd.symm (v, (0 : Vector 3))) =
      (ν.orthonormal
        (remainderBasepoint Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG x)).val v := by
  let K := gluedSphereMap Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  have hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K :=
    contMDiff_gluedSphere Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft hright hF hG
  have hKi : ∀ y, Injective (mfderiv (𝓡 3) (𝓡 6) K y) :=
    injective_mfderiv_gluedSphere Φ F G hε hprod ha hleft hright hF hG hFi hGi
  have hN := gluedSphere_eventuallyEq_northHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hleft
  have hS := gluedSphere_eventuallyEq_southHomeomorph Φ F G hε ⟨ha.1.le, ha.2⟩ hprod hright
  exact twoCapRemainder_rel
    (fun (A : Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) (p : M) ↦
      ∀ w : Vector (e.ambientDimension - 6),
        A.val (EuclideanSpace.finAddEquivProd.symm (w, (0 : Vector 3))) =
          (ν.orthonormal p).val w)
    (e.twoCapNormalizedFrameMap ν K hK hKi ε hε)
    (e.northCapReferenceFrameMap ν F hF hFi ε hε)
    (e.southCapReferenceFrameMap ν G hG hGi ε hε)
    K (F.comp (northCapHomeomorph ε hε : C(Sphere 3, Sphere 3)))
    (G.comp (southCapHomeomorph ε hε : C(Sphere 3, Sphere 3)))
    (e.twoCapNormalizedFrameMap_north ν K hK hKi ε hε F hF hFi hN)
    (e.twoCapNormalizedFrameMap_south ν K hK hKi ε hε G hG hGi hS)
    (fun y ↦ (hN y).eq_of_nhds) (fun y ↦ (hS y).eq_of_nhds)
    (e.twoCapNormalizedFrameMap_normal ν K hK hKi ε hε)
    (e.northCapReferenceFrameMap_normal ν F hF hFi ε hε)
    (e.southCapReferenceFrameMap_normal ν G hG hGi ε hε) x v

end EuclideanEmbedding
end NoExoticSixSphere
