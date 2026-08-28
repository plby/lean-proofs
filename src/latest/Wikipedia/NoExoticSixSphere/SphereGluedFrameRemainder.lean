import Wikipedia.NoExoticSixSphere.SphereFrameCapPeeling
import Wikipedia.NoExoticSixSphere.SphereTwoCapFrameNormalization

/-!
# A constructed remainder after removing both input frame contributions

Successive actual cap exchanges remove the two input frame maps, leaving
a specified continuous injective-operator sphere map. The resulting parity
decomposition is proved, not assumed. Identifying the remainder's parity
with the Whitney reference is a separate, still missing geometric step.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace HemisphereExchange

open SphereHemisphereRetraction SphereSumNeck

variable {Y : Type*} [TopologicalSpace Y] (Q F G : C(Sphere 3, Y))
  (hN : ∀ x : North, Q (northRetainedCap x.val) = F (northRetainedCap x.val))
  (hS : ∀ x : North, Q (southRetainedCap x.val) = G (southRetainedCap x.val))

include hS in
theorem northPeel_agrees_south (x : North) :
    peelCap Q F northRetainedCap hN (southRetainedCap x.val) = G (southRetainedCap x.val) := by
  rw [peelCap_of_inverse_head_nonpos Q F northRetainedCap hN _
    ((northRetainedCap_opposite_south x).trans (by norm_num))]
  exact hS x

def twoCapRemainder : C(Sphere 3, Y) :=
  peelCap (peelCap Q F northRetainedCap hN) G southRetainedCap
    (northPeel_agrees_south Q F G hN hS)

theorem twoCapRemainder_north (x : North) :
    twoCapRemainder Q F G hN hS (northRetainedCap x.val) =
      F (northRetainedCap (reflectHead x.val)) := by
  unfold twoCapRemainder
  rw [peelCap_of_inverse_head_nonpos _ G southRetainedCap _ _
    ((southRetainedCap_opposite_north x).trans (by norm_num))]
  exact peelCap_north Q F northRetainedCap hN x

theorem twoCapRemainder_south (x : North) :
    twoCapRemainder Q F G hN hS (southRetainedCap x.val) =
      G (southRetainedCap (reflectHead x.val)) :=
  peelCap_north _ G southRetainedCap _ x

theorem twoCapRemainder_middle (x : Sphere 3)
    (hxN : (northRetainedCap.symm x).val 0 ≤ 0)
    (hxS : (southRetainedCap.symm x).val 0 ≤ 0) :
    twoCapRemainder Q F G hN hS x = Q x := by
  unfold twoCapRemainder
  rw [peelCap_of_inverse_head_nonpos _ G southRetainedCap _ x hxS,
    peelCap_of_inverse_head_nonpos Q F northRetainedCap hN x hxN]

end HemisphereExchange

namespace Stiefel.Monomorphism

open GLOrthonormalization HemisphereExchange SphereHemisphereRetraction SphereSumNeck

theorem sphereParityOfDimension_twoCapRemainder {N n : ℕ}
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2)
    (Q F G : C(Sphere 3, Space N n))
    (hcapN : ∀ x : North, Q (northRetainedCap x.val) = F (northRetainedCap x.val))
    (hcapS : ∀ x : North, Q (southRetainedCap x.val) = G (southRetainedCap x.val)) :
    sphereParityOfDimension r hN hn Q =
      sphereParityOfDimension r hN hn F + sphereParityOfDimension r hN hn G +
        sphereParityOfDimension r hN hn (twoCapRemainder Q F G hcapN hcapS) := by
  calc
    _ = sphereParityOfDimension r hN hn F +
        sphereParityOfDimension r hN hn (peelCap Q F northRetainedCap hcapN) :=
      sphereParityOfDimension_peelCap r hN hn Q F northRetainedCap hcapN
    _ = sphereParityOfDimension r hN hn F + (sphereParityOfDimension r hN hn G +
        sphereParityOfDimension r hN hn (twoCapRemainder Q F G hcapN hcapS)) :=
      congrArg (sphereParityOfDimension r hN hn F + ·)
        (sphereParityOfDimension_peelCap r hN hn _ G southRetainedCap
          (northPeel_agrees_south Q F G hcapN hcapS))
    _ = _ := (add_assoc _ _ _).symm

end Stiefel.Monomorphism

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel HemisphereExchange SphereHemisphereRetraction SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (K F G : C(Sphere 3, M))
  (hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K) (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
  (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
  (hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x))
  (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
  (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
  (ε : ℝ) (hε : 0 < ε)
  (hcapN : ∀ x : North, (K : Sphere 3 → M) =ᶠ[𝓝 (northRetainedCap x.val)]
    F ∘ northCapHomeomorph ε hε)
  (hcapS : ∀ x : North, (K : Sphere 3 → M) =ᶠ[𝓝 (southRetainedCap x.val)]
    G ∘ southCapHomeomorph ε hε)

def gluedFrameRemainder :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  twoCapRemainder (e.twoCapNormalizedFrameMap ν K hK hKi ε hε)
    (e.northCapReferenceFrameMap ν F hF hFi ε hε)
    (e.southCapReferenceFrameMap ν G hG hGi ε hε)
    (e.twoCapNormalizedFrameMap_north ν K hK hKi ε hε F hF hFi hcapN)
    (e.twoCapNormalizedFrameMap_south ν K hK hKi ε hε G hG hGi hcapS)

theorem sphereDerivativeParity_eq_inputs_add_remainder :
    e.sphereDerivativeParity ν K hK hKi =
      e.sphereDerivativeParity ν F hF hFi + e.sphereDerivativeParity ν G hG hGi +
        Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
          (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
          (e.gluedFrameRemainder ν K F G hK hF hG hKi hFi hGi ε hε hcapN hcapS) := by
  have h := Monomorphism.sphereParityOfDimension_twoCapRemainder
    ((e.ambientDimension - 6) + 1)
    (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
    (e.twoCapNormalizedFrameMap ν K hK hKi ε hε)
    (e.northCapReferenceFrameMap ν F hF hFi ε hε)
    (e.southCapReferenceFrameMap ν G hG hGi ε hε)
    (e.twoCapNormalizedFrameMap_north ν K hK hKi ε hε F hF hFi hcapN)
    (e.twoCapNormalizedFrameMap_south ν K hK hKi ε hε G hG hGi hcapS)
  rw [e.twoCapNormalizedFrameMap_parity, e.northCapReferenceFrameMap_parity,
    e.southCapReferenceFrameMap_parity] at h
  exact h

end EuclideanEmbedding
end NoExoticSixSphere
