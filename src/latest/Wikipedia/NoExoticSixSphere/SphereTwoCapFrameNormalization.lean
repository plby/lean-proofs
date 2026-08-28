import Wikipedia.NoExoticSixSphere.HemisphereSourceReparametrization
import Wikipedia.NoExoticSixSphere.LocalizedCapFrameCoordinates
import Wikipedia.NoExoticSixSphere.SphereRetainedCapCoordinates

/-!
# Simultaneous source normalization on both retained caps

The two localized coordinate changes have disjoint supports. Both preserve
the actual operator parity. On each cap the normalized operator agrees with
the corresponding input frame precomposed by the constructed cap homeomorphism
and followed by a fixed source-coordinate change. These fixed changes retain
the pole Jacobians and preserve parity; they are not silently discarded.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere

namespace Stiefel.Monomorphism

open GLOrthonormalization SphereHemisphereRetraction SphereSumNeck

variable {N n : ℕ} (V W : North → Vector n ≃L[ℝ] Vector n)
  (hV : Continuous (fun x ↦ (V x).toContinuousLinearMap))
  (hW : Continuous (fun x ↦ (W x).toContinuousLinearMap))

def twoCapSourceRecoordinate (F : C(Sphere 3, Space N n)) : C(Sphere 3, Space N n) :=
  localizedSourceRecoordinateAlong W hW southRetainedCap
    (localizedSourceRecoordinateAlong V hV northRetainedCap F)

theorem twoCapSourceRecoordinate_north (F : C(Sphere 3, Space N n)) (x : North) :
    twoCapSourceRecoordinate V W hV hW F (northRetainedCap x.val) =
      recoordinate (ContinuousLinearEquiv.refl ℝ (Vector N))
        (basedSourceCoordinates V x) (F (northRetainedCap x.val)) := by
  unfold twoCapSourceRecoordinate
  rw [localizedSourceRecoordinateAlong_opposite W hW southRetainedCap _ _
    (southRetainedCap_opposite_north x)]
  exact localizedSourceRecoordinateAlong_cap V hV northRetainedCap F x

theorem twoCapSourceRecoordinate_south (F : C(Sphere 3, Space N n)) (x : North) :
    twoCapSourceRecoordinate V W hV hW F (southRetainedCap x.val) =
      recoordinate (ContinuousLinearEquiv.refl ℝ (Vector N))
        (basedSourceCoordinates W x) (F (southRetainedCap x.val)) := by
  unfold twoCapSourceRecoordinate
  rw [localizedSourceRecoordinateAlong_cap,
    localizedSourceRecoordinateAlong_opposite V hV northRetainedCap F _
      (northRetainedCap_opposite_south x)]

theorem sphereParityOfDimension_twoCapSourceRecoordinate
    (r : ℕ) (hN : N = 3 + (r + 2)) (hn : n = r + 2) (F : C(Sphere 3, Space N n)) :
    sphereParityOfDimension r hN hn (twoCapSourceRecoordinate V W hV hW F) =
      sphereParityOfDimension r hN hn F := by
  unfold twoCapSourceRecoordinate
  rw [sphereParityOfDimension_localizedSourceRecoordinateAlong,
    sphereParityOfDimension_localizedSourceRecoordinateAlong]

end Stiefel.Monomorphism

namespace SphereSumNeck

open GLOrthonormalization SphereHemisphereRetraction HemisphereSourceCoordinates

def northCapInverseJacobian (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    North → Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  inverseJacobian k (northCapHomeomorph ε hε) northRetainedCap
    (fun x ↦ isLocalDiffeomorphAt_northCapHomeomorph ε hε
      (half_lt_head_of_northRegion (northRetainedCap_mem_northRegion x)))

def southCapInverseJacobian (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    North → Vector (k + 3) ≃L[ℝ] Vector (k + 3) :=
  inverseJacobian k (southCapHomeomorph ε hε) southRetainedCap
    (fun x ↦ isLocalDiffeomorphAt_southCapHomeomorph ε hε
      (southRetainedCap_mem_southRegion x))

theorem continuous_northCapInverseJacobian (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x ↦ (northCapInverseJacobian k ε hε x).toContinuousLinearMap) :=
  continuous_inverseJacobian _ _ _ _

theorem continuous_southCapInverseJacobian (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun x ↦ (southCapInverseJacobian k ε hε x).toContinuousLinearMap) :=
  continuous_inverseJacobian _ _ _ _

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0 : ℝ) 1)
  (hprod : Metric.closedBall (0 : Vector 3) (ε * 4) ×ˢ
    Metric.closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε ha hprod in
theorem gluedSphere_eventuallyEq_northHomeomorph
    (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v)) (x : North) :
    gluedSphere Φ ε a F G =ᶠ[𝓝 (northRetainedCap x.val)] F ∘ northCapHomeomorph ε hε := by
  have hx := northRetainedCap_mem_northRegion x
  have hp : F ∘ northCapHomeomorph ε hε =ᶠ[𝓝 (northRetainedCap x.val)] F ∘ sphereCap ε :=
    (northCapHomeomorph_eventuallyEq ε hε hx).mono (fun _ h ↦ congrArg F h)
  exact (gluedSphere_eventuallyEq_north Φ F G hε ha hprod hleft hx).trans hp.symm

include hε ha hprod in
theorem gluedSphere_eventuallyEq_southHomeomorph
    (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v)) (x : North) :
    gluedSphere Φ ε a F G =ᶠ[𝓝 (southRetainedCap x.val)] G ∘ southCapHomeomorph ε hε := by
  have hx := southRetainedCap_mem_southRegion x
  have hp : G ∘ southCapHomeomorph ε hε =ᶠ[𝓝 (southRetainedCap x.val)]
      G ∘ (sphereCap ε ∘ reflectHead) :=
    (southCapHomeomorph_eventuallyEq ε hε hx).mono (fun _ h ↦ congrArg G h)
  exact (gluedSphere_eventuallyEq_south Φ F G hε ha hprod hright hx).trans hp.symm

end SphereSumNeck

namespace EuclideanEmbedding

open GLOrthonormalization Stiefel SphereThreeTangentFrame SphereHemisphereRetraction SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (K : C(Sphere 3, M)) (hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K)
  (hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)) (ε : ℝ) (hε : 0 < ε)

def twoCapNormalizedFrameMap :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  Monomorphism.twoCapSourceRecoordinate
    (northCapInverseJacobian (e.ambientDimension - 6) ε hε)
    (southCapInverseJacobian (e.ambientDimension - 6) ε hε)
    (continuous_northCapInverseJacobian (e.ambientDimension - 6) ε hε)
    (continuous_southCapInverseJacobian (e.ambientDimension - 6) ε hε)
    (e.sphereFrameOperatorMap ν K hK hKi)

def northCapReferenceFrameMap :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  Monomorphism.fixedSourceRecoordinate
    (northCapInverseJacobian (e.ambientDimension - 6) ε hε
      (ClosedHemisphere.center (spherePole 3))).symm
    ((e.sphereFrameOperatorMap ν K hK hKi).comp
      (northCapHomeomorph ε hε : C(Sphere 3, Sphere 3)))

def southCapReferenceFrameMap :
    C(Sphere 3, Monomorphism.Space e.ambientDimension ((e.ambientDimension - 6) + 3)) :=
  Monomorphism.fixedSourceRecoordinate
    (southCapInverseJacobian (e.ambientDimension - 6) ε hε
      (ClosedHemisphere.center (spherePole 3))).symm
    ((e.sphereFrameOperatorMap ν K hK hKi).comp
      (southCapHomeomorph ε hε : C(Sphere 3, Sphere 3)))

theorem twoCapNormalizedFrameMap_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
      (e.twoCapNormalizedFrameMap ν K hK hKi ε hε) = e.sphereDerivativeParity ν K hK hKi :=
  Monomorphism.sphereParityOfDimension_twoCapSourceRecoordinate _ _ _ _ _ _ _ _

theorem northCapReferenceFrameMap_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
      (e.northCapReferenceFrameMap ν K hK hKi ε hε) = e.sphereDerivativeParity ν K hK hKi := by
  unfold northCapReferenceFrameMap
  rw [Monomorphism.sphereParityOfDimension_fixedSourceRecoordinate,
    Monomorphism.sphereParityOfDimension_precomp_homeomorph]
  rfl

theorem southCapReferenceFrameMap_parity :
    Monomorphism.sphereParityOfDimension ((e.ambientDimension - 6) + 1)
      (by have h := e.dimension_le_ambient (K (Stiefel.pole 3)); omega) (by omega)
      (e.southCapReferenceFrameMap ν K hK hKi ε hε) = e.sphereDerivativeParity ν K hK hKi := by
  unfold southCapReferenceFrameMap
  rw [Monomorphism.sphereParityOfDimension_fixedSourceRecoordinate,
    Monomorphism.sphereParityOfDimension_precomp_homeomorph]
  rfl

theorem twoCapNormalizedFrameMap_north (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hfi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (hgerm : ∀ x : North, (K : Sphere 3 → M) =ᶠ[𝓝 (northRetainedCap x.val)]
      f ∘ northCapHomeomorph ε hε) (x : North) :
    e.twoCapNormalizedFrameMap ν K hK hKi ε hε (northRetainedCap x.val) =
      e.northCapReferenceFrameMap ν f hf hfi ε hε (northRetainedCap x.val) := by
  let V := northCapInverseJacobian (e.ambientDimension - 6) ε hε
  have hc : (e.sphereFrameOperator ν K (northRetainedCap x.val)).comp
      (V x).toContinuousLinearMap =
        e.sphereFrameOperator ν f (northCapHomeomorph ε hε (northRetainedCap x.val)) := by
    rw [e.sphereFrameOperator_eq_of_germ ν (hgerm x)]
    exact e.sphereFrameOperator_comp_cancel ν f (northCapHomeomorph ε hε)
      (northRetainedCap x.val) (hf.mdifferentiableAt (by simp)) _
  change Monomorphism.twoCapSourceRecoordinate _ _ _ _ _ (northRetainedCap x.val) = _
  rw [Monomorphism.twoCapSourceRecoordinate_north]
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun A : Vector ((e.ambientDimension - 6) + 3) →L[ℝ]
    Vector e.ambientDimension ↦ A ((V (ClosedHemisphere.center (spherePole 3))).symm v)) hc

theorem twoCapNormalizedFrameMap_south (f : C(Sphere 3, M))
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hfi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) f x))
    (hgerm : ∀ x : North, (K : Sphere 3 → M) =ᶠ[𝓝 (southRetainedCap x.val)]
      f ∘ southCapHomeomorph ε hε) (x : North) :
    e.twoCapNormalizedFrameMap ν K hK hKi ε hε (southRetainedCap x.val) =
      e.southCapReferenceFrameMap ν f hf hfi ε hε (southRetainedCap x.val) := by
  let V := southCapInverseJacobian (e.ambientDimension - 6) ε hε
  have hc : (e.sphereFrameOperator ν K (southRetainedCap x.val)).comp
      (V x).toContinuousLinearMap =
        e.sphereFrameOperator ν f (southCapHomeomorph ε hε (southRetainedCap x.val)) := by
    rw [e.sphereFrameOperator_eq_of_germ ν (hgerm x)]
    exact e.sphereFrameOperator_comp_cancel ν f (southCapHomeomorph ε hε)
      (southRetainedCap x.val) (hf.mdifferentiableAt (by simp)) _
  change Monomorphism.twoCapSourceRecoordinate _ _ _ _ _ (southRetainedCap x.val) = _
  rw [Monomorphism.twoCapSourceRecoordinate_south]
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun A : Vector ((e.ambientDimension - 6) + 3) →L[ℝ]
    Vector e.ambientDimension ↦ A ((V (ClosedHemisphere.center (spherePole 3))).symm v)) hc

end EuclideanEmbedding
end NoExoticSixSphere
