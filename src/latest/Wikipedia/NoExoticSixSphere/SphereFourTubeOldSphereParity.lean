import Wikipedia.NoExoticSixSphere.SphereFourTubeOldZeroFrame
import Wikipedia.NoExoticSixSphere.SphereFourTubeOldBoundaryRelation
import Wikipedia.NoExoticSixSphere.ManifoldRawSphereFrame

/-!
# The original old-boundary sphere parity is unchanged by tube excision

The old zero inclusion fixes ambient points and preserves the original
full normal frame exactly. Thus its actual raw sphere-frame operator is
unchanged. The checked twisted-extension criterion compares the original
geometric parities without transporting either native zero atlas.
-/

noncomputable section

open Function Set ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime EuclideanEmbedding Stiefel

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)

def oldZeroMap : C({x : M // t x = 0}, {x : M // τ x = 0}) :=
  ⟨oldZeroInclusion Φ hΦ t τ hpos hout, continuous_subtype_val.subtype_mk _⟩

theorem oldZeroMap_injective : Injective (oldZeroMap Φ hΦ t τ hpos hout) := by
  intro p q hpq
  exact Subtype.ext (congrArg (fun z : {x : M // τ x = 0} ↦ z.val) hpq)

theorem oldZeroMap_to_half : (zeroToHalf τ).comp (oldZeroMap Φ hΦ t τ hpos hout) =
    oldZeroToNewHalf Φ hΦ t τ hpos hout := rfl

variable (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
  (hτreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))

theorem contMDiff_oldZeroMap :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zeroAtlas (n := 6) τ hτ hτreg;
    ContMDiff (𝓡 6) (𝓡 6) ∞ (oldZeroMap Φ hΦ t τ hpos hout) := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zeroAtlas (n := 6) τ hτ hτreg
  exact (isLocalDiffeomorph_oldZeroInclusion Φ hΦ t τ hpos hout ht hτ hreg hτreg).contMDiff

theorem oldZeroMap_comp_mfderiv_injective (f : C(Sphere 3, {x : M // t x = 0})) :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zeroAtlas (n := 6) τ hτ hτreg;
    ∀ (_ : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
      (_ : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s)) (s : Sphere 3),
      Injective (mfderiv (𝓡 3) (𝓡 6) ((oldZeroMap Φ hΦ t τ hpos hout).comp f) s) := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zeroAtlas (n := 6) τ hτ hτreg
  let := zero_isManifold (n := 6) t ht hreg
  intro hf hd s
  change Injective (mfderiv (𝓡 3) (𝓡 6) ((oldZeroMap Φ hΦ t τ hpos hout) ∘ f) s)
  rw [mfderiv_comp s
    ((contMDiff_oldZeroMap Φ hΦ t τ hpos hout ht hτ hreg hτreg).mdifferentiableAt (by simp))
    (hf.mdifferentiableAt (by simp))]
  exact ((isLocalDiffeomorph_oldZeroInclusion Φ hΦ t τ hpos hout ht hτ hreg hτreg (f s)
    ).mfderivToContinuousLinearEquiv (by simp)).injective.comp (hd s)

variable (e : EuclideanEmbedding 7 M) (r r' : e.TubularRetraction)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel) (m m' : M)

theorem oldZero_rawSphereFrameOperator (f : C(Sphere 3, {x : M // t x = 0}))
    (s : Sphere 3) :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zeroAtlas (n := 6) τ hτ hτreg;
    (zeroEmbedding (n := 6) e τ hτ hτreg).rawSphereFrameOperator
      (zeroNormalFrame (n := 6) e r' τ hτ hτreg a m')
      ((oldZeroMap Φ hΦ t τ hpos hout).comp f) s =
    (zeroEmbedding (n := 6) e t ht hreg).rawSphereFrameOperator
      (zeroNormalFrame (n := 6) e r t ht hreg a m) f s := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zeroAtlas (n := 6) τ hτ hτreg
  have ha : (zeroNormalFrame (n := 6) e r' τ hτ hτreg a m').ambient
      (oldZeroMap Φ hΦ t τ hpos hout (f s)) =
      (zeroNormalFrame (n := 6) e r t ht hreg a m).ambient (f s) := by
    apply ContinuousLinearMap.ext
    intro v
    exact oldZero_normalFrame Φ hΦ t τ hpos hout ht hτ hreg hτreg e r r' a m m' (f s) v
  exact congrArg (fun A : Vector (e.ambientDimension - 6) →L[ℝ] Vector e.ambientDimension ↦
    OperatorSum.operator A (SphereThreeTangentFrame.framedDerivative
      (e.toFun ∘ (fun x : {x : M // t x = 0} ↦ x.val) ∘ f) s)) ha

theorem oldZero_sphereParity_eq (f : C(Sphere 3, {x : M // t x = 0})) :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zeroAtlas (n := 6) τ hτ hτreg;
    ∀ (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
      (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
      (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ ((oldZeroMap Φ hΦ t τ hpos hout).comp f))
      (hFi : Injective ((oldZeroMap Φ hΦ t τ hpos hout).comp f))
      (hFd : ∀ s, Injective
        (mfderiv (𝓡 3) (𝓡 6) ((oldZeroMap Φ hΦ t τ hpos hout).comp f) s)),
      (zeroEmbedding (n := 6) e τ hτ hτreg).sphereParity
        (zeroNormalFrame (n := 6) e r' τ hτ hτreg a m')
        ((oldZeroMap Φ hΦ t τ hpos hout).comp f) hF hFi hFd =
      (zeroEmbedding (n := 6) e t ht hreg).sphereParity
        (zeroNormalFrame (n := 6) e r t ht hreg a m) f hf hi hd := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zeroAtlas (n := 6) τ hτ hτreg
  intro hf hi hd hF hFi hFd
  have hmap :
      (zeroEmbedding (n := 6) e τ hτ hτreg).rawSphereFrameOperatorMap
        (zeroNormalFrame (n := 6) e r' τ hτ hτreg a m')
        ((oldZeroMap Φ hΦ t τ hpos hout).comp f) hF hFd =
      (zeroEmbedding (n := 6) e t ht hreg).rawSphereFrameOperatorMap
        (zeroNormalFrame (n := 6) e r t ht hreg a m) f hf hd := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    exact oldZero_rawSphereFrameOperator Φ hΦ t τ hpos hout ht hτ hreg hτreg e r r' a m m' f s
  apply zmodTwo_eq_of_zero_iff
  rw [sphereParity_zero_iff_raw_twisted_extension, sphereParity_zero_iff_raw_twisted_extension,
    hmap]
  exact Iff.rfl

end NoExoticSixSphere.SphereFourTube
