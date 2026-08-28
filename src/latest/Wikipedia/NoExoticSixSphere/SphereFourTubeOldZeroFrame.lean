import Wikipedia.NoExoticSixSphere.SphereFourTubeTimeCollar
import Wikipedia.NoExoticSixSphere.RegularTimeZeroGerm

/-!
# The original native boundary frame is unchanged by tube excision

The old zero set maps into the new regular zero set by the identity on
ambient points. This map is a native local diffeomorphism and an open
embedding. The original outward induced normal frame agrees exactly
with the new frame there, including independent retraction choices.
-/

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization EmbeddedTime

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [T2Space M] [IsManifold (𝓡 7) ∞ M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (hΦ : Φ.source = univ) (t τ : C(M, ℝ))
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)

def oldZeroInclusion : {x : M // t x = 0} → {x : M // τ x = 0} :=
  zeroInclusionOfSubset t τ (fun x hx ↦
    ((modified_time_eventuallyEq_old_zero Φ τ hΦ t hpos hout hx).eq_of_nhds).trans hx)

theorem oldZeroInclusion_val (p : {x : M // t x = 0}) :
    (oldZeroInclusion Φ hΦ t τ hpos hout p).val = p.val := rfl

theorem range_oldZeroInclusion : range (oldZeroInclusion Φ hΦ t τ hpos hout) =
    {q : {x : M // τ x = 0} | t q.val = 0} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact p.property
  · intro hq
    exact ⟨⟨q.val, hq⟩, Subtype.ext rfl⟩

variable (ht : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ t)
  (hτ : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) t x))
  (hτreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) τ x))

theorem isLocalDiffeomorph_oldZeroInclusion :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zeroAtlas (n := 6) τ hτ hτreg;
    IsLocalDiffeomorph (𝓡 6) (𝓡 6) ∞ (oldZeroInclusion Φ hΦ t τ hpos hout) :=
  isLocalDiffeomorph_zeroInclusionOfSubset t τ ht hτ hreg hτreg _

include ht hτ hreg hτreg in
theorem isOpenEmbedding_oldZeroInclusion :
    Topology.IsOpenEmbedding (oldZeroInclusion Φ hΦ t τ hpos hout) := by
  let := zeroAtlas (n := 6) t ht hreg
  let := zeroAtlas (n := 6) τ hτ hτreg
  apply (isLocalDiffeomorph_oldZeroInclusion Φ hΦ t τ hpos hout ht hτ hreg hτreg
    ).isLocalHomeomorph.isOpenEmbedding_of_injective
  intro p q hpq
  exact Subtype.ext (congrArg (fun z : {x : M // τ x = 0} ↦ z.val) hpq)

theorem oldZero_normalFrame (e : EuclideanEmbedding 7 M) (r r' : e.TubularRetraction)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (m m' : M) (p : {x : M // t x = 0}) :
    letI := zeroAtlas (n := 6) t ht hreg;
    letI := zeroAtlas (n := 6) τ hτ hτreg;
    ∀ v : Vector (e.ambientDimension - 6),
      (zeroNormalFrame (n := 6) e r' τ hτ hτreg a m').ambient
        (oldZeroInclusion Φ hΦ t τ hpos hout p) v =
      (zeroNormalFrame (n := 6) e r t ht hreg a m).ambient p v :=
  zeroNormalFrame_eq_of_eventuallyEq t τ ht hτ hreg hτreg e r r' a m m' p
    (oldZeroInclusion Φ hΦ t τ hpos hout p) rfl
    (modified_time_eventuallyEq_old_zero Φ τ hΦ t hpos hout p.property)

end NoExoticSixSphere.SphereFourTube
