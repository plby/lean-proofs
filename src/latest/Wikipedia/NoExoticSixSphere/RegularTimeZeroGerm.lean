import Wikipedia.NoExoticSixSphere.RegularTimeZeroNormalFrame
import Wikipedia.NoExoticSixSphere.ManifoldLocalInverse

/-!
# Native zero inclusions and induced frames under equality of time germs

An inclusion of regular zero sets is smooth and locally a diffeomorphism
for their independently constructed regular-fiber atlases. Equality of
the ambient time germs preserves the full induced normal frame, even
when the two gradients use different tubular retractions.
-/

noncomputable section

open Function Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  (t τ : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hτ : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ τ)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))
  (hτreg : ∀ x, τ x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) τ x))

def zeroInclusionOfSubset (hinc : ∀ x, t x = 0 → τ x = 0) :
    {x : M // t x = 0} → {x : M // τ x = 0} :=
  fun p ↦ ⟨p.val, hinc p.val p.property⟩

theorem contMDiff_zeroInclusionOfSubset (hinc : ∀ x, t x = 0 → τ x = 0) :
    letI := zeroAtlas t ht hreg;
    letI := zeroAtlas τ hτ hτreg;
    ContMDiff (𝓡 n) (𝓡 n) ∞ (zeroInclusionOfSubset t τ hinc) := by
  let := zeroAtlas t ht hreg
  let := zeroAtlas τ hτ hτreg
  exact (regularFiber_contMDiff_iff_ambient τ hτ 0 hτreg n
    (by simp [Nat.add_comm]) (zeroInclusionOfSubset t τ hinc)).mpr
      (contMDiff_zeroInclusion t ht hreg)

theorem isLocalDiffeomorph_zeroInclusionOfSubset (hinc : ∀ x, t x = 0 → τ x = 0) :
    letI := zeroAtlas t ht hreg;
    letI := zeroAtlas τ hτ hτreg;
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (zeroInclusionOfSubset t τ hinc) := by
  let := zeroAtlas t ht hreg
  let := zeroAtlas τ hτ hτreg
  let := zero_isManifold t ht hreg
  let := zero_isManifold τ hτ hτreg
  let j := zeroInclusionOfSubset t τ hinc
  have hj : ContMDiff (𝓡 n) (𝓡 n) ∞ j :=
    contMDiff_zeroInclusionOfSubset t τ ht hτ hreg hτreg hinc
  intro p
  apply isLocalDiffeomorphAt_of_surjective_mfderiv hj rfl p
  let L : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) j p
  change Surjective L
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
  intro v w hvw
  have hc : inclusionDerivative t ht hreg p =
      (inclusionDerivative τ hτ hτreg (j p)).comp (mfderiv (𝓡 n) (𝓡 n) j p) :=
    mfderiv_comp p ((contMDiff_zeroInclusion τ hτ hτreg).mdifferentiableAt (by simp))
      (hj.mdifferentiableAt (by simp))
  apply inclusionDerivative_injective t ht hreg p
  rw [hc]
  exact congrArg (inclusionDerivative τ hτ hτreg (j p)) hvw

include ht hτ in
theorem gradient_eq_of_eventuallyEq (e : EuclideanEmbedding (n + 1) M)
    (r r' : e.TubularRetraction) (x : M) (heq : (τ : M → ℝ) =ᶠ[𝓝 x] t) :
    gradient e r' τ x = gradient e r t x := by
  apply gradient_unique e r t ht x _ (gradient_mem_tangent e r' τ x)
  intro v
  rw [inner_gradient_native e r' τ hτ]
  exact congrArg (fun L : Vector (n + 1) →L[ℝ] ℝ ↦ L v) heq.mfderiv_eq

include ht hτ in
theorem zeroColumns_eq_of_eventuallyEq (e : EuclideanEmbedding (n + 1) M)
    (r r' : e.TubularRetraction)
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (p : {x : M // t x = 0}) (q : {x : M // τ x = 0}) (hpq : q.val = p.val)
    (heq : (τ : M → ℝ) =ᶠ[𝓝 p.val] t) :
    zeroColumns e r' τ a q = zeroColumns e r t a p := by
  change OrthogonalFrameAppend.operator (a.orthonormal q.val).val
      (-NormedSpace.normalize (gradient e r' τ q.val)) =
    OrthogonalFrameAppend.operator (a.orthonormal p.val).val
      (-NormedSpace.normalize (gradient e r t p.val))
  rw [hpq, gradient_eq_of_eventuallyEq t τ ht hτ e r r' p.val heq]

theorem zeroNormalFrame_eq_of_eventuallyEq (e : EuclideanEmbedding (n + 1) M)
    (r r' : e.TubularRetraction)
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (m m' : M) (p : {x : M // t x = 0}) (q : {x : M // τ x = 0})
    (hpq : q.val = p.val) (heq : (τ : M → ℝ) =ᶠ[𝓝 p.val] t) :
    letI := zeroAtlas t ht hreg;
    letI := zeroAtlas τ hτ hτreg;
    ∀ v : Vector (e.ambientDimension - n),
      (zeroNormalFrame e r' τ hτ hτreg a m').ambient q v =
        (zeroNormalFrame e r t ht hreg a m).ambient p v := by
  let := zeroAtlas t ht hreg
  let := zeroAtlas τ hτ hτreg
  intro v
  change zeroColumns e r' τ a q (normalCoordinates e m v) =
    zeroColumns e r t a p (normalCoordinates e m v)
  rw [zeroColumns_eq_of_eventuallyEq t τ ht hτ e r r' a p q hpq heq]

end NoExoticSixSphere.EmbeddedTime
