import Wikipedia.NoExoticSixSphere.EmbeddedTimeGradient
import Wikipedia.NoExoticSixSphere.RegularFiberDifferential

/-!
# The actual embedded regular time-zero fiber and its tangent differential

The zero set retains the native regular-fiber atlas and the original
ambient embedding. Its tangent inclusion is injective, is killed by the
original time differential, and is orthogonal to the intrinsic time-gradient.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (t : C(M, ℝ)) (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

@[instance_reducible]
def zeroAtlas : ChartedSpace (Vector n) {x : M // t x = 0} :=
  regularFiberAtlas t ht 0 hreg n (by simp [Nat.add_comm])

theorem zero_isManifold : letI := zeroAtlas t ht hreg;
    IsManifold (𝓡 n) ∞ {x : M // t x = 0} :=
  regularFiber_isManifold t ht 0 hreg n (by simp [Nat.add_comm])

theorem contMDiff_zeroInclusion : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ (Subtype.val : {x : M // t x = 0} → M) :=
  regularFiber_contMDiff_subtype_val t ht 0 hreg n (by simp [Nat.add_comm])

def inclusionDerivative (p : {x : M // t x = 0}) : Vector n →L[ℝ] Vector (n + 1) :=
  letI := zeroAtlas t ht hreg;
  mfderiv (𝓡 n) (𝓡 (n + 1)) (Subtype.val : {x : M // t x = 0} → M) p

theorem inclusionDerivative_injective (p : {x : M // t x = 0}) :
    Injective (inclusionDerivative t ht hreg p) :=
  regularFiber_injective_mfderiv_subtype_val t ht 0 hreg n (by simp [Nat.add_comm]) p

theorem timeDerivative_comp_inclusion (p : {x : M // t x = 0}) :
    (timeDerivative (n := n + 1) t p.val).comp (inclusionDerivative t ht hreg p) = 0 :=
  regularFiber_differential_comp_inclusion t ht 0 hreg n (by simp [Nat.add_comm]) p

def zeroEmbedding : letI := zeroAtlas t ht hreg;
    EuclideanEmbedding n {x : M // t x = 0} := by
  let := zeroAtlas t ht hreg
  exact
    { ambientDimension := e.ambientDimension
      toFun := e.toFun ∘ Subtype.val
      smooth := e.smooth.comp (contMDiff_zeroInclusion t ht hreg)
      closedEmbedding := e.closedEmbedding.comp
        (isClosed_eq t.continuous continuous_const).isClosedEmbedding_subtypeVal
      injective_mfderiv p := by
        rw [mfderiv_comp p (e.smooth.mdifferentiableAt (by simp))
          ((contMDiff_zeroInclusion t ht hreg).mdifferentiableAt (by simp))]
        exact (e.injective_mfderiv p.val).comp (inclusionDerivative_injective t ht hreg p) }

theorem zeroEmbedding_apply (p : {x : M // t x = 0}) : letI := zeroAtlas t ht hreg;
    (zeroEmbedding e t ht hreg).toFun p = e.toFun p.val := rfl

def zeroDerivative (p : {x : M // t x = 0}) : Vector n →L[ℝ] Vector e.ambientDimension :=
  letI := zeroAtlas t ht hreg;
  mfderiv (𝓡 n) (𝓡 e.ambientDimension)
    (e.toFun ∘ (Subtype.val : {x : M // t x = 0} → M)) p

theorem zeroDerivative_eq (p : {x : M // t x = 0}) :
    zeroDerivative e t ht hreg p =
      (embeddingDerivative e p.val).comp (inclusionDerivative t ht hreg p) := by
  let := zeroAtlas t ht hreg
  let := zero_isManifold t ht hreg
  exact mfderiv_comp p (e.smooth.mdifferentiableAt (by simp))
    ((contMDiff_zeroInclusion t ht hreg).mdifferentiableAt (by simp))

theorem zero_tangent_le (p : {x : M // t x = 0}) :
    letI := zeroAtlas t ht hreg;
    (zeroEmbedding e t ht hreg).tangentImage p ≤ e.tangentImage p.val := by
  let := zeroAtlas t ht hreg
  let := zero_isManifold t ht hreg
  change (embeddingDerivative (zeroEmbedding e t ht hreg) p).range ≤
    (embeddingDerivative e p.val).range
  change (zeroDerivative e t ht hreg p).range ≤ (embeddingDerivative e p.val).range
  rw [zeroDerivative_eq]
  exact LinearMap.range_comp_le_range _ _

theorem inner_gradient_zero_derivative (r : e.TubularRetraction)
    (p : {x : M // t x = 0}) (v : Vector n) :
    letI := zeroAtlas t ht hreg; letI := zero_isManifold t ht hreg;
    inner ℝ (gradient e r t p.val) (zeroDerivative e t ht hreg p v) = 0 := by
  let := zeroAtlas t ht hreg
  let := zero_isManifold t ht hreg
  rw [zeroDerivative_eq, ContinuousLinearMap.comp_apply,
    inner_gradient_native e r t ht]
  exact congrArg (fun L : Vector n →L[ℝ] ℝ ↦ L v) (timeDerivative_comp_inclusion t ht hreg p)

end NoExoticSixSphere.EmbeddedTime
