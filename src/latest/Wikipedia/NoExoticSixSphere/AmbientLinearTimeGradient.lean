import Wikipedia.NoExoticSixSphere.EmbeddedTimeGradient

/-!
# The intrinsic gradient of an actual ambient linear time coordinate

If the original time is the restriction of an ambient linear functional,
its representing vector is the intrinsic gradient wherever that vector
belongs to the actual tangent image. The proof differentiates the actual
time identity and uses uniqueness, independently of the tubular choice.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] (e : EuclideanEmbedding n M)
  (r : e.TubularRetraction) (t : M → ℝ)

theorem gradient_eq_of_ambient_linear_time
    (ht : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ t)
    (c : Vector e.ambientDimension →L[ℝ] ℝ)
    (he : ∀ x, c (e.toFun x) = t x)
    (g : Vector e.ambientDimension) (hc : ∀ v, inner ℝ g v = c v)
    (x : M) (hg : g ∈ e.tangentImage x) : gradient e r t x = g := by
  apply (gradient_unique e r t ht x g hg ?_).symm
  intro v
  rw [hc]
  have hfun : c ∘ e.toFun = t := funext he
  have hd := mfderiv_comp x c.differentiableAt.mdifferentiableAt
    (e.smooth.mdifferentiableAt (by simp))
  rw [hfun, mfderiv_eq_fderiv, c.fderiv] at hd
  exact (congrArg (fun L : Vector n →L[ℝ] ℝ ↦ L v) hd).symm

end NoExoticSixSphere.EmbeddedTime
