import Wikipedia.NoExoticSixSphere.RegularTimeZeroColumns

/-!
# The actual time covector for the outward graph comparison

Pairing with the intrinsic ambient gradient gives a smooth ambient
covector. It annihilates every actual normal-frame column, agrees with
the native time differential on every tangent vector, and is strictly
negative on the actual outward normal. These are the geometric inputs
to the injectivity-preserving outward graph homotopy.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)

def timeCovector (x : M) : Vector e.ambientDimension →L[ℝ] ℝ :=
  innerSL ℝ (gradient e r t x)

theorem timeCovector_apply (x : M) (v : Vector e.ambientDimension) :
    timeCovector e r t x v = inner ℝ (gradient e r t x) v := rfl

include ht in
theorem contMDiff_timeCovector :
    ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, Vector e.ambientDimension →L[ℝ] ℝ) ∞
      (timeCovector e r t) :=
  ((innerSL ℝ).contDiff.contMDiff).comp (contMDiff_gradient e r t ht)

theorem timeCovector_frame
    (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)
    (x : M) (v : e.NormalModel) : timeCovector e r t x (a.ambient x v) = 0 := by
  have ha : (a.ambient x).range = (e.tangentImage x)ᗮ :=
    (a.ambient_range x).trans (e.range_normalProjection x)
  exact Submodule.inner_right_of_mem_orthogonal (gradient_mem_tangent e r t x)
    (ha.le ⟨v, rfl⟩)

include ht in
theorem timeCovector_native (x : M) (v : Vector (n + 1)) :
    timeCovector e r t x (embeddingDerivative e x v) = timeDerivative t x v :=
  inner_gradient_native e r t ht x v

include ht in
theorem timeCovector_composedDerivative {d : ℕ} (g : Vector d → M) (x : Vector d)
    (hg : ContMDiffAt (𝓡 d) (𝓡 (n + 1)) ∞ g x) (v : Vector d) :
    timeCovector e r t (g x) (fderiv ℝ (e.toFun ∘ g) x v) = fderiv ℝ (t ∘ g) x v := by
  let Dg : Vector d →L[ℝ] Vector (n + 1) := mfderiv (𝓡 d) (𝓡 (n + 1)) g x
  have hD : fderiv ℝ (e.toFun ∘ g) x = (embeddingDerivative e (g x)).comp
      Dg := by
    have h := mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hT : fderiv ℝ (t ∘ g) x = (timeDerivative t (g x)).comp
      Dg := by
    have h := mfderiv_comp x (ht.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact h
  rw [hD, ContinuousLinearMap.comp_apply, timeCovector_native e r t ht]
  exact (congrArg (fun L : Vector d →L[ℝ] ℝ ↦ L v) hT).symm

variable (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

include ht hreg in
theorem timeCovector_outward (p : {x : M // t x = 0}) :
    timeCovector e r t p.val (outwardNormal e r t p) = -‖gradient e r t p.val‖ :=
  (inner_gradient_tangent e r t p.val _ (outwardNormal_mem_tangent e r t p)).trans
    (extension_outward_eq e r t ht hreg p)

include ht hreg in
theorem timeCovector_outward_neg (p : {x : M // t x = 0}) :
    timeCovector e r t p.val (outwardNormal e r t p) < 0 := by
  rw [timeCovector_outward e r t ht hreg p]
  exact neg_lt_zero.mpr
    (norm_pos_iff.mpr (gradient_ne_zero e r t ht p.val (hreg p.val p.property)))

end NoExoticSixSphere.EmbeddedTime
