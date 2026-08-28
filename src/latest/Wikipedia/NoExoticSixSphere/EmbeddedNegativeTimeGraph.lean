import Wikipedia.NoExoticSixSphere.EmbeddedTimeInwardFrame
import Wikipedia.NoExoticSixSphere.OutwardGraphFrame

/-!
# The actual negative-time graph of a disk map into the embedded manifold

Both its smoothness and its complete derivative are derived from the
original map. The graph height is negative time, so a negative outward
radial derivative of time is precisely the positive height condition
used by the original sphere-parity criterion.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t) (g : Vector 4 → M)

def negativeTimeGraph (x : Vector 4) : Vector e.ambientDimension × ℝ :=
  (e.toFun (g x), -t (g x))

include ht in
theorem contDiffAt_negativeTimeGraph (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) :
    ContDiffAt ℝ ∞ (negativeTimeGraph e t g) x :=
  (e.smooth.contMDiffAt.comp x hg).contDiffAt.prodMk
    (ht.contMDiffAt.comp x hg).contDiffAt.neg

include ht in
theorem negativeTimeGraph_derivative (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) :
    fderiv ℝ (negativeTimeGraph e t g) x =
      OutwardGraphFrame.graph (fderiv ℝ (e.toFun ∘ g) x) (-timeCovector e r t (g x)) := by
  have hE : DifferentiableAt ℝ (e.toFun ∘ g) x :=
    (e.smooth.contMDiffAt.comp x hg).contDiffAt.differentiableAt (by simp)
  have hT : DifferentiableAt ℝ (t ∘ g) x :=
    (ht.contMDiffAt.comp x hg).contDiffAt.differentiableAt (by simp)
  have hd := (hE.hasFDerivAt.prodMk hT.hasFDerivAt.neg).fderiv
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : Vector 4 →L[ℝ] (Vector e.ambientDimension × ℝ) ↦ L v) hd
  change fderiv ℝ (negativeTimeGraph e t g) x v =
    (fderiv ℝ (e.toFun ∘ g) x v, -fderiv ℝ (t ∘ g) x v) at hv
  rw [OutwardGraphFrame.graph_apply]
  change fderiv ℝ (negativeTimeGraph e t g) x v =
    (fderiv ℝ (e.toFun ∘ g) x v, -timeCovector e r t (g x) (fderiv ℝ (e.toFun ∘ g) x v))
  rw [timeCovector_composedDerivative e r t ht g x hg]
  exact hv

include r ht in
theorem negativeTimeGraph_heightDerivative (x : Vector 4)
    (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g x) (v : Vector 4) :
    (fderiv ℝ (negativeTimeGraph e t g) x v).2 = -fderiv ℝ (t ∘ g) x v := by
  rw [negativeTimeGraph_derivative e r t ht g x hg, OutwardGraphFrame.graph_apply]
  change -timeCovector e r t (g x) (fderiv ℝ (e.toFun ∘ g) x v) = _
  rw [timeCovector_composedDerivative e r t ht g x hg]

include r ht in
theorem negativeTimeGraph_height_pos (s : Sphere 3)
    (hg : ContMDiffAt (𝓡 4) (𝓡 (n + 1)) ∞ g s.val)
    (hheight : fderiv ℝ (t ∘ g) s.val s.val < 0) :
    0 < (fderiv ℝ (negativeTimeGraph e t g) s.val s.val).2 := by
  rw [negativeTimeGraph_heightDerivative e r t ht g s.val hg s.val]
  exact neg_pos.mpr hheight

end NoExoticSixSphere.EmbeddedTime
