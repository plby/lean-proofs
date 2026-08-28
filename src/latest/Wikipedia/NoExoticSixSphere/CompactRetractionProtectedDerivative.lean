import Wikipedia.NoExoticSixSphere.CompactRetractionAffineFamily
import Wikipedia.NoExoticSixSphere.WeightedAffineProtectedDerivative

/-!
# Original ambient derivatives on the protected zero set

Nonnegativity makes the cutoff derivative vanish at every zero, even when
the cutoff is not locally constant. The retraction fixes the original map
on a genuine neighborhood of each point whose value is in its open base.
Thus the actual embedded derivative is unchanged at protected points.
-/

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

theorem fderiv_embedded_map_of_zero_cutoff (p : Parameters d e) (x : Vector d)
    (hf : ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiffAt ℝ ∞ χ x)
    (hn : ∀ z, 0 ≤ χ z) (hx : χ x = 0) (hb : f x ∈ r.base) :
    fderiv ℝ (e.toFun ∘ map e r f χ p) x = fderiv ℝ (e.toFun ∘ f) x := by
  let R := e.toFun ∘ r.toFun
  have ha : WeightedAffineComposite.ambient (e.toFun ∘ f) id χ p x = e.toFun (f x) := by
    simp only [WeightedAffineComposite.ambient, hx, zero_smul, add_zero, comp_apply]
  have hdom : WeightedAffineComposite.ambient (e.toFun ∘ f) id χ p x ∈ r.domain :=
    ha.symm ▸ r.contains ⟨f x, hb, rfl⟩
  have hR : ContDiffAt ℝ ∞ R
      (WeightedAffineComposite.ambient (e.toFun ∘ f) id χ p x) :=
    (e.smooth.contMDiffAt.comp _
      (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hdom))).contDiffAt
  have hjet := WeightedAffineComposite.fderiv_composite_eq_zero_parameter_of_zero_cutoff
    (e.toFun ∘ f) id R χ p x
    ((e.smooth.contMDiffAt.comp x hf).contDiffAt.differentiableAt (by simp))
    differentiableAt_id (hχ.differentiableAt (by simp)) (hR.differentiableAt (by simp)) hn hx
  have he0 : (e.toFun ∘ map e r f χ 0) =ᶠ[𝓝 x] (e.toFun ∘ f) := by
    filter_upwards [hf.continuousAt (r.base.isOpen.mem_nhds hb)] with y hy
    exact congrArg e.toFun (map_zero e r f χ y hy)
  exact hjet.trans he0.fderiv_eq

end NoExoticSixSphere.CompactRetractionAffineFamily
