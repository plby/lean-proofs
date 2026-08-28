import Wikipedia.NoExoticSixSphere.CompactRetractionAffineFamily
import Wikipedia.NoExoticSixSphere.WeightedAffinePairEvaluation

/-!
# Actual double-point parameter submersion with one active source point

Distinct source points admit independent affine value variations. The
original retraction and target chart have surjective derivatives on their
actual domains. Thus one nonzero cutoff suffices for surjectivity of the
parameter derivative of the image difference, even when the other point
is protected. No smoothness outside the specified domains is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

theorem hasFDerivAt_ambient_parameter (p : Parameters d e) (x : Vector d) :
    HasFDerivAt (fun q : Parameters d e ↦ ambient e f χ q x)
      (χ x • AffinePerturbation.evaluation x) p :=
  AffinePerturbation.hasFDerivAt_weighted_value x p (χ x) (e.toFun (f x))

theorem contDiffAt_chartRetraction
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (y : Vector e.ambientDimension) (hy : y ∈ r.domain) (hc : r.toFun y ∈ c.source) :
    ContDiffAt ℝ ∞ (fun z ↦ c (r.toFun z)) y := by
  have hr := r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hy)
  have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc)
  exact (hcs.comp y hr).contDiffAt

theorem surjective_fderiv_chartRetraction
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (y : Vector e.ambientDimension) (hy : y ∈ r.domain) (hc : r.toFun y ∈ c.source) :
    Surjective (fderiv ℝ (fun z ↦ c (r.toFun z)) y) := by
  have hr := r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hy)
  have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc)
  have hlocal : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (r.toFun y) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  have hsurj := (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  change Surjective (mfderiv (𝓡 n) (𝓡 n) c (r.toFun y)) at hsurj
  change Surjective (fderiv ℝ (c ∘ r.toFun) y)
  rw [← mfderiv_eq_fderiv, mfderiv_comp y (hcs.mdifferentiableAt (by simp))
    (hr.mdifferentiableAt (by simp))]
  exact hsurj.comp (r.submersive y hy)

theorem hasFDerivAt_chart_parameter
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (p : Parameters d e) (x : Vector d)
    (hp : ambient e f χ p x ∈ r.domain) (hc : map e r f χ p x ∈ c.source) :
    HasFDerivAt (fun q : Parameters d e ↦ c (map e r f χ q x))
      ((fderiv ℝ (fun y ↦ c (r.toFun y)) (ambient e f χ p x)).comp
        (χ x • AffinePerturbation.evaluation x)) p := by
  have hR : DifferentiableAt ℝ (fun y ↦ c (r.toFun y)) (ambient e f χ p x) :=
    (contDiffAt_chartRetraction e r c (ambient e f χ p x) hp hc).differentiableAt (by simp)
  have h := hR.hasFDerivAt.comp p (hasFDerivAt_ambient_parameter e f χ p x)
  exact h

theorem surjective_fderiv_chart_pair_difference_parameter
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (p : Parameters d e) (x y : Vector d) (hxy : x ≠ y)
    (hχxy : χ x ≠ 0 ∨ χ y ≠ 0)
    (hpx : ambient e f χ p x ∈ r.domain) (hpy : ambient e f χ p y ∈ r.domain)
    (hcx : map e r f χ p x ∈ c.source) (hcy : map e r f χ p y ∈ c.source) :
    Surjective (fderiv ℝ (fun q : Parameters d e ↦
      c (map e r f χ q x) - c (map e r f χ q y)) p) := by
  have he := ((hasFDerivAt_chart_parameter e r f χ c p x hpx hcx).sub
    (hasFDerivAt_chart_parameter e r f χ c p y hpy hcy)).fderiv
  change fderiv ℝ (fun q : Parameters d e ↦
    c (map e r f χ q x) - c (map e r f χ q y)) p = _ at he
  rw [he]
  exact AffinePerturbation.surjective_weighted_difference x y hxy _ _
    (surjective_fderiv_chartRetraction e r c (ambient e f χ p x) hpx hcx)
    (surjective_fderiv_chartRetraction e r c (ambient e f χ p y) hpy hcy)
    (χ x) (χ y) hχxy

end NoExoticSixSphere.CompactRetractionAffineFamily
