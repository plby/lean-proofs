import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereFamily
import Wikipedia.NoExoticSixSphere.WeightedAffinePairEvaluation

/-!
# Actual value and difference submersions with a protected region

An active source point has a surjective parameter derivative. At two distinct
points, the chart-coordinate difference has surjective parameter derivative
as soon as either cutoff is nonzero. In particular one point may remain fixed
throughout the family. The formulas use the actual tubular retraction.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding
open TwoSpherePerturbation (Parameters)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

theorem hasFDerivAt_ambient_parameter (p : Parameters e) (t : ℝ) (s : Sphere 2) :
    HasFDerivAt (fun q : Parameters e ↦ ambient e f χ q t s)
      ((cutoff t * χ s) • AffinePerturbation.evaluation (s : Vector 3)) p := by
  simpa only [ambient_apply] using
    AffinePerturbation.hasFDerivAt_weighted_value (s : Vector 3) p
      (cutoff t * χ s) (e.toFun (f t s))

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
    (p : Parameters e) (t : ℝ) (s : Sphere 2)
    (hp : ambient e f χ p t s ∈ r.domain) (hc : map e r f χ p t s ∈ c.source) :
    HasFDerivAt (fun q : Parameters e ↦ c (map e r f χ q t s))
      ((fderiv ℝ (fun y ↦ c (r.toFun y)) (ambient e f χ p t s)).comp
        ((cutoff t * χ s) • AffinePerturbation.evaluation (s : Vector 3))) p := by
  have hR := (contDiffAt_chartRetraction e r c (ambient e f χ p t s) hp hc).differentiableAt
    (by simp)
  have h := hR.hasFDerivAt.comp p (hasFDerivAt_ambient_parameter e f χ p t s)
  exact h

theorem surjective_fderiv_chart_parameter
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (p : Parameters e) (t : ℝ) (s : Sphere 2)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hχs : χ s ≠ 0)
    (hp : ambient e f χ p t s ∈ r.domain) (hc : map e r f χ p t s ∈ c.source) :
    Surjective (fderiv ℝ (fun q : Parameters e ↦ c (map e r f χ q t s)) p) := by
  rw [(hasFDerivAt_chart_parameter e r f χ c p t s hp hc).fderiv]
  exact (surjective_fderiv_chartRetraction e r c (ambient e f χ p t s) hp hc).comp
    (AffinePerturbation.surjective_smul_evaluation (s : Vector 3)
      (mul_ne_zero (cutoff_pos ht).ne' hχs))

theorem surjective_fderiv_chart_pair_difference_parameter
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (p : Parameters e) (t : ℝ) (s z : Sphere 2) (hsz : s ≠ z)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hχsz : χ s ≠ 0 ∨ χ z ≠ 0)
    (hps : ambient e f χ p t s ∈ r.domain) (hpz : ambient e f χ p t z ∈ r.domain)
    (hcs : map e r f χ p t s ∈ c.source) (hcz : map e r f χ p t z ∈ c.source) :
    Surjective (fderiv ℝ (fun q : Parameters e ↦
      c (map e r f χ q t s) - c (map e r f χ q t z)) p) := by
  have he := ((hasFDerivAt_chart_parameter e r f χ c p t s hps hcs).sub
    (hasFDerivAt_chart_parameter e r f χ c p t z hpz hcz)).fderiv
  change fderiv ℝ (fun q : Parameters e ↦
    c (map e r f χ q t s) - c (map e r f χ q t z)) p = _ at he
  rw [he]
  have hsz' : (s : Vector 3) ≠ (z : Vector 3) := fun h ↦ hsz (Subtype.ext h)
  apply AffinePerturbation.surjective_weighted_difference (s : Vector 3) (z : Vector 3)
    hsz' _ _ (surjective_fderiv_chartRetraction e r c (ambient e f χ p t s) hps hcs)
    (surjective_fderiv_chartRetraction e r c (ambient e f χ p t z) hpz hcz)
  exact hχsz.imp (mul_ne_zero (cutoff_pos ht).ne') (mul_ne_zero (cutoff_pos ht).ne')

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
