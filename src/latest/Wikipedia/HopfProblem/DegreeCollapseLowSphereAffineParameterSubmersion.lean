import Wikipedia.HopfProblem.DegreeCollapseLowSphereAffineFamily
import Wikipedia.NoExoticSixSphere.AffineParameterEvaluation

/-!

# Independent parameter variations at actual manifold-valued sphere points

The derivative of the tubular retraction is surjective. Affine parameter
evaluation can independently move two distinct sphere points in ambient
space, so the actual manifold-valued two-point parameter map is a submersion
at every interior time in the tubular domain. This is not yet jet genericity.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

open NoExoticSixSphere GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere d → M)

theorem hasFDerivAt_ambient_parameter (p : Parameters e d) (t : ℝ) (s : Sphere d) :
    HasFDerivAt (fun q : Parameters e d ↦ ambient e f q t s)
      (cutoff t • AffinePerturbation.evaluation (s : Vector (d + 1))) p :=
  AffinePerturbation.hasFDerivAt_weighted_value (s : Vector (d + 1)) p (cutoff t) (e.toFun (f t s))

theorem contMDiffAt_map_parameter (p : Parameters e d) (t : ℝ) (s : Sphere d)
    (hp : ambient e f p t s ∈ r.domain) :
    ContMDiffAt 𝓘(ℝ, Parameters e d) (𝓡 n) ∞ (fun q ↦ map e r f q t s) p := by
  have ha : ContDiff ℝ ∞ (fun q : Parameters e d ↦ ambient e f q t s) := by
    change ContDiff ℝ ∞ (fun q ↦ e.toFun (f t s) +
      cutoff t • AffinePerturbation.evaluation (s : Vector (d + 1)) q)
    have hL : ContDiff ℝ ∞
        (AffinePerturbation.evaluation (F := Vector e.ambientDimension) (s : Vector (d + 1))) :=
      (AffinePerturbation.evaluation (F := Vector e.ambientDimension) (s : Vector (d + 1))).contDiff
    exact contDiff_const.add (hL.const_smul (cutoff t))
  change ContMDiffAt 𝓘(ℝ, Parameters e d) (𝓡 n) ∞
    (r.toFun ∘ fun q ↦ ambient e f q t s) p
  exact (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)).comp p ha.contMDiff.contMDiffAt

theorem mfderiv_map_parameter (p : Parameters e d) (t : ℝ) (s : Sphere d)
    (hp : ambient e f p t s ∈ r.domain) :
    mfderiv 𝓘(ℝ, Parameters e d) (𝓡 n) (fun q ↦ map e r f q t s) p =
      (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t s)).comp
        (cutoff t • AffinePerturbation.evaluation (s : Vector (d + 1))) := by
  have ha := hasFDerivAt_ambient_parameter e f p t s
  have hr := (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)).mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, Parameters e d) (𝓡 n)
    (r.toFun ∘ fun q ↦ ambient e f q t s) p = _
  rw [mfderiv_comp p hr ha.hasMFDerivAt.mdifferentiableAt, mfderiv_eq_fderiv, ha.fderiv]
  rfl

theorem surjective_mfderiv_map_parameter (p : Parameters e d) (t : ℝ) (s : Sphere d)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hp : ambient e f p t s ∈ r.domain) :
    Surjective (mfderiv 𝓘(ℝ, Parameters e d) (𝓡 n) (fun q ↦ map e r f q t s) p) := by
  rw [mfderiv_map_parameter e r f p t s hp]
  intro v
  obtain ⟨w, hw⟩ := r.submersive (ambient e f p t s) hp v
  obtain ⟨q, hq⟩ := AffinePerturbation.surjective_smul_evaluation
    (F := Vector e.ambientDimension) (s : Vector (d + 1))
    (cutoff_pos ht).ne' w
  refine ⟨q, ?_⟩
  change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t s)
    ((cutoff t • AffinePerturbation.evaluation
      (F := Vector e.ambientDimension) (s : Vector (d + 1))) q) = v
  rw [hq, hw]

theorem surjective_mfderiv_pair_parameter (p : Parameters e d) (t : ℝ) (s z : Sphere d)
    (hsz : s ≠ z) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hp : ambient e f p t s ∈ r.domain) (hq : ambient e f p t z ∈ r.domain) :
    Surjective (mfderiv 𝓘(ℝ, Parameters e d) ((𝓡 n).prod (𝓡 n))
      (fun q ↦ (map e r f q t s, map e r f q t z)) p) := by
  have hs := (contMDiffAt_map_parameter e r f p t s hp).mdifferentiableAt (by simp)
  have hz := (contMDiffAt_map_parameter e r f p t z hq).mdifferentiableAt (by simp)
  rw [mfderiv_prodMk hs hz, mfderiv_map_parameter e r f p t s hp,
    mfderiv_map_parameter e r f p t z hq]
  rintro ⟨v₁, v₂⟩
  obtain ⟨w₁, hw₁⟩ := r.submersive (ambient e f p t s) hp v₁
  obtain ⟨w₂, hw₂⟩ := r.submersive (ambient e f p t z) hq v₂
  have hsz' : (s : Vector (d + 1)) ≠ (z : Vector (d + 1)) := fun h ↦ hsz (Subtype.ext h)
  obtain ⟨q, hq⟩ := AffinePerturbation.surjective_smul_pairEvaluation
    (F := Vector e.ambientDimension) (s : Vector (d + 1)) (z : Vector (d + 1)) hsz'
    (cutoff_pos ht).ne' (w₁, w₂)
  have h₁ := congrArg Prod.fst hq
  have h₂ := congrArg Prod.snd hq
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (s : Vector (d + 1))) q = w₁ at h₁
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (z : Vector (d + 1))) q = w₂ at h₂
  refine ⟨q, Prod.ext ?_ ?_⟩
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t s)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (s : Vector (d + 1))) q) = v₁
    rw [h₁, hw₁]
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t z)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (z : Vector (d + 1))) q) = v₂
    rw [h₂, hw₂]

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

