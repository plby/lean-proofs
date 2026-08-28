import Wikipedia.NoExoticSixSphere.ManifoldAffineSphereFamily
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

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization RelativeDoublePointPerturbation EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

theorem hasFDerivAt_ambient_parameter (p : Parameters e) (t : ℝ) (s : Sphere 3) :
    HasFDerivAt (fun q : Parameters e ↦ ambient e f q t s)
      (cutoff t • AffinePerturbation.evaluation (s : Vector 4)) p :=
  AffinePerturbation.hasFDerivAt_weighted_value (s : Vector 4) p (cutoff t) (e.toFun (f t s))

theorem contMDiffAt_map_parameter (p : Parameters e) (t : ℝ) (s : Sphere 3)
    (hp : ambient e f p t s ∈ r.domain) :
    ContMDiffAt 𝓘(ℝ, Parameters e) (𝓡 n) ∞ (fun q ↦ map e r f q t s) p := by
  have ha : ContDiff ℝ ∞ (fun q : Parameters e ↦ ambient e f q t s) := by
    change ContDiff ℝ ∞ (fun q ↦ e.toFun (f t s) +
      cutoff t • AffinePerturbation.evaluation (s : Vector 4) q)
    have hL : ContDiff ℝ ∞
        (AffinePerturbation.evaluation (F := Vector e.ambientDimension) (s : Vector 4)) :=
      (AffinePerturbation.evaluation (F := Vector e.ambientDimension) (s : Vector 4)).contDiff
    exact contDiff_const.add (hL.const_smul (cutoff t))
  change ContMDiffAt 𝓘(ℝ, Parameters e) (𝓡 n) ∞
    (r.toFun ∘ fun q ↦ ambient e f q t s) p
  exact (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)).comp p ha.contMDiff.contMDiffAt

theorem mfderiv_map_parameter (p : Parameters e) (t : ℝ) (s : Sphere 3)
    (hp : ambient e f p t s ∈ r.domain) :
    mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) (fun q ↦ map e r f q t s) p =
      (mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t s)).comp
        (cutoff t • AffinePerturbation.evaluation (s : Vector 4)) := by
  have ha := hasFDerivAt_ambient_parameter e f p t s
  have hr := (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds hp)).mdifferentiableAt (by simp)
  change mfderiv 𝓘(ℝ, Parameters e) (𝓡 n)
    (r.toFun ∘ fun q ↦ ambient e f q t s) p = _
  rw [mfderiv_comp p hr ha.hasMFDerivAt.mdifferentiableAt, mfderiv_eq_fderiv, ha.fderiv]
  rfl

theorem surjective_mfderiv_map_parameter (p : Parameters e) (t : ℝ) (s : Sphere 3)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hp : ambient e f p t s ∈ r.domain) :
    Surjective (mfderiv 𝓘(ℝ, Parameters e) (𝓡 n) (fun q ↦ map e r f q t s) p) := by
  rw [mfderiv_map_parameter e r f p t s hp]
  intro v
  obtain ⟨w, hw⟩ := r.submersive (ambient e f p t s) hp v
  obtain ⟨q, hq⟩ := AffinePerturbation.surjective_smul_evaluation
    (F := Vector e.ambientDimension) (s : Vector 4)
    (cutoff_pos ht).ne' w
  refine ⟨q, ?_⟩
  change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t s)
    ((cutoff t • AffinePerturbation.evaluation
      (F := Vector e.ambientDimension) (s : Vector 4)) q) = v
  rw [hq, hw]

theorem surjective_mfderiv_pair_parameter (p : Parameters e) (t : ℝ) (s z : Sphere 3)
    (hsz : s ≠ z) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hp : ambient e f p t s ∈ r.domain) (hq : ambient e f p t z ∈ r.domain) :
    Surjective (mfderiv 𝓘(ℝ, Parameters e) ((𝓡 n).prod (𝓡 n))
      (fun q ↦ (map e r f q t s, map e r f q t z)) p) := by
  have hs := (contMDiffAt_map_parameter e r f p t s hp).mdifferentiableAt (by simp)
  have hz := (contMDiffAt_map_parameter e r f p t z hq).mdifferentiableAt (by simp)
  rw [mfderiv_prodMk hs hz, mfderiv_map_parameter e r f p t s hp,
    mfderiv_map_parameter e r f p t z hq]
  rintro ⟨v₁, v₂⟩
  obtain ⟨w₁, hw₁⟩ := r.submersive (ambient e f p t s) hp v₁
  obtain ⟨w₂, hw₂⟩ := r.submersive (ambient e f p t z) hq v₂
  have hsz' : (s : Vector 4) ≠ (z : Vector 4) := fun h ↦ hsz (Subtype.ext h)
  obtain ⟨q, hq⟩ := AffinePerturbation.surjective_smul_pairEvaluation
    (F := Vector e.ambientDimension) (s : Vector 4) (z : Vector 4) hsz'
    (cutoff_pos ht).ne' (w₁, w₂)
  have h₁ := congrArg Prod.fst hq
  have h₂ := congrArg Prod.snd hq
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (s : Vector 4)) q = w₁ at h₁
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (z : Vector 4)) q = w₂ at h₂
  refine ⟨q, Prod.ext ?_ ?_⟩
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t s)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (s : Vector 4)) q) = v₁
    rw [h₁, hw₁]
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t z)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (z : Vector 4)) q) = v₂
    rw [h₂, hw₂]

end NoExoticSixSphere.ManifoldAffineSphereFamily
