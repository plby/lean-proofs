import Wikipedia.HopfProblem.DegreeCollapseAffineTripleEvaluation
import Wikipedia.NoExoticSixSphere.ManifoldAffineParameterSubmersion

/-!
# Three-point parameter submersion in the original target manifold

The three ambient affine variations are independent. Applying the original
smooth tubular retraction preserves surjectivity separately at each point.
The resulting derivative is the actual native derivative of the original
manifold-valued perturbation family, at every interior time in its domain.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding ManifoldAffineSphereFamily RelativeDoublePointPerturbation
open AffineTripleParameters

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

theorem surjective_mfderiv_triple_parameter (p : Parameters e) (t : ℝ) (x y z : Sphere 3)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hx : ambient e f p t x ∈ r.domain) (hy : ambient e f p t y ∈ r.domain)
    (hz : ambient e f p t z ∈ r.domain) :
    Surjective (mfderiv 𝓘(ℝ, Parameters e) ((𝓡 n).prod ((𝓡 n).prod (𝓡 n)))
      (fun q ↦ (map e r f q t x, map e r f q t y, map e r f q t z)) p) := by
  have hx' := (contMDiffAt_map_parameter e r f p t x hx).mdifferentiableAt (by simp)
  have hy' := (contMDiffAt_map_parameter e r f p t y hy).mdifferentiableAt (by simp)
  have hz' := (contMDiffAt_map_parameter e r f p t z hz).mdifferentiableAt (by simp)
  rw [mfderiv_prodMk hx' (hy'.prodMk hz'), mfderiv_prodMk hy' hz',
    mfderiv_map_parameter e r f p t x hx, mfderiv_map_parameter e r f p t y hy,
    mfderiv_map_parameter e r f p t z hz]
  rintro ⟨v₁, v₂, v₃⟩
  obtain ⟨w₁, hw₁⟩ := r.submersive (ambient e f p t x) hx v₁
  obtain ⟨w₂, hw₂⟩ := r.submersive (ambient e f p t y) hy v₂
  obtain ⟨w₃, hw₃⟩ := r.submersive (ambient e f p t z) hz v₃
  obtain ⟨q, hq⟩ := surjective_smul_tripleEvaluation (F := Vector e.ambientDimension)
    x y z hxy hxz hyz (cutoff_pos ht).ne' (w₁, w₂, w₃)
  have h₁ := congrArg Prod.fst hq
  have h₂ := congrArg (fun v : Vector e.ambientDimension × Vector e.ambientDimension ×
    Vector e.ambientDimension ↦ v.2.1) hq
  have h₃ := congrArg (fun v : Vector e.ambientDimension × Vector e.ambientDimension ×
    Vector e.ambientDimension ↦ v.2.2) hq
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (x : Vector 4)) q = w₁ at h₁
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (y : Vector 4)) q = w₂ at h₂
  change (cutoff t • AffinePerturbation.evaluation
    (F := Vector e.ambientDimension) (z : Vector 4)) q = w₃ at h₃
  refine ⟨q, Prod.ext ?_ (Prod.ext ?_ ?_)⟩
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t x)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (x : Vector 4)) q) = v₁
    rw [h₁, hw₁]
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t y)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (y : Vector 4)) q) = v₂
    rw [h₂, hw₂]
  · change mfderiv (𝓡 e.ambientDimension) (𝓡 n) r.toFun (ambient e f p t z)
      ((cutoff t • AffinePerturbation.evaluation
        (F := Vector e.ambientDimension) (z : Vector 4)) q) = v₃
    rw [h₃, hw₃]

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters
