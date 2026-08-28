import Wikipedia.NoExoticSixSphere.RegularTimeZeroEmbedding
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppend
import Wikipedia.NoExoticSixSphere.SphereNormalization
import Wikipedia.NoExoticSixSphere.SmoothRangeOrthonormalization

/-!
# Full induced normal columns for the actual regular time-zero boundary

Keep the original orthonormal normal columns and append the negative unit
time-gradient. This is the outward direction of the nonnegative time half.
The smooth orthonormal columns span the actual zero-fiber normal space;
neither an arbitrary plane field nor an externally supplied boundary frame
is substituted for it.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

def outwardNormal (p : {x : M // t x = 0}) : Vector e.ambientDimension :=
  -NormedSpace.normalize (gradient e r t p.val)

include ht hreg in
theorem outwardNormal_norm (p : {x : M // t x = 0}) : ‖outwardNormal e r t p‖ = 1 := by
  rw [outwardNormal, norm_neg]
  exact NormedSpace.norm_normalize (gradient_ne_zero e r t ht p.val (hreg p.val p.property))

theorem outwardNormal_mem_tangent (p : {x : M // t x = 0}) :
    outwardNormal e r t p ∈ e.tangentImage p.val :=
  (e.tangentImage p.val).neg_mem
    ((e.tangentImage p.val).smul_mem _ (gradient_mem_tangent e r t p.val))

theorem contMDiff_outwardNormal : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 n) (𝓡 e.ambientDimension) ∞ (outwardNormal e r t) := by
  let := zeroAtlas t ht hreg
  exact (contMDiff_normalize
    ((contMDiff_gradient e r t ht).comp (contMDiff_zeroInclusion t ht hreg))
    (fun p ↦ gradient_ne_zero e r t ht p.val (hreg p.val p.property))).neg

theorem outwardNormal_orthogonal_zero (p : {x : M // t x = 0}) (v : Vector n) :
    inner ℝ (outwardNormal e r t p) (zeroDerivative e t ht hreg p v) = 0 := by
  let := zeroAtlas t ht hreg
  let := zero_isManifold t ht hreg
  simp only [outwardNormal, NormedSpace.normalize, inner_neg_left, real_inner_smul_left,
    inner_gradient_zero_derivative e t ht hreg r p v, mul_zero, neg_zero]

include ht hreg in
theorem extension_outward_eq (p : {x : M // t x = 0}) :
    fderiv ℝ (extension e r t) (e.toFun p.val) (outwardNormal e r t p) =
      -‖gradient e r t p.val‖ := by
  rw [← inner_gradient_tangent e r t p.val _ (outwardNormal_mem_tangent e r t p),
    outwardNormal, NormedSpace.normalize, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, pow_two, ← mul_assoc,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr
      (gradient_ne_zero e r t ht p.val (hreg p.val p.property))), one_mul]

include ht hreg in
theorem extension_outward_neg (p : {x : M // t x = 0}) :
    fderiv ℝ (extension e r t) (e.toFun p.val) (outwardNormal e r t p) < 0 := by
  rw [extension_outward_eq e r t ht hreg p]
  exact neg_lt_zero.mpr
    (norm_pos_iff.mpr (gradient_ne_zero e r t ht p.val (hreg p.val p.property)))

variable (a : SmoothRangeFrame (𝓡 (n + 1)) e.normalProjection e.NormalModel)

theorem outwardNormal_orthogonal_frame (p : {x : M // t x = 0}) (v : e.NormalModel) :
    inner ℝ (outwardNormal e r t p) ((a.orthonormal p.val).val v) = 0 := by
  have ha : (a.orthonormal p.val).val.range = (e.tangentImage p.val)ᗮ :=
    (a.orthonormal_range p.val).trans (e.range_normalProjection p.val)
  exact Submodule.inner_right_of_mem_orthogonal (outwardNormal_mem_tangent e r t p)
    (ha.le ⟨v, rfl⟩)

def zeroColumns (p : {x : M // t x = 0}) :
    Vector ((e.ambientDimension - (n + 1)) + 1) →L[ℝ] Vector e.ambientDimension :=
  OrthogonalFrameAppend.operator (a.orthonormal p.val).val (outwardNormal e r t p)

theorem zeroColumns_congr_time (u : C(M, ℝ)) (hu : u = t)
    (p : {x : M // u x = 0}) (q : {x : M // t x = 0}) (hp : p.val = q.val) :
    zeroColumns e r u a p = zeroColumns e r t a q := by
  subst u
  have hpq : p = q := Subtype.ext hp
  subst q
  rfl

include ht in
theorem zeroColumns_retraction_independent (r' : e.TubularRetraction)
    (p : {x : M // t x = 0}) : zeroColumns e r' t a p = zeroColumns e r t a p := by
  simp only [zeroColumns, outwardNormal, gradient_retraction_independent e r t r' ht p.val]

include ht hreg in
theorem zeroColumns_norm (p : {x : M // t x = 0})
    (v : Vector ((e.ambientDimension - (n + 1)) + 1)) :
    ‖zeroColumns e r t a p v‖ = ‖v‖ :=
  OrthogonalFrameAppend.norm_operator (a.orthonormal p.val) (outwardNormal e r t p)
    (outwardNormal_norm e r t ht hreg p) (outwardNormal_orthogonal_frame e r t a p) v

theorem contMDiff_zeroColumns : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 n) 𝓘(ℝ, Vector ((e.ambientDimension - (n + 1)) + 1) →L[ℝ]
      Vector e.ambientDimension) ∞ (zeroColumns e r t a) := by
  let := zeroAtlas t ht hreg
  exact OrthogonalFrameAppend.contMDiff_operator
    (a.contMDiff_orthonormal.comp (contMDiff_zeroInclusion t ht hreg))
    (contMDiff_outwardNormal e r t ht hreg)

theorem zeroColumns_normal (p : {x : M // t x = 0}) :
    (zeroColumns e r t a p).range ≤ (zeroDerivative e t ht hreg p).rangeᗮ := by
  let := zeroAtlas t ht hreg
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  have ha : (a.orthonormal p.val).val.range = (e.tangentImage p.val)ᗮ :=
    (a.orthonormal_range p.val).trans (e.range_normalProjection p.val)
  have hv : zeroDerivative e t ht hreg p v ∈ e.tangentImage p.val :=
    zero_tangent_le e t ht hreg p ⟨v, rfl⟩
  have ho (u : e.NormalModel) :
      inner ℝ (zeroDerivative e t ht hreg p v) ((a.orthonormal p.val).val u) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hv (ha.le ⟨u, rfl⟩)
  have hn : inner ℝ (zeroDerivative e t ht hreg p v) (outwardNormal e r t p) = 0 :=
    (real_inner_comm _ _).trans (outwardNormal_orthogonal_zero e r t ht hreg p v)
  change inner ℝ (zeroDerivative e t ht hreg p v)
    (OrthogonalFrameAppend.operator (a.orthonormal p.val).val (outwardNormal e r t p) w) = 0
  rw [OrthogonalFrameAppend.operator_apply, inner_add_right, real_inner_smul_right, ho, hn]
  simp

theorem zeroColumns_range (p : {x : M // t x = 0}) :
    (zeroColumns e r t a p).range = (zeroDerivative e t ht hreg p).rangeᗮ := by
  let := zeroAtlas t ht hreg
  apply Submodule.eq_of_le_of_finrank_eq (zeroColumns_normal e r t ht hreg a p)
  let L : Vector ((e.ambientDimension - (n + 1)) + 1) →ₗᵢ[ℝ] Vector e.ambientDimension :=
    ⟨(zeroColumns e r t a p).toLinearMap, zeroColumns_norm e r t ht hreg a p⟩
  rw [LinearMap.finrank_range_of_inj L.injective, finrank_euclideanSpace_fin]
  have hi : Injective (zeroDerivative e t ht hreg p) :=
    (zeroEmbedding e t ht hreg).injective_mfderiv p
  have hd := (zeroDerivative e t ht hreg p).range.finrank_add_finrank_orthogonal
  rw [LinearMap.finrank_range_of_inj hi, finrank_euclideanSpace_fin,
    finrank_euclideanSpace_fin] at hd
  have hN := e.dimension_le_ambient p.val
  omega

end NoExoticSixSphere.EmbeddedTime
