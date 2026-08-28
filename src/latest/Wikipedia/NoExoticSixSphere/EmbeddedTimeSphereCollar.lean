import Wikipedia.NoExoticSixSphere.InwardSphereCollar
import Wikipedia.NoExoticSixSphere.EmbeddedTimeInwardFrame

/-!
# An actual inward smooth collar for a sphere in the regular time-zero boundary

Radially extend the original embedded sphere and its inward unit time-gradient,
then apply the actual tubular retraction. The retraction fixes the entire
boundary differential because that differential lies in the original tangent
image. The time derivative in the outward radial direction is strictly negative.
The manifold and zero fiber keep their original native smooth structures.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EmbeddedTime

open GLOrthonormalization

variable {n p : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector (n + 1)) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] (e : EuclideanEmbedding (n + 1) M)
  (r : e.TubularRetraction) (t : C(M, ℝ))
  (ht : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ t)
  (hreg : ∀ x, t x = 0 → Surjective (mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) t x))

theorem inwardNormal_mem_tangent (q : {x : M // t x = 0}) :
    inwardNormal e r t q ∈ e.tangentImage q.val :=
  (e.tangentImage q.val).neg_mem (outwardNormal_mem_tangent e r t q)

include ht hreg in
theorem timeCovector_inward (q : {x : M // t x = 0}) :
    timeCovector e r t q.val (inwardNormal e r t q) = ‖gradient e r t q.val‖ := by
  change timeCovector e r t q.val (-outwardNormal e r t q) = _
  rw [map_neg, timeCovector_outward e r t ht hreg, neg_neg]

theorem timeCovector_zeroDerivative (q : {x : M // t x = 0}) (v : Vector n) :
    timeCovector e r t q.val (zeroDerivative e t ht hreg q v) = 0 := by
  let := zeroAtlas t ht hreg
  let := zero_isManifold t ht hreg
  exact inner_gradient_zero_derivative e t ht hreg r q v

def sphereCollarAmbient (b : Sphere p) (f : Sphere p → {x : M // t x = 0}) :
    Vector (p + 1) → Vector e.ambientDimension :=
  InwardSphereCollar.map b (fun s ↦ e.toFun (f s).val) (fun s ↦ inwardNormal e r t (f s))

def sphereCollar (b : Sphere p) (f : Sphere p → {x : M // t x = 0}) :
    Vector (p + 1) → M := r.toFun ∘ sphereCollarAmbient e r t b f

omit [IsManifold (𝓡 (n + 1)) ∞ M] in
theorem sphereCollarAmbient_coe (b : Sphere p) (f : Sphere p → {x : M // t x = 0})
    (s : Sphere p) : sphereCollarAmbient e r t b f s.val = e.toFun (f s).val :=
  InwardSphereCollar.map_coe b _ _ s

theorem sphereCollar_coe (b : Sphere p) (f : Sphere p → {x : M // t x = 0})
    (s : Sphere p) : sphereCollar e r t b f s.val = (f s).val := by
  change r.toFun (sphereCollarAmbient e r t b f s.val) = (f s).val
  rw [sphereCollarAmbient_coe, r.fixes]

theorem contDiff_sphereCollarAmbient (b : Sphere p) (f : Sphere p → {x : M // t x = 0}) :
    letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → ContDiff ℝ ∞ (sphereCollarAmbient e r t b f) := by
  let := zeroAtlas t ht hreg
  intro hf
  exact InwardSphereCollar.contDiff_map b _ _
    ((zeroEmbedding e t ht hreg).smooth.comp hf)
    ((contMDiff_inwardNormal e r t ht hreg).comp hf)

theorem contMDiffAt_sphereCollar_coe (b : Sphere p) (f : Sphere p → {x : M // t x = 0})
    (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      ContMDiffAt (𝓡 (p + 1)) (𝓡 (n + 1)) ∞ (sphereCollar e r t b f) s.val := by
  let := zeroAtlas t ht hreg
  intro hf
  have hA := contDiff_sphereCollarAmbient e r t ht hreg b f hf
  have hr := r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds
    (r.contains ⟨(f s).val, rfl⟩))
  have hr' : ContMDiffAt (𝓡 e.ambientDimension) (𝓡 (n + 1)) ∞ r.toFun
      (sphereCollarAmbient e r t b f s.val) := by
    rw [sphereCollarAmbient_coe]
    exact hr
  exact hr'.comp s.val hA.contMDiff.contMDiffAt

theorem sphereDerivative_mem_zero_tangent (f : Sphere p → {x : M // t x = 0})
    (s : Sphere p) (v : Vector p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      mfderiv (𝓡 p) (𝓡 e.ambientDimension) (fun s ↦ e.toFun (f s).val) s v ∈
        (zeroDerivative e t ht hreg (f s)).range := by
  let := zeroAtlas t ht hreg
  intro hf
  have hD := mfderiv_comp s ((zeroEmbedding e t ht hreg).smooth.mdifferentiableAt
    (by simp)) (hf.mdifferentiableAt (by simp))
  change mfderiv (𝓡 p) (𝓡 e.ambientDimension) (fun s ↦ e.toFun (f s).val) s =
    (zeroDerivative e t ht hreg (f s)).comp (mfderiv (𝓡 p) (𝓡 n) f s) at hD
  rw [hD]
  exact ⟨_, rfl⟩

theorem fderiv_sphereCollarAmbient_mem_tangent (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) (v : Vector (p + 1)) :
    letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      fderiv ℝ (sphereCollarAmbient e r t b f) s.val v ∈ e.tangentImage (f s).val := by
  let := zeroAtlas t ht hreg
  intro hf
  have hF : ContMDiff (𝓡 p) (𝓡 e.ambientDimension) ∞ (fun s ↦ e.toFun (f s).val) :=
    (zeroEmbedding e t ht hreg).smooth.comp hf
  have hN : ContMDiff (𝓡 p) (𝓡 e.ambientDimension) ∞ (fun s ↦ inwardNormal e r t (f s)) :=
    (contMDiff_inwardNormal e r t ht hreg).comp hf
  rw [sphereCollarAmbient, InwardSphereCollar.fderiv_map_coe b _ _ hF hN]
  apply (e.tangentImage (f s).val).sub_mem
  · obtain ⟨w, hw⟩ := SmoothSphereAmbient.range_fderiv_extension_le b _ hF s ⟨v, rfl⟩
    have hm := zero_tangent_le e t ht hreg (f s)
      (sphereDerivative_mem_zero_tangent e t ht hreg f s w hf)
    exact hw ▸ hm
  · exact (e.tangentImage (f s).val).smul_mem _ (inwardNormal_mem_tangent e r t (f s))

theorem fderiv_embedded_sphereCollar_coe (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      fderiv ℝ (e.toFun ∘ sphereCollar e r t b f) s.val =
        fderiv ℝ (sphereCollarAmbient e r t b f) s.val := by
  let := zeroAtlas t ht hreg
  intro hf
  have hA := contDiff_sphereCollarAmbient e r t ht hreg b f hf
  have hg := contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  have hr : ContMDiffAt (𝓡 e.ambientDimension) (𝓡 (n + 1)) ∞ r.toFun
      (sphereCollarAmbient e r t b f s.val) := by
    rw [sphereCollarAmbient_coe]
    exact r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds (r.contains ⟨(f s).val, rfl⟩))
  let Dg : Vector (p + 1) →L[ℝ] Vector (n + 1) :=
    mfderiv (𝓡 (p + 1)) (𝓡 (n + 1)) (sphereCollar e r t b f) s.val
  have hD : Dg = (mfderiv (𝓡 e.ambientDimension) (𝓡 (n + 1)) r.toFun
      (e.toFun (f s).val)).comp (fderiv ℝ (sphereCollarAmbient e r t b f) s.val) := by
    have h := mfderiv_comp s.val (hr.mdifferentiableAt (by simp))
      (hA.contMDiff.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    change Dg = (mfderiv (𝓡 e.ambientDimension) (𝓡 (n + 1)) r.toFun
      (sphereCollarAmbient e r t b f s.val)).comp
        (fderiv ℝ (sphereCollarAmbient e r t b f) s.val) at h
    rw [sphereCollarAmbient_coe] at h
    exact h
  have hE : fderiv ℝ (e.toFun ∘ sphereCollar e r t b f) s.val =
      (embeddingDerivative e (f s).val).comp Dg := by
    have h := mfderiv_comp s.val (e.smooth.mdifferentiableAt (by simp))
      (hg.mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    change fderiv ℝ (e.toFun ∘ sphereCollar e r t b f) s.val =
      (embeddingDerivative e (sphereCollar e r t b f s.val)).comp Dg at h
    rw [sphereCollar_coe] at h
    exact h
  apply ContinuousLinearMap.ext
  intro v
  rw [hE, hD]
  change mfderiv (𝓡 (n + 1)) (𝓡 e.ambientDimension) e.toFun (f s).val
    (mfderiv (𝓡 e.ambientDimension) (𝓡 (n + 1)) r.toFun (e.toFun (f s).val)
      (fderiv ℝ (sphereCollarAmbient e r t b f) s.val v)) = _
  exact r.mfderiv_embedding_retract_tangent (f s).val _
    (fderiv_sphereCollarAmbient_mem_tangent e r t ht hreg b f s v hf)

theorem fderiv_time_sphereCollar_radial (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f →
      fderiv ℝ (t ∘ sphereCollar e r t b f) s.val s.val =
        -2 * ‖gradient e r t (f s).val‖ := by
  let := zeroAtlas t ht hreg
  intro hf
  have hg := contMDiffAt_sphereCollar_coe e r t ht hreg b f s hf
  have hF : ContMDiff (𝓡 p) (𝓡 e.ambientDimension) ∞ (fun s ↦ e.toFun (f s).val) :=
    (zeroEmbedding e t ht hreg).smooth.comp hf
  have hN : ContMDiff (𝓡 p) (𝓡 e.ambientDimension) ∞ (fun s ↦ inwardNormal e r t (f s)) :=
    (contMDiff_inwardNormal e r t ht hreg).comp hf
  rw [← timeCovector_composedDerivative e r t ht _ s.val hg s.val,
    sphereCollar_coe, fderiv_embedded_sphereCollar_coe e r t ht hreg b f s hf]
  change timeCovector e r t (f s).val
    (fderiv ℝ (InwardSphereCollar.map b _ _) s.val s.val) = _
  rw [InwardSphereCollar.fderiv_map_radial b _ _ hF hN,
    map_smul, timeCovector_inward e r t ht hreg]
  rfl

theorem fderiv_time_sphereCollar_radial_neg (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ContMDiff (𝓡 p) (𝓡 n) ∞ f → fderiv ℝ (t ∘ sphereCollar e r t b f) s.val s.val < 0 := by
  let := zeroAtlas t ht hreg
  intro hf
  rw [fderiv_time_sphereCollar_radial e r t ht hreg b f s hf]
  exact mul_neg_of_neg_of_pos (by norm_num)
    (norm_pos_iff.mpr (gradient_ne_zero e r t ht (f s).val (hreg (f s).val (f s).property)))

theorem injective_fderiv_sphereCollarAmbient_coe (b : Sphere p)
    (f : Sphere p → {x : M // t x = 0}) (s : Sphere p) : letI := zeroAtlas t ht hreg;
    ∀ (_ : ContMDiff (𝓡 p) (𝓡 n) ∞ f)
      (_ : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 n) f q)),
      Injective (fderiv ℝ (sphereCollarAmbient e r t b f) s.val) := by
  let := zeroAtlas t ht hreg
  intro hf hd
  have hF : ContMDiff (𝓡 p) (𝓡 e.ambientDimension) ∞ (fun s ↦ e.toFun (f s).val) :=
    (zeroEmbedding e t ht hreg).smooth.comp hf
  have hN : ContMDiff (𝓡 p) (𝓡 e.ambientDimension) ∞ (fun s ↦ inwardNormal e r t (f s)) :=
    (contMDiff_inwardNormal e r t ht hreg).comp hf
  have hfi : ∀ q, Injective (mfderiv (𝓡 p) (𝓡 e.ambientDimension)
      (fun s ↦ e.toFun (f s).val) q) := by
    intro q
    have hD := mfderiv_comp q ((zeroEmbedding e t ht hreg).smooth.mdifferentiableAt
      (by simp)) (hf.mdifferentiableAt (by simp))
    change mfderiv (𝓡 p) (𝓡 e.ambientDimension) (fun s ↦ e.toFun (f s).val) q =
      (zeroDerivative e t ht hreg (f q)).comp (mfderiv (𝓡 p) (𝓡 n) f q) at hD
    rw [hD]
    exact ((zeroEmbedding e t ht hreg).injective_mfderiv (f q)).comp (hd q)
  refine InwardSphereCollar.injective_fderiv_map_coe b _ _ hF hN hfi s
    (timeCovector e r t (f s).val) ?_ ?_
  · intro w
    obtain ⟨v, hv⟩ := sphereDerivative_mem_zero_tangent e t ht hreg f s w hf
    exact (congrArg (timeCovector e r t (f s).val) hv).symm.trans
      (timeCovector_zeroDerivative e r t ht hreg (f s) v)
  · rw [timeCovector_inward e r t ht hreg]
    exact norm_ne_zero_iff.mpr
      (gradient_ne_zero e r t ht (f s).val (hreg (f s).val (f s).property))

end NoExoticSixSphere.EmbeddedTime
