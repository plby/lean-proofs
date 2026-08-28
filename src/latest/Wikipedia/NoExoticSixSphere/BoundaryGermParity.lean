import Wikipedia.NoExoticSixSphere.OutwardGraphParityCriterion

/-!
# Boundary parity uses only the actual boundary germ

The radial differential is continuous on the sphere under pointwise
smoothness there, and the native chain rule gives the tangential identity.
Thus the original collar homotopy and outward graph comparison require
no map or smoothness on the missing interior of an annulus.
-/

noncomputable section

open Function
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere

open GLOrthonormalization Stiefel DiskBoundary
open SphereThreeTangentFrame CollaredDiskFrame SpanningDiskFrameCoordinates

namespace CollaredDiskFrame

theorem boundary_tangent_derivative_at {N : ℕ} (F : Vector 4 → Vector N × ℝ)
    (g : Sphere 3 → Vector N) (hg : ContMDiff (𝓡 3) (𝓡 N) ∞ g)
    (hb : ∀ s : Sphere 3, F s.val = (g s, 0))
    (s : Sphere 3) (hF : DifferentiableAt ℝ F s.val) (u : Vector 3) :
    fderiv ℝ F s.val (operator s.val u) = (framedDerivative g s u, 0) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) := contMDiff_coe_sphere
  have h₀ := framedDerivative_outer_comp_at F (Subtype.val : Sphere 3 → Vector 4) s hF
    (hs.mdifferentiableAt (by simp))
  rw [framedDerivative_coe] at h₀
  have he : F ∘ (Subtype.val : Sphere 3 → Vector 4) =
      (ContinuousLinearMap.inl ℝ (Vector N) ℝ) ∘ g := funext hb
  rw [he] at h₀
  have h₁ := framedDerivative_outer_comp_at (ContinuousLinearMap.inl ℝ (Vector N) ℝ)
    g s (ContinuousLinearMap.inl ℝ (Vector N) ℝ).differentiableAt
    (hg.mdifferentiableAt (by simp))
  rw [ContinuousLinearMap.fderiv] at h₁
  exact congrArg (fun L : Vector 3 →L[ℝ] (Vector N × ℝ) ↦ L u) (h₀.symm.trans h₁)

def sphereDifferential {N : ℕ} (F : Vector 4 → Vector N × ℝ)
    (hF : ∀ s : Sphere 3, ContDiffAt ℝ ∞ F s.val) :
    C(Sphere 3, Vector 4 →L[ℝ] (Vector N × ℝ)) where
  toFun s := fderiv ℝ F s.val
  continuous_toFun := continuous_iff_continuousAt.mpr (fun s ↦
    ((hF s).continuousAt_fderiv (by simp)).comp continuous_subtype_val.continuousAt)

end CollaredDiskFrame

namespace EuclideanEmbedding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

theorem boundaryGermOperator_homotopic_raw_twisted
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ s : Sphere 3, ContDiffAt ℝ ∞ F s.val)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (B : C(Sphere 3,
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hB : ∀ s, (B s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    B.Homotopic (twistedBlockMap (e.rawSphereFrameOperatorMap a f hf hd)) := by
  let aS : C(Sphere 3, e.NormalModel →L[ℝ] Vector e.ambientDimension) :=
    ⟨fun s ↦ a.ambient (f s), a.contMDiff_ambient.continuous.comp hf.continuous⟩
  let TS : C(Sphere 3, Vector 3 →L[ℝ] Vector e.ambientDimension) :=
    ⟨framedDerivative (e.toFun ∘ f), e.continuous_sphereTangentOperator f hf⟩
  let R : C(Sphere 3, Vector e.ambientDimension × ℝ) :=
    ⟨fun s ↦ fderiv ℝ F s.val s.val,
      (sphereDifferential F hF).continuous.clm_apply continuous_subtype_val⟩
  let v := (ContinuousMap.fst : C(Vector e.ambientDimension × ℝ, _)).comp R
  let c := (ContinuousMap.snd : C(Vector e.ambientDimension × ℝ, ℝ)).comp R
  have haS : ∀ s, Injective (aS s) := fun s ↦ a.ambient_injective (f s)
  have hTS : ∀ s, Injective (TS s) := e.injective_sphereTangentOperator f hf hd
  have hrS : ∀ s, Disjoint (aS s).range (TS s).range := e.rawSphereNormal_range_disjoint a f hf
  have he : sphereOperatorMap aS TS haS hTS hrS = e.rawSphereFrameOperatorMap a f hf hd := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    rfl
  have hBC : B = collarMap aS TS v c haS hTS hrS hheight := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    change (B s).val = combined
      ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (aS s))
      (collarDerivative s (TS s) (v s) (c s))
    rw [hB, eq_collarDerivative_of_tangent_radial s (TS s) (fderiv ℝ F s.val) (v s) (c s)
      (boundary_tangent_derivative_at F (e.toFun ∘ f) (e.smooth.comp hf) hb s
        ((hF s).differentiableAt (by simp))) rfl]
    rfl
  rw [hBC, ← he]
  exact ⟨collarHomotopy aS TS v c haS hTS hrS hheight⟩

theorem sphereParity_zero_iff_boundaryGermOperator_extends
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ s : Sphere 3, ContDiffAt ℝ ∞ F s.val)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (B : C(Sphere 3,
      Monomorphism.Space (e.ambientDimension + 6) (((e.ambientDimension - 6) + 5) + 4)))
    (hB : ∀ s, (B s).val =
      combined ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp
        (a.ambient (f s))) (fderiv ℝ F s.val))
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    e.sphereParity a f hf hi hd = 0 ↔ Extends B :=
  (e.sphereParity_zero_iff_raw_twisted_extension a f hf hd hi).trans
    (extends_homotopic_iff
      (e.boundaryGermOperator_homotopic_raw_twisted a f hf hd F hF hb B hB hheight)).symm

open OutwardGraphFrame

theorem sphereParity_zero_iff_outwardGermOperator_extends {k : ℕ}
    (hN : e.ambientDimension = 3 + (k + 4))
    (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (F : Vector 4 → Vector e.ambientDimension × ℝ)
    (hF : ∀ s : Sphere 3, ContDiffAt ℝ ∞ F s.val)
    (hb : ∀ s : Sphere 3, F s.val = (e.toFun (f s), 0))
    (A : C(Sphere 3, Vector k →L[ℝ] Vector e.ambientDimension))
    (D : C(Sphere 3, Vector 4 →L[ℝ] Vector e.ambientDimension))
    (ν : C(Sphere 3, Vector e.ambientDimension))
    (ξ : C(Sphere 3, Vector e.ambientDimension →L[ℝ] ℝ))
    (Q : e.NormalModel ≃L[ℝ] Vector (k + 1))
    (P : C(Sphere 3, Monomorphism.Space e.ambientDimension (k + 4)))
    (hP : ∀ s, (P s).val = OperatorSum.operator (A s) (D s))
    (ha : ∀ s, a.ambient (f s) =
      (OrthogonalFrameAppend.operator (A s) (ν s)).comp Q.toContinuousLinearMap)
    (hD : ∀ s : Sphere 3, fderiv ℝ F s.val = graph (D s) (ξ s))
    (hA : ∀ s u, ξ s (A s u) = 0) (hν : ∀ s, ξ s (ν s) < 0)
    (hheight : ∀ s : Sphere 3, 0 < (fderiv ℝ F s.val s.val).2) :
    e.sphereParity a f hf hi hd = 0 ↔ Extends P := by
  have hAD : ∀ s, Injective ((A s).coprod (D s)) :=
    fun s ↦ coprod_injective_of_operator (P s) (A s) (D s) (hP s)
  let G := outwardMap A D ν ξ Q hAD hA hν
  have hG (s : Sphere 3) : (G s).val = combined
      ((ContinuousLinearMap.inl ℝ (Vector e.ambientDimension) ℝ).comp (a.ambient (f s)))
      (fderiv ℝ F s.val) := by
    rw [ha, hD]
    exact outwardMap_value A D ν ξ Q hAD hA hν s
  exact (e.sphereParity_zero_iff_boundaryGermOperator_extends a f hf hi hd F hF hb G hG
    hheight).trans (extends_outward_normalCoordinates_iff hN A D ν ξ Q P G hP
      (outwardMap_value A D ν ξ Q hAD hA hν) hA hν)

end EuclideanEmbedding
end NoExoticSixSphere
