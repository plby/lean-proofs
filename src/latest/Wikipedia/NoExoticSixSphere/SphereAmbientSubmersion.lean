import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Actual sphere submersions from their ambient polynomial differential

The inclusion differential identifies the native tangent space with
the orthogonal hyperplane. The chain rule therefore transfers a
surjective ambient differential on those hyperplanes to surjectivity
of the ORIGINAL native manifold derivative.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace NoExoticSixSphere

def sphereAmbientDerivative {m n : ℕ} (x : Sphere m)
    (g : Sphere m → EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  mfderiv (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) g x

theorem sphereMap_mfderiv_surjective_of_ambient {m n : ℕ}
    (F : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (f : Sphere m → Sphere n) (hF : ContDiff ℝ ∞ F) (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f)
    (he : ∀ x, (f x).val = F x.val) (x : Sphere m)
    (hs : ∀ z : EuclideanSpace ℝ (Fin (n + 1)), inner ℝ (f x).val z = 0 →
      ∃ v : EuclideanSpace ℝ (Fin (m + 1)),
        inner ℝ x.val v = 0 ∧ fderiv ℝ F x.val v = z) :
    Function.Surjective (mfderiv (𝓡 m) (𝓡 n) f x) := by
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)) :=
    mfderiv (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
    (Subtype.val : Sphere m → EuclideanSpace ℝ (Fin (m + 1))) x
  let B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    mfderiv (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
    (Subtype.val : Sphere n → EuclideanSpace ℝ (Fin (n + 1))) (f x)
  have hsource : ContMDiff (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (Subtype.val : Sphere m → EuclideanSpace ℝ (Fin (m + 1))) := contMDiff_coe_sphere
  have htarget : ContMDiff (𝓡 n) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) ∞
      (Subtype.val : Sphere n → EuclideanSpace ℝ (Fin (n + 1))) := contMDiff_coe_sphere
  have hmaps : (Subtype.val : Sphere n → EuclideanSpace ℝ (Fin (n + 1))) ∘ f =
      F ∘ (Subtype.val : Sphere m → EuclideanSpace ℝ (Fin (m + 1))) := funext he
  have hD : B.comp (mfderiv (𝓡 m) (𝓡 n) f x) = (fderiv ℝ F x.val).comp A := by
    have hd := congrArg (sphereAmbientDerivative x) hmaps
    unfold sphereAmbientDerivative at hd
    rw [mfderiv_comp x (htarget.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp)),
      mfderiv_comp x (hF.differentiable (by simp) x.val).mdifferentiableAt
        (hsource.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hd
    exact hd
  intro w
  have hw : B w ∈ (ℝ ∙ (f x).val)ᗮ := by
    rw [← range_mfderiv_coe_sphere (n := n) (f x)]
    exact ⟨w, rfl⟩
  obtain ⟨v, hv, hz⟩ := hs (B w) (Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw)
  have hv' : v ∈ A.range := by
    change v ∈ (mfderiv (𝓡 m) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
      (Subtype.val : Sphere m → EuclideanSpace ℝ (Fin (m + 1))) x).range
    rw [range_mfderiv_coe_sphere]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  obtain ⟨u, hu⟩ := hv'
  refine ⟨u, mfderiv_coe_sphere_injective (n := n) (f x) ?_⟩
  change B (mfderiv (𝓡 m) (𝓡 n) f x u) = B w
  have happ := congrArg (fun L : EuclideanSpace ℝ (Fin m) →L[ℝ]
    EuclideanSpace ℝ (Fin (n + 1)) ↦ L u) hD
  exact happ.trans ((congrArg (fderiv ℝ F x.val) hu).trans hz)

end NoExoticSixSphere
