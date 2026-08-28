import Wikipedia.HopfProblem.DegreeCollapseTwoSphereEmbeddingFamily
import Wikipedia.HopfProblem.OrbitPairEmbeddingIsotopyExtension
import Wikipedia.SmoothSixDPoincare.SmoothConnectingCurve

/-!
# Native ambient isotopy of homotopic embedded two-spheres

Smooth the actual homotopy and extend it to stationary real-time ends.
The constructed affine parameter removes all collisions and derivative
kernels while preserving those ends. Native embedding-family extension
then gives an ambient diffeomorphism isotopic to the identity, with the
entire original two-sphere parametrization retained.

An actual Euclidean embedding and tubular retraction are inputs here;
the regular-level application constructs them from the original state.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding
open Wikipedia.SmoothSixDPoincare

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)

include e r in
theorem exists_native_isotopy_of_two_sphere_homotopy (hdim : 5 < n)
    (γ δ : C(Sphere 2, M))
    (hγ : ContMDiff (𝓡 2) (𝓡 n) ∞ γ) (hγi : Injective γ)
    (hγd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) γ x))
    (hδ : ContMDiff (𝓡 2) (𝓡 n) ∞ δ) (hδi : Injective δ)
    (hδd : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) δ x))
    (hhom : γ.Homotopic δ) :
    ∃ D : Diffeomorph (𝓡 n) (𝓡 n) M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity D ∧ ∀ x, D (γ x) = δ x := by
  obtain ⟨H⟩ := hhom
  obtain ⟨H', hH', _, _⟩ :=
    ManifoldSmoothing.exists_smooth_homotopy_with_collars hγ hδ H
  let f : ℝ → Sphere 2 → M := fun t x => H' (CurveImmersion.smoothTime t, x)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f) :=
    hH'.comp ((CurveImmersion.contMDiff_smoothTime.comp contMDiff_fst).prodMk contMDiff_snd)
  have hleft (t : ℝ) (ht : t ≤ 0) : f t = γ := by
    have h0 : CurveImmersion.smoothTime t = 0 := by
      apply Subtype.ext
      change (projIcc (0 : ℝ) 1 zero_le_one (Real.smoothTransition t)).val = 0
      rw [Real.smoothTransition.zero_of_nonpos ht]
      simp
    funext x
    change H' (CurveImmersion.smoothTime t, x) = γ x
    rw [h0, H'.apply_zero]
  have hright (t : ℝ) (ht : 1 ≤ t) : f t = δ := by
    have h1 : CurveImmersion.smoothTime t = 1 := by
      apply Subtype.ext
      change (projIcc (0 : ℝ) 1 zero_le_one (Real.smoothTransition t)).val = 1
      rw [Real.smoothTransition.one_of_one_le ht]
      simp
    funext x
    change H' (CurveImmersion.smoothTime t, x) = δ x
    rw [h1, H'.apply_one]
  obtain ⟨g, hg, hgi, hgd, hfix⟩ := exists_smooth_embedding_family e r f hF hdim
    (fun t ht => by
      rcases ht with ht | ht
      · rw [hleft t ht]; exact hγi
      · rw [hright t ht]; exact hδi)
    (fun t ht => by
      rcases ht with ht | ht
      · rw [hleft t ht]; exact hγd
      · rw [hright t ht]; exact hδd)
  obtain ⟨D, hD, hformula⟩ :=
    OrbitPair.NativeFamily.exists_ambient_diffeomorph_of_embedding_family hg hgi hgd
  refine ⟨D, hD, ?_⟩
  intro x
  have h0 : g 0 x = γ x := (hfix 0 (Or.inl le_rfl) x).trans
    (congrFun (hleft 0 le_rfl) x)
  have h1 : g 1 x = δ x := (hfix 1 (Or.inr le_rfl) x).trans
    (congrFun (hright 1 le_rfl) x)
  have hh : D (g 0 x) = g 1 x := hformula x
  rwa [h0, h1] at hh

end Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation
