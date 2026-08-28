import Wikipedia.NoExoticSixSphere.QuaternionicHopfRegularFiber
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-!
# The actual smooth Hopf regular fiber is the standard three-sphere

The first-axis parametrization has injective ORIGINAL native derivative.
The regular-fiber atlas constructed from the proved submersion therefore
makes it a diffeomorphism from the standard three-sphere, with its exact
ambient inclusion retained. No framing class or Hopf invariant is assigned
by this atlas comparison.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

theorem fiberPoint_injective : Function.Injective fiberPoint := by
  intro p q hpq
  apply Subtype.ext
  have h := congrArg (fun x : Sphere 7 ↦ Quaternion.linearIsometryEquivTuple (first x.val)) hpq
  simpa only [first_fiberPoint, LinearIsometryEquiv.apply_symm_apply] using h

theorem fiberPoint_mfderiv_injective (q : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 7) fiberPoint q) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hsource : ContMDiff (𝓡 3) 𝓘(ℝ, V 4) ∞ (Subtype.val : Sphere 3 → V 4) :=
    contMDiff_coe_sphere
  have htarget : ContMDiff (𝓡 7) 𝓘(ℝ, V 8) ∞ (Subtype.val : Sphere 7 → V 8) :=
    contMDiff_coe_sphere
  have he : (Subtype.val : Sphere 7 → V 8) ∘ fiberPoint =
      axis.toContinuousLinearMap ∘ (Subtype.val : Sphere 3 → V 4) := rfl
  have hd := congrArg (sphereAmbientDerivative q) he
  unfold sphereAmbientDerivative at hd
  rw [mfderiv_comp q (htarget.mdifferentiableAt (by simp))
      (contMDiff_fiberPoint.mdifferentiableAt (by simp)),
    mfderiv_comp q axis.toContinuousLinearMap.differentiableAt.mdifferentiableAt
      (hsource.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hd
  intro v w hvw
  apply mfderiv_coe_sphere_injective (n := 3) q
  apply axis.injective
  have hv := congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L v) hd
  have hw := congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L w) hd
  exact hv.symm.trans ((congrArg
    (mfderiv (𝓡 7) 𝓘(ℝ, V 8) (Subtype.val : Sphere 7 → V 8) (fiberPoint q)) hvw).trans hw)

theorem sphereMap_fiber_range (x : Sphere 7) :
    sphereMap x = spherePole 4 ↔ ∃ q : Sphere 3, fiberPoint q = x := by
  constructor
  · intro hx
    exact ⟨fiberInverse ⟨x, hx⟩, fiberPoint_fiberInverse ⟨x, hx⟩⟩
  · rintro ⟨q, rfl⟩
    exact sphereMap_fiberPoint q

def fiberDiffeomorph :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap (spherePole 4) north_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    Sphere 3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ {x : Sphere 7 // sphereMap x = spherePole 4} :=
  diffeomorphToRegularFiber sphereMap contMDiff_sphereMap (spherePole 4) north_regular 3
    (by simp only [finrank_euclideanSpace_fin]) fiberPoint contMDiff_fiberPoint
    fiberPoint_injective fiberPoint_mfderiv_injective sphereMap_fiber_range

theorem fiberDiffeomorph_val (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap (spherePole 4) north_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (fiberDiffeomorph q).val = fiberPoint q := rfl

end NoExoticSixSphere.QuaternionicHopf
