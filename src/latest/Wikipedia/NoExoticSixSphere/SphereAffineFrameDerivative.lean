import Wikipedia.NoExoticSixSphere.SphereProductFrameCancellation

/-!
# The actual sphere-framed derivative of an affine ambient map
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem framedDerivative_coe (s : Sphere 3) :
    framedDerivative (Subtype.val : Sphere 3 → Vector 4) s = operator s.val := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere
  have h := framedDerivative_eq_native (Subtype.val : Sphere 3 → Vector 4) s
    (hs.mdifferentiableAt (by simp))
  exact h.trans (inclusion_comp_nativeFrame s)

theorem framedDerivative_affine (L : Vector 4 →L[ℝ] F) (c : F) (s : Sphere 3) :
    framedDerivative (fun q : Sphere 3 ↦ L q.val + c) s = (L.comp (operator s.val)) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 3) (𝓡 4) ∞ (Subtype.val : Sphere 3 → Vector 4) :=
    contMDiff_coe_sphere
  have h := framedDerivative_outer_comp_at (fun v : Vector 4 ↦ L v + c)
    (Subtype.val : Sphere 3 → Vector 4) s (L.differentiableAt.add_const c)
      (hs.mdifferentiableAt (by simp))
  rw [(L.hasFDerivAt.add_const c).fderiv, framedDerivative_coe] at h
  exact h

end NoExoticSixSphere.SphereThreeTangentFrame
