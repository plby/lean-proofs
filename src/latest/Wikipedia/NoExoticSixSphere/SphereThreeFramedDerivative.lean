import Wikipedia.NoExoticSixSphere.SphereThreeTangentFrame
import Wikipedia.NoExoticSixSphere.SphereExtensionDerivative
import Wikipedia.NoExoticSixSphere.SphereExtensionFamily
import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily
import Wikipedia.NoExoticSixSphere.PartialFrameConnectivity

/-!
# Spatial derivatives in the genuine global three-sphere frame

Differentiate the actual smooth radial extension and restrict to the
quaternionic tangent frame. The resulting operator has the range of the
original manifold derivative, and is injective whenever that derivative is.
The original source atlas is retained throughout.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization Stiefel

def inclusionDerivative (s : Sphere 3) : Vector 3 →L[ℝ] Vector 4 :=
  mfderiv (𝓡 3) (𝓡 4) (fun x : Sphere 3 ↦ x.val) s

theorem range_inclusionDerivative (s : Sphere 3) :
    (inclusionDerivative s).range = (ℝ ∙ s.val)ᗮ := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  change (mfderiv (𝓡 3) (𝓡 4) (fun x : Sphere 3 ↦ x.val) s).range = _
  convert! range_mvfderiv_subtypeVal s

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def framedDerivative (f : Sphere 3 → F) (s : Sphere 3) : Vector 3 →L[ℝ] F :=
  (fderiv ℝ (SmoothSphereAmbient.extension (pole 3) f) s.val).comp (operator s.val)

theorem extensionDerivative_comp_inclusion (f : Sphere 3 → F)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ f) (s : Sphere 3) :
    (fderiv ℝ (SmoothSphereAmbient.extension (pole 3) f) s.val).comp
      (inclusionDerivative s) = mfderiv (𝓡 3) 𝓘(ℝ, F) f s := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hc : SmoothSphereAmbient.extension (pole 3) f ∘ (fun x : Sphere 3 ↦ x.val) = f :=
    funext (SmoothSphereAmbient.extension_coe (pole 3) f)
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun x : Sphere 3 ↦ x.val) := contMDiff_coe_sphere
  have h := mfderiv_comp s
    ((SmoothSphereAmbient.contDiff_extension (pole 3) f hf).contMDiff.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))
  rw [hc, mfderiv_eq_fderiv] at h
  exact h.symm

theorem range_framedDerivative (f : Sphere 3 → F)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ f) (s : Sphere 3) :
    (framedDerivative f s).range = (mfderiv (𝓡 3) 𝓘(ℝ, F) f s).range := by
  rw [← extensionDerivative_comp_inclusion f hf s]
  change ((fderiv ℝ (SmoothSphereAmbient.extension (pole 3) f) s.val).toLinearMap.comp
    (operator s.val).toLinearMap).range =
      ((fderiv ℝ (SmoothSphereAmbient.extension (pole 3) f) s.val).toLinearMap.comp
        (inclusionDerivative s).toLinearMap).range
  rw [LinearMap.range_comp, LinearMap.range_comp, range_operator, range_inclusionDerivative]

theorem injective_framedDerivative (f : Sphere 3 → F)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ f) (s : Sphere 3)
    (hinj : Injective (mfderiv (𝓡 3) 𝓘(ℝ, F) f s)) : Injective (framedDerivative f s) := by
  apply (injective_iff_map_eq_zero (framedDerivative f s)).mpr
  intro v hv
  have ht : operator s.val v ∈ (inclusionDerivative s).range := by
    rw [range_inclusionDerivative, ← range_operator]
    exact ⟨v, rfl⟩
  obtain ⟨w, hw⟩ := ht
  have hd : mfderiv (𝓡 3) 𝓘(ℝ, F) f s w = 0 := by
    have he := congrArg (fun L : Vector 3 →L[ℝ] F ↦ L w)
      (extensionDerivative_comp_inclusion f hf s)
    exact he.symm.trans ((congrArg
      (fderiv ℝ (SmoothSphereAmbient.extension (pole 3) f) s.val) hw).trans hv)
  have hw0 : w = 0 := hinj (hd.trans (map_zero _).symm)
  have ht0 : operator s.val v = 0 := by rw [← hw, hw0, map_zero]
  exact (Stiefel.injective (frame s)) (ht0.trans (map_zero _).symm)

theorem contMDiff_framedDerivative_family (f : ℝ → Sphere 3 → F)
    (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, F) ∞ (uncurry f)) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, Vector 3 →L[ℝ] F) ∞
      (fun p : ℝ × Sphere 3 ↦ framedDerivative (f p.1) p.2) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have he := SmoothSphereAmbient.contDiff_extension_family (pole 3) f hf
  have hd := DiskHomotopy.contDiff_spatial_fderiv
    (fun t x ↦ SmoothSphereAmbient.extension (pole 3) (f t) x) he
  have hs : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) 𝓘(ℝ, ℝ × Vector 4) ∞
      (fun p : ℝ × Sphere 3 ↦ (p.1, p.2.val)) :=
    contMDiff_fst.prodMk_space (contMDiff_coe_sphere.comp contMDiff_snd)
  exact (hd.contMDiff.comp hs).clm_comp (contMDiff_frame.comp contMDiff_snd)

end NoExoticSixSphere.SphereThreeTangentFrame
