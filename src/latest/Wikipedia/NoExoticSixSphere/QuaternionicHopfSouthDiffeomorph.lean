import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthDifferential
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-! # The nonbasepoint Hopf fiber with its actual regular-fiber smooth atlas -/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

theorem southFiberPoint_injective : Function.Injective southFiberPoint := by
  intro p q hpq
  apply Subtype.ext
  exact southAxis.injective (congrArg Subtype.val hpq)

theorem southFiberPoint_mfderiv_injective (q : Sphere 3) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 7) southFiberPoint q) := by
  let : Fact (Module.finrank ℝ (V 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hsource : ContMDiff (𝓡 3) 𝓘(ℝ, V 4) ∞ (Subtype.val : Sphere 3 → V 4) :=
    contMDiff_coe_sphere
  have htarget : ContMDiff (𝓡 7) 𝓘(ℝ, V 8) ∞ (Subtype.val : Sphere 7 → V 8) :=
    contMDiff_coe_sphere
  have he : (Subtype.val : Sphere 7 → V 8) ∘ southFiberPoint =
      southAxis.toContinuousLinearMap ∘ (Subtype.val : Sphere 3 → V 4) := rfl
  have hd := congrArg (sphereAmbientDerivative q) he
  unfold sphereAmbientDerivative at hd
  rw [mfderiv_comp q (htarget.mdifferentiableAt (by simp))
      (contMDiff_southFiberPoint.mdifferentiableAt (by simp)),
    mfderiv_comp q southAxis.toContinuousLinearMap.differentiableAt.mdifferentiableAt
      (hsource.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hd
  intro v w hvw
  apply injective_mvfderiv_subtypeVal_sphere (n := 3) q
  apply southAxis.injective
  have hv := congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L v) hd
  have hw := congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L w) hd
  exact hv.symm.trans ((congrArg
    (mfderiv (𝓡 7) 𝓘(ℝ, V 8) (Subtype.val : Sphere 7 → V 8) (southFiberPoint q)) hvw).trans hw)

theorem sphereMap_southFiber_range (x : Sphere 7) :
    sphereMap x = south ↔ ∃ q : Sphere 3, southFiberPoint q = x := by
  constructor
  · intro hx
    exact ⟨southFiberInverse ⟨x, hx⟩, southFiberPoint_southFiberInverse ⟨x, hx⟩⟩
  · rintro ⟨q, rfl⟩
    exact sphereMap_southFiberPoint q

def southFiberDiffeomorph :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    Sphere 3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ {x : Sphere 7 // sphereMap x = south} :=
  diffeomorphToRegularFiber sphereMap contMDiff_sphereMap south south_regular 3
    (by simp only [finrank_euclideanSpace_fin]) southFiberPoint contMDiff_southFiberPoint
    southFiberPoint_injective southFiberPoint_mfderiv_injective sphereMap_southFiber_range

theorem southFiberDiffeomorph_val (q : Sphere 3) :
    letI := regularFiberAtlas sphereMap contMDiff_sphereMap south south_regular 3
      (by simp only [finrank_euclideanSpace_fin]);
    (southFiberDiffeomorph q).val = southFiberPoint q := rfl

end NoExoticSixSphere.QuaternionicHopf
