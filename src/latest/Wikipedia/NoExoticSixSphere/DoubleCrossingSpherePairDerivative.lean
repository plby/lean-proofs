import Wikipedia.NoExoticSixSphere.DoubleCrossingSpherePairMap

/-!
# Native derivatives of both embedded reference spheres

The derivatives are the specified injective ambient linear maps restricted
to the actual native sphere derivative. The original atlas is retained.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.DoubleCrossingSpherePair

open GLOrthonormalization SphereThreeTangentFrame

theorem hasFDerivAt_leftAmbient (x : Vector 4) : HasFDerivAt leftAmbient leftLinear x :=
  leftLinear.hasFDerivAt.add_const (0, axis)

theorem hasFDerivAt_rightAmbient (x : Vector 4) : HasFDerivAt rightAmbient rightLinear x :=
  rightLinear.hasFDerivAt.add_const (axis, 0)

theorem mfderiv_left (x : Sphere 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) left x =
      leftLinear.comp (inclusionDerivative x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  change mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3)
    (leftAmbient ∘ (fun s : Sphere 3 ↦ s.val)) x = _
  rw [mfderiv_comp x (contDiff_leftAmbient.contMDiff.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, (hasFDerivAt_leftAmbient x.val).fderiv]
  rfl

theorem mfderiv_right (x : Sphere 3) :
    mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) right x =
      rightLinear.comp (inclusionDerivative x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  change mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3)
    (rightAmbient ∘ (fun s : Sphere 3 ↦ s.val)) x = _
  rw [mfderiv_comp x (contDiff_rightAmbient.contMDiff.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, (hasFDerivAt_rightAmbient x.val).fderiv]
  rfl

theorem injective_mfderiv_left (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) left x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative x) := by
    convert! injective_mvfderiv_subtypeVal_sphere x
  rw [mfderiv_left]
  exact injective_leftLinear.comp hi

theorem injective_mfderiv_right (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) right x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative x) := by
    convert! injective_mvfderiv_subtypeVal_sphere x
  rw [mfderiv_right]
  exact injective_rightLinear.comp hi

def leftDerivative (x : Sphere 3) : Vector 3 →L[ℝ] (Vector 3 × Vector 3) :=
  mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) left x

def rightDerivative (x : Sphere 3) : Vector 3 →L[ℝ] (Vector 3 × Vector 3) :=
  mfderiv (𝓡 3) 𝓘(ℝ, Vector 3 × Vector 3) right x

theorem leftDerivative_apply (x : Sphere 3) (v : Vector 3) :
    leftDerivative x v = leftLinear (inclusionDerivative x v) :=
  congrArg (fun A : Vector 3 →L[ℝ] (Vector 3 × Vector 3) ↦ A v) (mfderiv_left x)

theorem rightDerivative_apply (x : Sphere 3) (v : Vector 3) :
    rightDerivative x v = rightLinear (inclusionDerivative x v) :=
  congrArg (fun A : Vector 3 →L[ℝ] (Vector 3 × Vector 3) ↦ A v) (mfderiv_right x)

end NoExoticSixSphere.DoubleCrossingSpherePair
