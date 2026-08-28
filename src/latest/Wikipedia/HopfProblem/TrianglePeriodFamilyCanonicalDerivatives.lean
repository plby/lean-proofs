import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalLinear
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual derivatives of period-family coordinate maps

A period-family coordinate change has the form
`(z, ζ) ↦ (f z, R z *ᵥ ζ + d z)`.  We differentiate this function itself,
entry by entry, before applying the block-determinant calculation.  Thus the
canonical-volume transformation below is a consequence of the genuine
Fréchet derivative, not a separately specified Jacobian.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

/-- The actual skew-product function appearing in period-family coordinates. -/
def skewMap (f : ℂ → ℂ) (R : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (d : ℂ → ComplexPlane₂) (x : Model) : Model :=
  (f x.1, R x.1 *ᵥ x.2 + d x.1)

@[simp] theorem skewMap_apply (f : ℂ → ℂ)
    (R : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (d : ℂ → ComplexPlane₂)
    (z : ℂ) (ζ : ComplexPlane₂) :
    skewMap f R d (z, ζ) = (f z, R z *ᵥ ζ + d z) := rfl

/-- Differentiating a matrix-valued function applied to the moving fibre point. -/
theorem mulVec_hasFDerivAt
    {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ}
    {z : ℂ} (ζ : ComplexPlane₂)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z) :
    HasFDerivAt (fun x : Model => R x.1 *ᵥ x.2)
      ((ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).smulRight (R' *ᵥ ζ) +
        (Matrix.toLin' (R z)).toContinuousLinearMap.comp
          (ContinuousLinearMap.snd ℂ ℂ ComplexPlane₂)) (z, ζ) := by
  apply hasFDerivAt_pi''
  intro i
  have hentry (j : Fin 2) :=
    ((hR i j).comp_hasFDerivAt (z, ζ)
      (hasFDerivAt_fst (𝕜 := ℂ))).mul
        ((hasFDerivAt_apply (𝕜 := ℂ) j ζ).comp (z, ζ)
          (hasFDerivAt_snd (𝕜 := ℂ)))
  have hs := HasFDerivAt.sum (u := Finset.univ) (fun j _ => hentry j)
  convert! hs using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- A base-dependent vector translation has the expected base-direction derivative. -/
theorem baseVector_hasFDerivAt {d : ℂ → ComplexPlane₂} {d' : ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hd : HasDerivAt d d' z) :
    HasFDerivAt (fun x : Model => d x.1)
      ((ContinuousLinearMap.fst ℂ ℂ ComplexPlane₂).smulRight d') (z, ζ) := by
  exact (hd.hasFDerivAt.comp (z, ζ) (hasFDerivAt_fst (𝕜 := ℂ))).congr_fderiv
    (by apply ContinuousLinearMap.ext; intro v; rfl)

/-- The genuine Fréchet derivative of the skew-product coordinate map. -/
theorem skewMap_hasFDerivAt
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {f' z : ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ} {d' : ComplexPlane₂}
    (ζ : ComplexPlane₂) (hf : HasDerivAt f f' z)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z)
    (hd : HasDerivAt d d' z) :
    HasFDerivAt (skewMap f R d)
      (blockDerivative f' (R' *ᵥ ζ + d') (R z)) (z, ζ) := by
  have hf₁ := hf.comp_hasFDerivAt (z, ζ) (hasFDerivAt_fst (𝕜 := ℂ))
  have hζ := (mulVec_hasFDerivAt ζ hR).add (baseVector_hasFDerivAt ζ hd)
  exact (hf₁.prodMk hζ).congr_fderiv (by
    apply ContinuousLinearMap.ext
    intro v
    apply Prod.ext
    · rfl
    · change (v.1 • (R' *ᵥ ζ) + R z *ᵥ v.2) + v.1 • d' =
        v.1 • (R' *ᵥ ζ + d') + R z *ᵥ v.2
      rw [smul_add]
      abel)

/-- The derivative supplied above agrees with Mathlib's actual `fderiv`. -/
theorem fderiv_skewMap
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {f' z : ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ} {d' : ComplexPlane₂}
    (ζ : ComplexPlane₂) (hf : HasDerivAt f f' z)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z)
    (hd : HasDerivAt d d' z) :
    fderiv ℂ (skewMap f R d) (z, ζ) =
      blockDerivative f' (R' *ᵥ ζ + d') (R z) :=
  (skewMap_hasFDerivAt ζ hf hR hd).fderiv

/-- The determinant of the genuine derivative is independent of the translation. -/
theorem det_fderiv_skewMap
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {f' z : ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ} {d' : ComplexPlane₂}
    (ζ : ComplexPlane₂) (hf : HasDerivAt f f' z)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z)
    (hd : HasDerivAt d d' z) :
    LinearMap.det (fderiv ℂ (skewMap f R d) (z, ζ)).toLinearMap =
      f' * (R z).det := by
  rw [fderiv_skewMap ζ hf hR hd, det_blockDerivative]

/-- Pullback of the standard volume by the actual coordinate-map derivative. -/
theorem volume_pullback_skewMap
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {f' z : ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ} {d' : ComplexPlane₂}
    (ζ : ComplexPlane₂) (hf : HasDerivAt f f' z)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z)
    (hd : HasDerivAt d d' z) :
    volume.compContinuousLinearMap (fderiv ℂ (skewMap f R d) (z, ζ)) =
      (f' * (R z).det) • volume := by
  rw [volume_pullback, det_fderiv_skewMap ζ hf hR hd]

/-- Every genuine continuous top covector has the same Jacobian multiplier. -/
theorem pullback_skewMap (α : TopCovector)
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {f' z : ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ} {d' : ComplexPlane₂}
    (ζ : ComplexPlane₂) (hf : HasDerivAt f f' z)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z)
    (hd : HasDerivAt d d' z) :
    α.compContinuousLinearMap (fderiv ℂ (skewMap f R d) (z, ζ)) =
      (f' * (R z).det) • α := by
  rw [pullback_eq_det_smul, det_fderiv_skewMap ζ hf hR hd]

/-- Coefficients of actual pulled-back top covectors in the standard frame. -/
theorem coefficient_pullback_skewMap (α : TopCovector)
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {f' z : ℂ} {R' : Matrix (Fin 2) (Fin 2) ℂ} {d' : ComplexPlane₂}
    (ζ : ComplexPlane₂) (hf : HasDerivAt f f' z)
    (hR : ∀ i j, HasDerivAt (fun w => R w i j) (R' i j) z)
    (hd : HasDerivAt d d' z) :
    coefficient (α.compContinuousLinearMap (fderiv ℂ (skewMap f R d) (z, ζ))) =
      (f' * (R z).det) * coefficient α := by
  rw [coefficient_pullback, det_fderiv_skewMap ζ hf hR hd]

/-- The derivative formula with no separately supplied derivative data. -/
theorem fderiv_skewMap_of_differentiable
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hf : DifferentiableAt ℂ f z)
    (hR : ∀ i j, DifferentiableAt ℂ (fun w => R w i j) z)
    (hd : DifferentiableAt ℂ d z) :
    fderiv ℂ (skewMap f R d) (z, ζ) =
      blockDerivative (deriv f z)
        ((fun i j => deriv (fun w => R w i j) z) *ᵥ ζ + deriv d z) (R z) :=
  fderiv_skewMap ζ hf.hasDerivAt (fun i j => (hR i j).hasDerivAt) hd.hasDerivAt

theorem det_fderiv_skewMap_of_differentiable
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hf : DifferentiableAt ℂ f z)
    (hR : ∀ i j, DifferentiableAt ℂ (fun w => R w i j) z)
    (hd : DifferentiableAt ℂ d z) :
    LinearMap.det (fderiv ℂ (skewMap f R d) (z, ζ)).toLinearMap =
      deriv f z * (R z).det :=
  det_fderiv_skewMap ζ hf.hasDerivAt (fun i j => (hR i j).hasDerivAt) hd.hasDerivAt

theorem volume_pullback_skewMap_of_differentiable
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hf : DifferentiableAt ℂ f z)
    (hR : ∀ i j, DifferentiableAt ℂ (fun w => R w i j) z)
    (hd : DifferentiableAt ℂ d z) :
    volume.compContinuousLinearMap (fderiv ℂ (skewMap f R d) (z, ζ)) =
      (deriv f z * (R z).det) • volume :=
  volume_pullback_skewMap ζ hf.hasDerivAt (fun i j => (hR i j).hasDerivAt) hd.hasDerivAt

theorem pullback_skewMap_of_differentiable (α : TopCovector)
    {f : ℂ → ℂ} {R : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {d : ℂ → ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hf : DifferentiableAt ℂ f z)
    (hR : ∀ i j, DifferentiableAt ℂ (fun w => R w i j) z)
    (hd : DifferentiableAt ℂ d z) :
    α.compContinuousLinearMap (fderiv ℂ (skewMap f R d) (z, ζ)) =
      (deriv f z * (R z).det) • α :=
  pullback_skewMap α ζ hf.hasDerivAt (fun i j => (hR i j).hasDerivAt) hd.hasDerivAt

/-- A lattice translation depending on the base, as an actual product-map function. -/
def shearMap (d : ℂ → ComplexPlane₂) (x : Model) : Model :=
  (x.1, x.2 + d x.1)

@[simp] theorem shearMap_apply (d : ℂ → ComplexPlane₂) (z : ℂ) (ζ : ComplexPlane₂) :
    shearMap d (z, ζ) = (z, ζ + d z) := rfl

theorem shearMap_eq_skewMap (d : ℂ → ComplexPlane₂) :
    shearMap d = skewMap id (fun _ => 1) d := by
  funext x
  simp [shearMap, skewMap]

/-- The derivative of the actual lattice shear, without any invertibility assumption. -/
theorem shearMap_hasFDerivAt {d : ℂ → ComplexPlane₂} {d' : ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hd : HasDerivAt d d' z) :
    HasFDerivAt (shearMap d) (shearDerivative d') (z, ζ) := by
  rw [shearMap_eq_skewMap]
  simpa [shearDerivative] using
    (skewMap_hasFDerivAt (f := id) (R := fun _ => 1)
      (R' := 0) ζ (hasDerivAt_id z)
      (fun i j => hasDerivAt_const z ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)) hd)

theorem fderiv_shearMap {d : ℂ → ComplexPlane₂} {d' : ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hd : HasDerivAt d d' z) :
    fderiv ℂ (shearMap d) (z, ζ) = shearDerivative d' :=
  (shearMap_hasFDerivAt ζ hd).fderiv

theorem det_fderiv_shearMap {d : ℂ → ComplexPlane₂} {d' : ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hd : HasDerivAt d d' z) :
    LinearMap.det (fderiv ℂ (shearMap d) (z, ζ)).toLinearMap = 1 := by
  rw [fderiv_shearMap ζ hd, det_shearDerivative]

theorem volume_pullback_shearMap {d : ℂ → ComplexPlane₂} {d' : ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hd : HasDerivAt d d' z) :
    volume.compContinuousLinearMap (fderiv ℂ (shearMap d) (z, ζ)) = volume := by
  rw [fderiv_shearMap ζ hd, volume_pullback_shearDerivative]

theorem pullback_shearMap (α : TopCovector) {d : ℂ → ComplexPlane₂}
    {d' : ComplexPlane₂} {z : ℂ} (ζ : ComplexPlane₂) (hd : HasDerivAt d d' z) :
    α.compContinuousLinearMap (fderiv ℂ (shearMap d) (z, ζ)) = α := by
  rw [fderiv_shearMap ζ hd, pullback_shearDerivative]

theorem volume_pullback_shearMap_of_differentiable {d : ℂ → ComplexPlane₂}
    {z : ℂ} (ζ : ComplexPlane₂) (hd : DifferentiableAt ℂ d z) :
    volume.compContinuousLinearMap (fderiv ℂ (shearMap d) (z, ζ)) = volume :=
  volume_pullback_shearMap ζ hd.hasDerivAt

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
