import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundarySigns
import Wikipedia.SmoothSixDPoincare.SphereChartOrientation

/-!
# Local boundary signs compared with the fixed outward sphere convention

Use the actual derivative of a sphere parametrization and one fixed normal
frame. The chain rule and the radial-frame determinant factorization identify
the local derivative sign, corrected by the chart's outward sign, with the
original normal Jacobian sign. This is a local formula; it does not assert
the still-needed global sum of local contributions.
-/

noncomputable section

open Set Metric ContinuousMap Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates

variable {V F : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {m : ℕ} [Fact (Module.finrank ℝ V = m + 1)]

def chartJacobian
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m)
      (EuclideanSpace ℝ (Fin m)) (sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F)
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  ((chartRadialFrame c z).comp j'.symm.toContinuousLinearMap).det

theorem chartJacobian_ne_zero
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m)
      (EuclideanSpace ℝ (Fin m)) (sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source) : chartJacobian c j B z ≠ 0 :=
  (RegularValues.bijective_iff_det_ne_zero _).mp
    ((bijective_chartRadialFrame c hz).comp
      ((ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j).symm.bijective)

omit [FiniteDimensional ℝ V] in
/-- The actual coordinate derivative, not an independent linear model, gives this factorization. -/
theorem chartJacobian_factor
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m)
      (EuclideanSpace ℝ (Fin m)) (sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source)
    (f : sphere (0 : V) 1 → F) (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)) *
      (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det = chartJacobian c j B z := by
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] F := mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)
  let C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m) c z
  let j' := (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) B).trans j
  have hd : fderiv ℝ (f ∘ c) z = A.comp C := by
    have h := mfderiv_comp z hf (c.mdifferentiableAt (by simp) hz)
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hB : (B.symm.toContinuousLinearMap.comp A).IsInvertible :=
    (show B.symm.toContinuousLinearMap.IsInvertible from ⟨B.symm, rfl⟩).comp hA
  have h := normalJacobian_mul_chartDet j' (c z) (B.symm.toContinuousLinearMap.comp A) hB C
  rw [normalJacobian_change_normal_model j B (c z) A hA] at h
  change normalJacobian j (c z) A * _ = _
  rw [hd]
  rw [← ContinuousLinearMap.comp_assoc]
  apply h.trans
  unfold chartJacobian
  rw [chartRadialFrame_eq c hz]

private theorem sign_factor {a b c : ℝ} (hb : b ≠ 0) (h : a * b = c) :
    SignType.sign c * SignType.sign b = SignType.sign a := by
  have hsq : SignType.sign b * SignType.sign b = 1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hb)
  rw [← h, sign_mul, mul_assoc, hsq, mul_one]

/-- Outward-chart sign times the coordinate derivative sign equals the fixed normal sign. -/
theorem chartJacobian_sign_factor
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) (𝓡 m)
      (EuclideanSpace ℝ (Fin m)) (sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin m) ≃L[ℝ] F)
    {z : EuclideanSpace ℝ (Fin m)} (hz : z ∈ c.source)
    (f : sphere (0 : V) 1 → F) (hf : MDifferentiableAt (𝓡 m) 𝓘(ℝ, F) f (c z))
    (hA : (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z)).IsInvertible) :
    SignType.sign (chartJacobian c j B z) *
      SignType.sign (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) z)).det =
        SignType.sign (normalJacobian j (c z) (mfderiv (𝓡 m) 𝓘(ℝ, F) f (c z))) := by
  have h := chartJacobian_factor c j B hz f hf hA
  apply sign_factor _ h
  intro hd
  rw [hd, mul_zero] at h
  exact chartJacobian_ne_zero c j B hz h.symm

end Wikipedia.SmoothSixDPoincare.SphereNormalCoordinates
