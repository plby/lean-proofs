import Wikipedia.NoExoticSixSphere.OrthogonalSecondVariation

/-!
# Realizing skew-adjoint fields by actual fixed-endpoint variations

The family `γ(t) * exp(s W(t))` is smooth in both parameters. Its actual
left-trivialized parameter derivative at zero is exactly `W(t)`. If the field
vanishes at the two endpoints, the entire variation fixes those endpoints.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalExponentialVariation

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalExponential
  OrthogonalMaurerCartan OrthogonalFirstVariation TwoParameterCalculus

variable {n : ℕ}

noncomputable def family (γ : ℝ → OrthogonalOperators n) (W : ℝ → SkewOperators n)
    (p : ℝ × ℝ) : OrthogonalOperators n := γ p.2 * exp (p.1 • W p.2)

theorem family_zero (γ : ℝ → OrthogonalOperators n) (W : ℝ → SkewOperators n) (t : ℝ) :
    family γ W (0, t) = γ t := by
  simp only [family, zero_smul, exp_zero, mul_one]

theorem family_of_field_zero (γ : ℝ → OrthogonalOperators n) (W : ℝ → SkewOperators n)
    {t : ℝ} (ht : W t = 0) (s : ℝ) : family γ W (s, t) = γ t := by
  simp only [family, ht, smul_zero, exp_zero, mul_one]

variable {γ : ℝ → OrthogonalOperators n} {W : ℝ → SkewOperators n}
  (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1)) (hW : ContDiff ℝ ∞ W)

include hγ hW

theorem contDiff_family_operator :
    ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator (family γ W)) := by
  have harg : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 • W p.2) :=
    contDiff_fst.smul (hW.comp contDiff_snd)
  have he : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ (exp (p.1 • W p.2)).1.1) :=
    ContDiff.comp (g := fun K : SkewOperators n ↦ (exp K).1.1)
      (f := fun p : ℝ × ℝ ↦ p.1 • W p.2) contDiff_exp_operator harg
  exact (hγ.comp contDiff_snd).clm_comp he

theorem variation_zero (t : ℝ) :
    variation (family γ W) (0, t) = (W t : Vector n →L[ℝ] Vector n) := by
  have hA := contDiff_family_operator hγ hW
  have hd := hasDerivAt_first ((hA.differentiable (by simp)) (0, t))
  have he := OrthogonalPathEnergy.hasDerivAt_left_exp (γ t) (W t) 0
  have hfirst := hd.unique he
  unfold variation
  rw [hfirst, family_zero]
  apply ContinuousLinearMap.ext
  intro x
  change (inverse (γ t)).1.1
    ((γ t).1.1 ((exp (0 • W t)).1.1 ((W t : Vector n →L[ℝ] Vector n) x))) = _
  rw [zero_smul, exp_zero, inverse_apply_self]
  rfl

theorem second_variation_zero (t : ℝ) :
    second (variation (family γ W)) (0, t) =
      ((deriv W t : SkewOperators n) : Vector n →L[ℝ] Vector n) := by
  have hd := hasDerivAt_second
    (((contDiff_variation (contDiff_family_operator hγ hW)).differentiable (by simp)) (0, t))
  have heq : (fun r ↦ variation (family γ W) (0, r)) =
      (fun r ↦ (W r : Vector n →L[ℝ] Vector n)) := funext (variation_zero hγ hW)
  rw [heq] at hd
  let L : SkewOperators n →L[ℝ] (Vector n →L[ℝ] Vector n) :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL
  exact hd.unique (L.hasFDerivAt.comp_hasDerivAt t
    (((hW.differentiable (by simp)) t).hasDerivAt))

/-- The index form is realized by the actual energy of the constructed variation. -/
theorem hasDerivAt_deriv_energy_family (l u : ℝ) (hl : W l = 0) (hu : W u = 0)
    (b : OrthogonalOperators n) (K : SkewOperators n)
    (hpath : ∀ t, γ t = b * exp (t • K)) :
    HasDerivAt (deriv (fun s ↦ OrthogonalPathEnergy.energy
      (fun t ↦ (family γ W (s, t)).1.1) l u))
      (2 * ∫ t in l..u, OrthogonalIndexForm.density K
        (W t : Vector n →L[ℝ] Vector n)
        ((deriv W t : SkewOperators n) : Vector n →L[ℝ] Vector n)) 0 := by
  have hd := hasDerivAt_deriv_energy_of_exponential (contDiff_family_operator hγ hW)
    l u
    (fun s ↦ (family_of_field_zero γ W hl s).trans (family_zero γ W l).symm)
    (fun s ↦ (family_of_field_zero γ W hu s).trans (family_zero γ W u).symm)
    0 b K (fun t ↦ (family_zero γ W t).trans (hpath t))
  simpa only [variation_zero hγ hW, second_variation_zero hγ hW] using hd

end NoExoticSixSphere.OrthogonalExponentialVariation
