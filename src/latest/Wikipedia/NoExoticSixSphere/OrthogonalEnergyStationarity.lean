import Wikipedia.NoExoticSixSphere.OrthogonalBodyVelocityCurve

/-!
# Stationary energy forces vanishing body acceleration

Stationarity quantifies over actual smooth two-parameter orthogonal families
with fixed endpoints. A weighted body-acceleration field gives such a family.
Its first energy derivative is a negative weighted squared norm, so stationarity
forces the body acceleration to vanish throughout the interior of the interval.
-/

open scoped ContDiff

namespace NoExoticSixSphere.OrthogonalEnergyStationarity

open GLOrthonormalization CayleyTransform HilbertSchmidt OrthogonalPathEnergy
  OrthogonalBodyVelocityCurve OrthogonalExponentialVariation OrthogonalFirstVariation

variable {n : ℕ}

/-- Stationarity under all actual smooth variations fixing the two endpoint slices. -/
def IsStationary (γ : ℝ → OrthogonalOperators n) (l u : ℝ) : Prop :=
  ∀ a : ℝ × ℝ → OrthogonalOperators n,
    ContDiff ℝ ∞ (OrthogonalMaurerCartan.operator a) →
    (∀ t, a (0, t) = γ t) → (∀ s, a (s, l) = γ l) → (∀ s, a (s, u) = γ u) →
    HasDerivAt (fun s ↦ energy (fun t ↦ (a (s, t)).1.1) l u) 0 0

variable {γ : ℝ → OrthogonalOperators n}
  (hγ : ContDiff ℝ ∞ (fun t ↦ (γ t).1.1))

theorem hasDerivAt_energy_family {W : ℝ → SkewOperators n} (hW : ContDiff ℝ ∞ W)
    (l u : ℝ) (hl : W l = 0) (hu : W u = 0) :
    HasDerivAt (fun s ↦ energy (fun t ↦ (family γ W (s, t)).1.1) l u)
      (-2 * ∫ t in l..u, innerForm
        ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n)
        (W t : Vector n →L[ℝ] Vector n)) 0 := by
  have hd := hasDerivAt_energy_fixedEndpoints (contDiff_family_operator hγ hW) 0 l u
    (fun s ↦ (family_of_field_zero γ W hl s).trans (family_zero γ W l).symm)
    (fun s ↦ (family_of_field_zero γ W hu s).trans (family_zero γ W u).symm)
  simpa only [second_velocity_family_zero hγ hW, variation_zero hγ hW] using hd

noncomputable def weightedAcceleration (l u t : ℝ) : SkewOperators n :=
  ((t - l) * (u - t)) • deriv (body hγ) t

theorem contDiff_weightedAcceleration (l u : ℝ) :
    ContDiff ℝ ∞ (weightedAcceleration hγ l u) :=
  ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)).smul
    (contDiff_body hγ).deriv'

theorem weightedAcceleration_left (l u : ℝ) : weightedAcceleration hγ l u l = 0 := by
  simp only [weightedAcceleration, sub_self, zero_mul, zero_smul]

theorem weightedAcceleration_right (l u : ℝ) : weightedAcceleration hγ l u u = 0 := by
  simp only [weightedAcceleration, sub_self, mul_zero, zero_smul]

theorem weightedAcceleration_integral_eq_zero {l u : ℝ} (hcrit : IsStationary γ l u) :
    (∫ t in l..u, ((t - l) * (u - t)) * squareNorm
      ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n)) = 0 := by
  let W := weightedAcceleration hγ l u
  have hW : ContDiff ℝ ∞ W := contDiff_weightedAcceleration hγ l u
  have hl : W l = 0 := weightedAcceleration_left hγ l u
  have hu : W u = 0 := weightedAcceleration_right hγ l u
  have hd := hasDerivAt_energy_family hγ hW l u hl hu
  have hzero := hcrit (family γ W) (contDiff_family_operator hγ hW)
    (family_zero γ W) (family_of_field_zero γ W hl) (family_of_field_zero γ W hu)
  have heq := hd.unique hzero
  change -2 * (∫ t in l..u, innerForm
    ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n)
    (((t - l) * (u - t)) •
      ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n))) = 0 at heq
  simp only [innerForm_smul_right] at heq
  change (∫ t in l..u, ((t - l) * (u - t)) * innerForm
    ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n)
    ((deriv (body hγ) t : SkewOperators n) : Vector n →L[ℝ] Vector n)) = 0
  linarith

/-- The Euler--Lagrange condition follows from actual fixed-endpoint stationarity. -/
theorem body_derivative_eq_zero_of_stationary {l u : ℝ} (hcrit : IsStationary γ l u)
    {t : ℝ} (ht : t ∈ Set.Ioo l u) : deriv (body hγ) t = 0 := by
  let B : ℝ → Vector n →L[ℝ] Vector n :=
    fun r ↦ ((deriv (body hγ) r : SkewOperators n) : Vector n →L[ℝ] Vector n)
  have hB : Continuous B :=
    (skewAdjoint.submodule ℝ (Vector n →L[ℝ] Vector n)).subtypeL.continuous.comp
      (ContDiff.deriv' (n := ∞) (contDiff_body hγ)).continuous
  have hsq : Continuous (fun r ↦ squareNorm (B r)) :=
    Continuous.comp (g := squareNorm (n := n)) (f := B)
      (contDiff_squareNorm (n := n)).continuous hB
  have hc : Continuous (fun r ↦ ((r - l) * (u - r)) * squareNorm (B r)) :=
    ((continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)).mul hsq
  by_contra hne
  have hBn : B t ≠ 0 := by
    intro hz
    apply hne
    exact Subtype.ext hz
  have hspos : 0 < squareNorm (B t) := lt_of_le_of_ne (squareNorm_nonneg _)
    (Ne.symm (fun hz ↦ hBn ((squareNorm_eq_zero_iff _).mp hz)))
  have hp := intervalIntegral.integral_pos (ht.1.trans ht.2) hc.continuousOn
    (fun r hr ↦ mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hr.1.le) (sub_nonneg.mpr hr.2)) (squareNorm_nonneg _))
    ⟨t, ⟨ht.1.le, ht.2.le⟩,
      mul_pos (mul_pos (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)) hspos⟩
  have hz := weightedAcceleration_integral_eq_zero hγ hcrit
  change (∫ r in l..u, ((r - l) * (u - r)) * squareNorm (B r)) = 0 at hz
  linarith

theorem body_eq_of_stationary {l u : ℝ} (hlu : l < u) (hcrit : IsStationary γ l u)
    {t : ℝ} (ht : t ∈ Set.Icc l u) : body hγ t = body hγ l := by
  apply OrthogonalConstantVelocity.eq_of_hasDerivAt_zero_Ioo hlu
    (contDiff_body hγ).continuous _ ht ⟨le_rfl, hlu.le⟩
  intro r hr
  exact (((contDiff_body hγ).differentiable (by simp)) r).hasDerivAt.congr_deriv
    (body_derivative_eq_zero_of_stationary hγ hcrit hr)

include hγ in
/-- Every actual smooth stationary path is exponential throughout the given interval. -/
theorem stationary_is_exponential {l u : ℝ} (hlu : l < u) (hcrit : IsStationary γ l u) :
    ∃ K : SkewOperators n, ∀ t ∈ Set.Icc l u,
      γ t = γ l * OrthogonalExponential.exp ((t - l) • K) := by
  refine ⟨body hγ l, fun t ht ↦ ?_⟩
  apply OrthogonalConstantVelocity.eq_mul_exp_on_Icc γ (body hγ l) hlu hγ.continuous _ ht
  intro r hr
  apply ((hγ.differentiable (by simp)) r).hasDerivAt.congr_deriv
  have hb := body_eq_of_stationary hγ hlu hcrit ⟨hr.1.le, hr.2.le⟩
  rw [← hb, body_coe]
  apply ContinuousLinearMap.ext
  intro x
  exact (OrthogonalPaths.self_apply_inverse (γ r) _).symm

end NoExoticSixSphere.OrthogonalEnergyStationarity
