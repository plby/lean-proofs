import Wikipedia.HopfProblem.OrbitPairSphereNegativeDirections

/-!
# The negative-index bound for every nonminimal antipodal great circle

The actual antipodal endpoint forces an odd multiple of π for the speed.
Energy above the minimum therefore forces absolute speed at least `3π`.
The two-mode construction then supplies twice the normal-plane dimension
in independent negative directions, realized by smooth sphere-valued paths
with those same endpoints.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.OrbitPair.SphereAntipodalIndex

open NoExoticSixSphere GLOrthonormalization SphereGreatCircle SphereNegativeDirections

variable {n : ℕ}

theorem cos_eq_neg_one_of_antipodal {x y : Vector n} (hx : ‖x‖ = 1)
    (hxy : inner ℝ x y = 0) {w : ℝ} (hend : curve x y w 1 = -x) :
    Real.cos w = -1 := by
  have h := congrArg (fun z => inner ℝ x z) hend
  simpa only [curve, mul_one, inner_add_right, real_inner_smul_right,
    inner_neg_right, real_inner_self_eq_norm_sq, hx, one_pow, hxy, mul_one,
    mul_zero, add_zero] using h

theorem odd_speed_of_antipodal {x y : Vector n} (hx : ‖x‖ = 1)
    (hxy : inner ℝ x y = 0) {w : ℝ} (hend : curve x y w 1 = -x) :
    ∃ k : ℤ, w = (2 * (k : ℝ) + 1) * Real.pi := by
  have hcos := cos_eq_neg_one_of_antipodal hx hxy hend
  have hc : Real.cos (w - Real.pi) = 1 := by
    rw [Real.cos_sub, hcos, Real.cos_pi, Real.sin_pi]
    ring
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (w - Real.pi)).mp hc
  refine ⟨k, ?_⟩
  linarith

theorem speed_ge_three_pi_of_nonminimal {x y : Vector n}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    {w : ℝ} (hend : curve x y w 1 = -x)
    (habove : Real.pi ^ 2 < SpherePathEnergy.energy (curve x y w) 0 1) :
    3 * Real.pi ≤ |w| := by
  rw [energy_curve hx hy hxy] at habove
  obtain ⟨k, hk⟩ := odd_speed_of_antipodal hx hxy hend
  have hk₀ : k ≠ 0 := by
    intro h
    rw [h] at hk
    norm_num at hk
    exact habove.ne' (congrArg (fun z : ℝ => z ^ 2) hk)
  have hk₁ : k ≠ -1 := by
    intro h
    rw [h] at hk
    norm_num at hk
    rw [hk, neg_sq] at habove
    exact (lt_irrefl _) habove
  have hor : 1 ≤ k ∨ k ≤ -2 := by omega
  rcases hor with h | h
  · have hr : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    have hw : 3 * Real.pi ≤ w := by nlinarith [Real.pi_pos]
    exact hw.trans (le_abs_self w)
  · have hr : (k : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h
    have hw : 3 * Real.pi ≤ -w := by nlinarith [Real.pi_pos]
    exact hw.trans (neg_le_abs w)

theorem exists_negative_family {x y : Vector n}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    {w : ℝ} (hend : curve x y w 1 = -x)
    (habove : Real.pi ^ 2 < SpherePathEnergy.energy (curve x y w) 0 1) :
    ∃ (d : ℕ) (F : (Fin d → ℝ) →ₗ[ℝ] (ℝ → Vector n)),
      d + 4 = 2 * n ∧ Function.Injective F ∧ ∀ c,
        ContDiff ℝ ∞ (F c) ∧ F c 0 = 0 ∧ F c 1 = 0 ∧
          (c ≠ 0 → deriv (deriv (fun s => SpherePathEnergy.energy
            (fun t => SphereNormalVariation.family (curve x y w) (F c) (s, t)) 0 1)) 0 < 0) :=
  exists_negative_fieldFamily hx hy hxy w
    (speed_ge_three_pi_of_nonminimal hx hy hxy hend habove)

theorem realized_family {x y : Vector n}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : inner ℝ x y = 0)
    {w : ℝ} (hend : curve x y w 1 = -x) (p : Parameters x y) :
    let A := SphereNormalVariation.family (curve x y w) (fieldLinear x y p)
    ContDiff ℝ ∞ A ∧ (∀ q, ‖A q‖ = 1) ∧
      (∀ s, A (s, 0) = x ∧ A (s, 1) = -x) ∧
      (∀ t, A (0, t) = curve x y w t) ∧
      (∀ t, NoExoticSixSphere.TwoParameterCalculus.first A (0, t) = fieldLinear x y p t) := by
  have hn := norm_curve hx hy hxy w
  have ho := field_orthogonal x y p w
  refine ⟨SphereNormalVariation.contDiff_family (contDiff_curve x y w)
    (SphereSineModes.contDiff_field _ _) hn ho,
    SphereNormalVariation.norm_family hn ho, ?_, SphereNormalVariation.family_zero hn,
    SphereNormalVariation.first_family_zero (contDiff_curve x y w)
      (SphereSineModes.contDiff_field _ _) hn ho⟩
  intro s
  constructor
  · exact (SphereNormalVariation.family_of_field_zero hn
      (show fieldLinear x y p 0 = 0 from SphereSineModes.field_zero _ _) s).trans
      (curve_zero x y w)
  · exact (SphereNormalVariation.family_of_field_zero hn
      (show fieldLinear x y p 1 = 0 from SphereSineModes.field_one _ _) s).trans hend

end Wikipedia.HopfProblem.OrbitPair.SphereAntipodalIndex
