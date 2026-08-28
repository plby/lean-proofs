import Wikipedia.HopfProblem.SpecialPeriodsModularUnreduced
import Wikipedia.HopfProblem.SpecialPeriodsModularPullbackRotations
import Wikipedia.HopfProblem.SpecialPeriodsTriangleActions
import Mathlib.Topology.Order.IntermediateValue

/-!
# Uniqueness of the normalized global modular lift

Equal modular values give one fixed modular transformation between two
holomorphic upper-half-plane lifts: local injectivity at one regular
value and the analytic identity theorem make the pointwise orbit
comparison global.  Normalization at two distinct upper-half-plane values
then forces this transformation to act identically.

This proves uniqueness, not existence of the global special periods or
of the triangle quotient coordinate.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularGroup Matrix
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem modularSL_holomorphic (g : SL(2, ℤ)) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℍ => g • z) :=
  UpperHalfPlane.contMDiff_smul (g := SpecialLinearGroup.mapGL ℝ g) (by simp)

theorem upperHalfPlane_holomorphic_eq_of_eventuallyEq {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    {a : ℍ} (he : f =ᶠ[𝓝 a] g) : f = g := by
  have hfc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (f z : ℂ)) :=
    (UpperHalfPlane.contMDiff_coe.comp hf).mdifferentiable (by simp)
  have hgc : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z => (g z : ℂ)) :=
    (UpperHalfPlane.contMDiff_coe.comp hg).mdifferentiable (by simp)
  have hz : ∀ᶠ z in 𝓝[≠] a, (f z : ℂ) - (g z : ℂ) = 0 :=
    (he.mono fun z hz => by rw [hz, sub_self]).filter_mono nhdsWithin_le_nhds
  have hzero := UpperHalfPlane.eq_zero_of_frequently (hfc.sub hgc) hz.frequently
  funext z
  apply UpperHalfPlane.ext
  exact sub_eq_zero.mp (congrFun hzero z)

/-- A real Möbius transformation fixing two distinct interior points is
the identity on the upper half-plane. -/
theorem realSL_action_identity_of_two_fixed (g : SL(2, ℝ)) {a b : ℍ}
    (ha : g • a = a) (hb : g • b = b) (hab : a ≠ b) : ∀ z : ℍ, g • z = z := by
  have hc : Triangle.cayleyCoordinate a b ≠ 0 := by
    apply div_ne_zero _ (Triangle.sub_conj_ne_zero a b)
    apply sub_ne_zero.mpr
    intro h
    exact hab (UpperHalfPlane.ext h).symm
  have hm : Triangle.slMultiplier g a = 1 := by
    have h := Triangle.cayleyCoordinate_smul g a b ha
    rw [hb] at h
    exact mul_right_cancel₀ hc (by simpa only [one_mul] using h.symm)
  intro z
  apply (Triangle.cayleyBiholomorph a).injective
  apply Subtype.ext
  change Triangle.cayleyCoordinate a (g • z) = Triangle.cayleyCoordinate a z
  rw [Triangle.cayleyCoordinate_smul g a z ha, hm, one_mul]

theorem integerSL_real_action (g : SL(2, ℤ)) (z : ℍ) :
    (SpecialLinearGroup.map (Int.castRingHom ℝ) g) • z = g • z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, coe_specialLinearGroup_apply]
  rfl

theorem modularSL_action_identity_of_two_fixed (g : SL(2, ℤ)) {a b : ℍ}
    (ha : g • a = a) (hb : g • b = b) (hab : a ≠ b) : ∀ z : ℍ, g • z = z := by
  have h := realSL_action_identity_of_two_fixed
    (SpecialLinearGroup.map (Int.castRingHom ℝ) g)
    (by simpa only [integerSL_real_action] using ha)
    (by simpa only [integerSL_real_action] using hb) hab
  simpa only [integerSL_real_action] using h

/-- Two holomorphic modular lifts differ by a single actual integral
Möbius transformation, provided their common value is regular somewhere. -/
theorem modularJ_equal_lifts_differ_by_SL {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hJ : ∀ z, modularJ (f z) = modularJ (g z))
    (a : ℍ) (ha : modularJ (f a) ∈ modularRegularValues) :
    ∃ γ : SL(2, ℤ), ∀ z, γ • f z = g z := by
  obtain ⟨γ, hγ⟩ := (modularJ_eq_iff_exists_smul (g a) (f a)).mp (hJ a).symm
  have hga : modularJ (g a) ∈ modularRegularValues := (hJ a) ▸ ha
  obtain ⟨U, hUo, hgaU, hUi⟩ := modularJ_regular_injOn_neighbourhood (g a)
    ((mem_modularRegularValues _).mp hga).1 ((mem_modularRegularValues _).mp hga).2
  have hγf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => γ • f z) :=
    (modularSL_holomorphic γ).comp hf
  have hnear₁ : ∀ᶠ z in 𝓝 a, γ • f z ∈ U := by
    apply hγf.continuous.continuousAt.preimage_mem_nhds
    simpa only [hγ] using hUo.mem_nhds hgaU
  have hnear₂ : ∀ᶠ z in 𝓝 a, g z ∈ U :=
    hg.continuous.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgaU)
  have he : (fun z => γ • f z) =ᶠ[𝓝 a] g := by
    filter_upwards [hnear₁, hnear₂] with z h₁ h₂
    exact hUi h₁ h₂ ((modularJ_SL_invariant γ (f z)).trans (hJ z))
  refine ⟨γ, ?_⟩
  exact congrFun (upperHalfPlane_holomorphic_eq_of_eventuallyEq hγf hg he)

/-- Two matching, distinct normalizing values remove the modular
ambiguity of a holomorphic lift. -/
theorem modular_lifts_eq_of_two_values {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hJ : ∀ z, modularJ (f z) = modularJ (g z))
    (x : ℍ) (hx : modularJ (f x) ∈ modularRegularValues)
    (a b : ℍ) (ha : f a = g a) (hb : f b = g b) (hab : f a ≠ f b) : f = g := by
  obtain ⟨γ, hγ⟩ := modularJ_equal_lifts_differ_by_SL hf hg hJ x hx
  have hid := modularSL_action_identity_of_two_fixed γ ((hγ a).trans ha.symm)
    ((hγ b).trans hb.symm) hab
  funext z
  exact (hid (f z)).symm.trans (hγ z)

theorem rhoPoint_ne_I : rhoPoint ≠ UpperHalfPlane.I := by
  intro h
  have he := congrArg (fun z : ℍ => (z : ℂ).re) h
  norm_num [rhoPoint] at he

/-- Continuity between the two elliptic values supplies a genuine
regular modular value, without a separate nonconstancy hypothesis. -/
theorem exists_regular_modular_value_of_centers {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {f : X → ℍ} (hf : Continuous f) (a b : X)
    (ha : f a = rhoPoint) (hb : f b = UpperHalfPlane.I) :
    ∃ x, modularJ (f x) ∈ modularRegularValues := by
  let F : X → ℝ := fun x => (modularJ (f x)).re
  have hF : Continuous F := Complex.continuous_re.comp (modularJ_continuous.comp hf)
  have hmid : (864 : ℝ) ∈ Icc (F a) (F b) := by
    norm_num [F, ha, hb]
  obtain ⟨x, hx⟩ := intermediate_value_univ a b hF hmid
  refine ⟨x, (mem_modularRegularValues _).mpr ⟨?_, ?_⟩⟩
  · intro hz
    have hh : F x = 0 := by simp [F, hz]
    linarith
  · intro hz
    have hh : F x = 1728 := by norm_num [F, hz]
    linarith

/-- The normalized global modular lift is unique. The normalizations
are at two actual points of its upper-half-plane source. -/
theorem normalized_modular_lift_unique {f g : ℍ → ℍ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hJ : ∀ z, modularJ (f z) = modularJ (g z)) (a b : ℍ)
    (hfa : f a = rhoPoint) (hga : g a = rhoPoint)
    (hfb : f b = UpperHalfPlane.I) (hgb : g b = UpperHalfPlane.I) : f = g := by
  obtain ⟨x, hx⟩ := exists_regular_modular_value_of_centers hf.continuous a b hfa hfb
  exact modular_lifts_eq_of_two_values hf hg hJ x hx a b (hfa.trans hga.symm)
    (hfb.trans hgb.symm) (by simpa only [hfa, hfb] using rhoPoint_ne_I)

theorem modular_T_has_no_fixed_point (z : ℍ) : T • z ≠ z := by
  intro h
  have hc := congrArg (fun w : ℍ => (w : ℂ)) h
  rw [modular_T_smul, coe_vadd] at hc
  have hr := congrArg Complex.re hc
  simp only [Complex.add_re, Complex.ofReal_one, Complex.one_re] at hr
  linarith

theorem modularRho_fixed_iff (z : ℍ) : (T * S) • z = z ↔ z = rhoPoint := by
  constructor
  · intro hz
    by_contra hzr
    have hid := modularSL_action_identity_of_two_fixed (T * S) TS_smul_rhoPoint hz
      (Ne.symm hzr)
    have hI := hid UpperHalfPlane.I
    rw [mul_smul, S_smul_I] at hI
    exact modular_T_has_no_fixed_point UpperHalfPlane.I hI
  · rintro rfl
    exact TS_smul_rhoPoint

theorem modularI_fixed_iff (z : ℍ) : S • z = z ↔ z = UpperHalfPlane.I := by
  constructor
  · intro hz
    by_contra hzi
    have hid := modularSL_action_identity_of_two_fixed S S_smul_I hz (Ne.symm hzi)
    have hρ : T • rhoPoint = rhoPoint := by
      simpa only [mul_smul, hid rhoPoint] using TS_smul_rhoPoint
    exact modular_T_has_no_fixed_point rhoPoint hρ
  · rintro rfl
    exact S_smul_I

/-- The two covariance laws of Definition 3.1, on the constructed actual
triangle generators. -/
def TauCovariant (τ : ℍ → ℍ) : Prop :=
  (∀ z : ℍ, (τ (Triangle.generatorOneSL • z) : ℂ) =
    ((τ z : ℂ) - 1) / (τ z : ℂ)) ∧
  (∀ z : ℍ, (τ (Triangle.generatorTwoSL • z) : ℂ) = -1 / (τ z : ℂ))

/-- The generator equations force the two elliptic normalizing values;
these values need not be independently assumed. -/
theorem tau_covariant_values {τ : ℍ → ℍ} (hτ : TauCovariant τ) :
    τ Triangle.centerOne = rhoPoint ∧ τ Triangle.centerTwo = UpperHalfPlane.I := by
  constructor
  · apply (modularRho_fixed_iff _).mp
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    have h := hτ.1 Triangle.centerOne
    rw [Triangle.generatorOne_fix] at h
    exact h.symm
  · apply (modularI_fixed_iff _).mp
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    have h := hτ.2 Triangle.centerTwo
    rw [Triangle.generatorTwo_fix] at h
    exact h.symm

/-- The uniqueness assertion for the global special `τ`: its modular
equation and two generator laws determine a holomorphic map uniquely.
No existence assertion is hidden in the hypotheses. -/
theorem global_tau_unique {τ σ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hσ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω σ)
    (hJ : ∀ z, modularJ (τ z) = modularJ (σ z))
    (hτc : TauCovariant τ) (hσc : TauCovariant σ) : τ = σ :=
  normalized_modular_lift_unique hτ hσ hJ Triangle.centerOne Triangle.centerTwo
    (tau_covariant_values hτc).1 (tau_covariant_values hσc).1
    (tau_covariant_values hτc).2 (tau_covariant_values hσc).2

end Wikipedia.HopfProblem.SpecialPeriods
