import Wikipedia.HopfProblem.SpecialPeriodsModular

/-!
# Surjectivity of the constructed modular j-function

The actual modular function of Section 3.1 takes every complex value.  If a
value were omitted, its reciprocal resolvent would be a holomorphic
weight-zero modular form.  The simple pole of `j` at infinity makes this
resolvent vanish at the cusp.  Constancy of level-one weight-zero modular
forms would then make the resolvent identically zero, a contradiction.

In particular, the conclusion does not assume a valence formula, a
fundamental-domain bijection, or a modular covering theorem.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane ModularForm
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The reciprocal resolvent tends to zero at the cusp, for every complex
parameter.  No omission hypothesis is needed for this limit. -/
theorem inv_modularJ_sub_tendsto (c : ℂ) :
    Tendsto (fun z : ℍ => (modularJ z - c)⁻¹) atImInfty (𝓝 0) := by
  exact tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded c).comp
    (tendsto_norm_atTop_iff_cobounded.mp norm_modularJ_tendsto))

private theorem inv_modularJ_sub_slash (c : ℂ) (γ : SL(2, ℤ)) :
    (fun z : ℍ => (modularJ z - c)⁻¹) ∣[(0 : ℤ)] γ =
      fun z : ℍ => (modularJ z - c)⁻¹ := by
  funext z
  simp only [SL_slash_apply, neg_zero, zpow_zero, mul_one]
  exact congrArg (fun w : ℂ => (w - c)⁻¹) (modularJ_SL_invariant γ z)

/-- An omitted value would give an actual weight-zero modular form, with
holomorphicity and boundedness at every cusp proved from the construction. -/
private def omittedValueModularForm (c : ℂ) (hc : ∀ z : ℍ, modularJ z ≠ c) :
    ModularForm 𝒮ℒ 0 where
  toFun z := (modularJ z - c)⁻¹
  slash_action_eq' := by
    rintro γ ⟨γ', rfl⟩
    exact inv_modularJ_sub_slash c γ'
  holo' := (modularJ_mdifferentiable.sub mdifferentiable_const).inv
    (fun z => sub_ne_zero.mpr (hc z))
  bdd_at_cusps' {s} hs := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hs]
    intro γ _
    rw [inv_modularJ_sub_slash]
    exact ZeroAtFilter.boundedAtFilter (inv_modularJ_sub_tendsto c)

/-- The normalized modular j-function constructed from the Eisenstein
series and the discriminant takes every finite complex value. -/
theorem modularJ_surjective : Function.Surjective modularJ := by
  intro c
  by_contra h
  have hc : ∀ z : ℍ, modularJ z ≠ c := fun z hz => h ⟨z, hz⟩
  let f := omittedValueModularForm c hc
  obtain ⟨a, ha⟩ := ModularFormClass.levelOne_weight_zero_const f
  have hlim : Tendsto (fun _ : ℍ => a) atImInfty (𝓝 (0 : ℂ)) := by
    change Tendsto (Function.const ℍ a) atImInfty (𝓝 (0 : ℂ))
    rw [← ha]
    exact inv_modularJ_sub_tendsto c
  have ha₀ : a = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have hz : (modularJ UpperHalfPlane.I - c)⁻¹ = 0 := by
    have he := congr_fun ha UpperHalfPlane.I
    change (modularJ UpperHalfPlane.I - c)⁻¹ = a at he
    exact he.trans ha₀
  exact inv_ne_zero (sub_ne_zero.mpr (hc UpperHalfPlane.I)) hz

end Wikipedia.HopfProblem.SpecialPeriods
