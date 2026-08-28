import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedLocus
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphisms

/-!
# The same finite subgroup inside the genuine automorphism component

The subgroup is the image of the literal complex roots of unity under
the proved action isomorphism. Its elements are exactly the actual
identity-component automorphisms whose `n`-th power is the identity.
The inherited action is evaluation of the original biholomorphisms,
and its fixed-point set is the same original double curve.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed

open Automorphisms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- The actual finite subgroup of the genuine automorphism identity component. -/
def identityRoots (n : ℕ) : Subgroup Aut₀ :=
  (rootsOfUnity n ℂ).map verticalIdentityHom

/-- Membership means that the original automorphism's `n`-th iterate
is the identity, not merely that a chosen parameter has finite order. -/
theorem mem_identityRoots_iff (n : ℕ) (f : Aut₀) :
    f ∈ identityRoots n ↔ f ^ n = 1 := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [← map_pow, (mem_rootsOfUnity n u).mp hu, map_one]
  · intro hf
    obtain ⟨u, rfl⟩ := verticalIdentityHom_surjective f
    refine ⟨u, ?_, rfl⟩
    apply (mem_rootsOfUnity n u).mpr
    apply verticalIdentityHom_injective
    simpa only [map_pow, map_one] using hf

/-- The subgroup is finite in the existing full automorphism group. -/
theorem identityRoots_finite {n : ℕ} (hn : 0 < n) : Finite (identityRoots n) := by
  let := rootsOfUnity_finite hn
  let f : rootsOfUnity n ℂ → identityRoots n :=
    fun u => ⟨verticalIdentityHom u.val, ⟨u.val, u.property, rfl⟩⟩
  apply Finite.of_surjective f
  rintro ⟨g, u, hu, hug⟩
  exact ⟨⟨u, hu⟩, Subtype.ext hug⟩

/-- Evaluation of this actual finite automorphism subgroup fixes
precisely the existing native cusp double curve. -/
theorem identityRoots_fixedPoints_eq_D₀ (n : ℕ) (hn : 2 ≤ n) :
    MulAction.fixedPoints (identityRoots n) Space = VerticalAction.D₀ := by
  let := VerticalAction.action
  ext x
  constructor
  · intro hx
    rw [← rootsOfUnity_fixedPoints_eq_D₀ n hn]
    intro u
    have hu : verticalIdentityHom u.val ∈ identityRoots n := ⟨u.val, u.property, rfl⟩
    exact hx ⟨verticalIdentityHom u.val, hu⟩
  · intro hx g
    obtain ⟨u, hu, hug⟩ := g.property
    have he : (verticalIdentityHom u : Aut) x = x :=
      (VerticalAction.action_fixed_iff x).mpr hx u
    change (g.val : Aut) x = x
    rw [← hug]
    exact he

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed
