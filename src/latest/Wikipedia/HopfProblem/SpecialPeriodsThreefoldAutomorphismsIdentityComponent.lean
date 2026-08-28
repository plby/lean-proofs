import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsRigidity
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsToricRecovery

/-!
# The actual identity component is the complex multiplicative group

The full group is the group of all biholomorphisms of the original
threefold, equipped with its usual compact-open topology. Local rigidity
proved that its actual identity component is exactly the existing
vertical action image. The independently proved parameter recovery makes
this identification a homeomorphism as well as a group isomorphism.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- The genuine identity component, with its original subspace topology,
is isomorphic as a topological group to `ℂˣ`. -/
def identityComponentMulEquiv : ℂˣ ≃ₜ* Aut₀ := by
  let e : ℂˣ ≃* Aut₀ := MulEquiv.ofBijective verticalIdentityHom
    ⟨verticalIdentityHom_injective, verticalIdentityHom_surjective⟩
  refine { e with
    continuous_toFun := verticalIdentityHom_continuous
    continuous_invFun := ?_ }
  apply verticalHom_isEmbedding.isInducing.continuous_iff.mpr
  have he : verticalHom ∘ e.symm = fun f : Aut₀ => (f : Aut) := by
    funext f
    exact congrArg Subtype.val (e.apply_symm_apply f)
  change Continuous (verticalHom ∘ e.symm)
  rw [he]
  exact continuous_subtype_val

@[simp] theorem identityComponentMulEquiv_apply (u : ℂˣ) :
    identityComponentMulEquiv u = verticalIdentityHom u := rfl

/-- The topological group identification is the original action pointwise. -/
@[simp] theorem identityComponentMulEquiv_apply_point (u : ℂˣ) (x : Threefold.Space) :
    (identityComponentMulEquiv u : Aut) x = VerticalAction.actionBiholomorph u x := rfl

/-- Every element of the actual identity component has one unique
multiplicative parameter in the previously constructed action. -/
theorem existsUnique_vertical_parameter (f : Aut₀) :
    ∃! u : ℂˣ, verticalIdentityHom u = f := by
  refine ⟨identityComponentMulEquiv.symm f, identityComponentMulEquiv.apply_symm_apply f, ?_⟩
  intro u hu
  exact verticalIdentityHom_injective (hu.trans
    (identityComponentMulEquiv.apply_symm_apply f).symm)

/-- Every automorphism in the actual identity component preserves the
original map to the sphere. -/
theorem identityComponent_projectionSphere (f : Aut₀) (x : Threefold.Space) :
    projectionSphere ((f : Aut) x) = projectionSphere x := by
  obtain ⟨u, rfl⟩ := verticalIdentityHom_surjective f
  exact verticalHom_projectionSphere u x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
