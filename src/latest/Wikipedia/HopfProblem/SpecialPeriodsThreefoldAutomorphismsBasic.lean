import Wikipedia.HopfProblem.HolomorphicAutomorphismTopology
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionMultiplicative
import Mathlib.Analysis.Complex.Convex

/-!
# The full automorphism group of the original threefold

`Aut` contains every biholomorphism for the actual glued atlas. Its
topology is the ordinary compact-open topology on maps and inverses,
which agrees with the forward compact-open topology by compactness.
`Aut₀` is its actual identity connected component. The already constructed
vertical action gives an injective continuous homomorphism into it.
Surjectivity onto this component is not part of these definitions.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- Every native biholomorphism, with the usual compact-open topology. -/
abbrev Aut := HolomorphicAutomorphism IF Threefold.Space

/-- The genuine identity component of the full topological group. -/
abbrev Aut₀ := ↥(HolomorphicAutomorphism.identityComponent IF Threefold.Space)

theorem mem_identityComponent_iff (f : Aut) :
    f ∈ HolomorphicAutomorphism.identityComponent IF Threefold.Space ↔
      f ∈ connectedComponent (1 : Aut) := Iff.rfl

/-- The already constructed vertical action, now valued in the full
native automorphism group rather than a selected group of time maps. -/
def verticalHom : ℂˣ →* Aut where
  toFun u := HolomorphicAutomorphism.ofDiffeomorph (VerticalAction.actionBiholomorph u)
  map_one' := by
    let := VerticalAction.action
    apply HolomorphicAutomorphism.ext
    intro x
    exact one_smul ℂˣ x
  map_mul' u v := by
    let := VerticalAction.action
    apply HolomorphicAutomorphism.ext
    intro x
    exact mul_smul u v x

@[simp] theorem verticalHom_apply (u : ℂˣ) (x : Threefold.Space) :
    verticalHom u x = VerticalAction.actionBiholomorph u x := rfl

theorem verticalHom_injective : Function.Injective verticalHom := by
  intro u v huv
  apply VerticalAction.actionBiholomorph_injective
  exact congrArg HolomorphicAutomorphism.toDiffeomorph huv

/-- Joint holomorphy is a statement about the original action on the
original manifold; no Lie-group structure on `Aut` is presumed. -/
theorem verticalHom_joint_holomorphic :
    ContMDiff (𝓘(ℂ).prod IF) IF ω
      (fun p : ℂˣ × Threefold.Space => verticalHom p.1 p.2) :=
  VerticalAction.action_holomorphic

theorem verticalHom_continuous : Continuous verticalHom := by
  apply (HolomorphicAutomorphism.continuous_iff_toContinuousMap_of_compact
    IF Threefold.Space).mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact verticalHom_joint_holomorphic.continuous

/-- The action is a continuous homomorphism for the actual compact-open
automorphism topology. -/
def verticalContinuousHom : ℂˣ →ₜ* Aut where
  __ := verticalHom
  continuous_toFun := verticalHom_continuous

theorem verticalHom_mem_identityComponent (u : ℂˣ) :
    verticalHom u ∈ HolomorphicAutomorphism.identityComponent IF Threefold.Space := by
  change verticalHom u ∈ connectedComponent (1 : Aut)
  exact (isPreconnected_range verticalHom_continuous).subset_connectedComponent
    ⟨1, map_one verticalHom⟩ ⟨u, rfl⟩

/-- The actual vertical action takes values in the actual connected
component, by connectedness of the existing complex multiplicative group. -/
def verticalIdentityHom : ℂˣ →* Aut₀ :=
  verticalHom.codRestrict (HolomorphicAutomorphism.identityComponent IF Threefold.Space)
    verticalHom_mem_identityComponent

@[simp] theorem verticalIdentityHom_coe (u : ℂˣ) :
    (verticalIdentityHom u : Aut) = verticalHom u := rfl

theorem verticalIdentityHom_continuous : Continuous verticalIdentityHom :=
  verticalHom_continuous.subtype_mk verticalHom_mem_identityComponent

theorem verticalIdentityHom_injective : Function.Injective verticalIdentityHom := by
  intro u v huv
  exact verticalHom_injective (congrArg Subtype.val huv)

theorem verticalHom_projectionSphere (u : ℂˣ) (x : Threefold.Space) :
    projectionSphere (verticalHom u x) = projectionSphere x :=
  VerticalAction.projectionSphere_action u x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
