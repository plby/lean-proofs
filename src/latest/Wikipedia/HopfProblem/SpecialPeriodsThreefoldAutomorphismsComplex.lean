import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsIdentityComponent
import Wikipedia.HopfProblem.HolomorphicAutomorphismComplexGroup

/-!
# The genuine identity component as a complex Lie group

Only after proving the topological group identification do we construct
the analytic atlas on the actual identity component. Its topology is
still the original compact-open subspace topology. The identification
with `ℂˣ` is an actual biholomorphism, the original group operations are
holomorphic, and evaluation on the original threefold is jointly
holomorphic.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- An analytic atlas on the actual compact-open identity component,
obtained from the proved open embedding into the punctured complex plane. -/
@[instance_reducible]
def identityComponentChartedSpace : ChartedSpace ℂ Aut₀ :=
  HolomorphicAutomorphismComplexGroup.chartedSpace identityComponentMulEquiv

theorem identityComponent_isManifold :
    letI := identityComponentChartedSpace
    IsManifold 𝓘(ℂ) ω Aut₀ :=
  HolomorphicAutomorphismComplexGroup.isManifold identityComponentMulEquiv

/-- The original multiplication and inverse make the actual identity
component a complex Lie group for the unchanged compact-open topology. -/
theorem identityComponent_lieGroup :
    letI := identityComponentChartedSpace
    LieGroup 𝓘(ℂ) ω Aut₀ :=
  HolomorphicAutomorphismComplexGroup.lieGroup identityComponentMulEquiv

/-- The actual identity component is biholomorphic to the usual complex
multiplicative group, by the original vertical action. -/
def identityComponentBiholomorph :
    letI := identityComponentChartedSpace
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) ℂˣ Aut₀ ω :=
  HolomorphicAutomorphismComplexGroup.diffeomorph identityComponentMulEquiv

@[simp] theorem identityComponentBiholomorph_apply (u : ℂˣ) :
    letI := identityComponentChartedSpace
    identityComponentBiholomorph u = verticalIdentityHom u := rfl

theorem identityComponentBiholomorph_mul (u v : ℂˣ) :
    letI := identityComponentChartedSpace
    identityComponentBiholomorph (u * v) =
      identityComponentBiholomorph u * identityComponentBiholomorph v :=
  identityComponentMulEquiv.map_mul u v

/-- The biholomorphism retains the already proved original topological
group equivalence exactly. -/
theorem identityComponentBiholomorph_toHomeomorph :
    letI := identityComponentChartedSpace
    identityComponentBiholomorph.toHomeomorph = identityComponentMulEquiv.toHomeomorph :=
  HolomorphicAutomorphismComplexGroup.diffeomorph_toHomeomorph identityComponentMulEquiv

/-- Evaluation of every element of the genuine identity component on
the original threefold is jointly holomorphic. -/
theorem identityComponent_evaluation_holomorphic :
    letI := identityComponentChartedSpace
    ContMDiff (𝓘(ℂ).prod IF) IF ω
      (fun p : Aut₀ × Threefold.Space => (p.1 : Aut) p.2) := by
  let := identityComponentChartedSpace
  have hp : ContMDiff (𝓘(ℂ).prod IF) (𝓘(ℂ).prod IF) ω
      (fun p : Aut₀ × Threefold.Space => (identityComponentMulEquiv.symm p.1, p.2)) :=
    ((HolomorphicAutomorphismComplexGroup.contMDiff_symm identityComponentMulEquiv).comp
      contMDiff_fst).prodMk contMDiff_snd
  have h := verticalHom_joint_holomorphic.comp hp
  have he : (fun p : Aut₀ × Threefold.Space =>
      verticalHom (identityComponentMulEquiv.symm p.1) p.2) =
      (fun p : Aut₀ × Threefold.Space => (p.1 : Aut) p.2) := by
    funext p
    exact congrArg (fun f : Aut₀ => (f : Aut) p.2)
      (identityComponentMulEquiv.apply_symm_apply p.1)
  simpa only [Function.comp_def, he] using h

/-- The native tangent space of the actual identity component is a
complex line, for its proved compatible analytic structure. -/
theorem identityComponent_tangent_finrank :
    letI := identityComponentChartedSpace
    Module.finrank ℂ (TangentSpace 𝓘(ℂ) (1 : Aut₀)) = 1 := by
  let := identityComponentChartedSpace
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
