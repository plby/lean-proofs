import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsComplex

/-!
# Proposition 9.23: the genuine automorphism identity component

The full group consists of every biholomorphism of the original native
threefold, with the usual compact-open topology. A proved local
normal-family rigidity argument identifies its actual identity connected
component with the constructed vertical action. The resulting equivalence
is both a topological group isomorphism and an analytic diffeomorphism;
the actual evaluation action is jointly holomorphic and fibre-preserving.

The proof uses the already established one-dimensional space of all
native holomorphic tangent sections, but does not assume an automorphism
Lie-group theorem or infer local openness merely from that dimension.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space

/-- A statement in the full native automorphism group: membership in
its actual identity component is equivalent to one unique vertical
multiplicative parameter. -/
theorem mem_connectedComponent_iff_existsUnique_parameter (f : Aut) :
    f ∈ connectedComponent (1 : Aut) ↔ ∃! u : ℂˣ, verticalHom u = f := by
  constructor
  · intro hf
    have hr : f ∈ (verticalHom.range : Set Aut) := by
      rwa [verticalHom_range_eq_connectedComponent]
    obtain ⟨u, hu⟩ := hr
    exact ⟨u, hu, fun v hv => verticalHom_injective (hv.trans hu.symm)⟩
  · rintro ⟨u, hu, _⟩
    rw [← hu]
    exact verticalHom_mem_identityComponent u

/-- The actual additive flow is surjective onto the genuine identity
component, with its existing normalization as translation by `s e₂`. -/
theorem exists_flow_parameter (f : Aut₀) :
    ∃ s : ℂ, ∀ x : Threefold.Space, (f : Aut) x = VerticalAction.flow s x := by
  obtain ⟨u, rfl⟩ := verticalIdentityHom_surjective f
  obtain ⟨s, rfl⟩ := VerticalAction.Exponential.normalizedExponential_surjective u
  exact ⟨s, VerticalAction.actionBiholomorph_exponential s⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
