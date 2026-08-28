import Wikipedia.HopfProblem.SpecialPeriodsThreefoldAutomorphismsRigidityField
import Wikipedia.HopfProblem.HolomorphicAutomorphismDisplacementNonzero

/-!
# Local rigidity in the full compact-open automorphism group

Failure of local surjectivity of the actual vertical action would yield
an actual normalized sequence of full native automorphisms. Compact
holomorphic normal limits give a nonzero native field, while the proved
classification and preserved local detector force that same field to be
zero. Thus the actual action image is a neighborhood of the identity.
No automorphism Lie-group theorem or infinitesimal-to-global assumption
is used.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_compact Threefold.space_t2Space Threefold.space_secondCountable

/-- There is no genuine normalized sequence outside the vertical action. -/
theorem normalizedSequence_false (S : NormalizedSequence) : False := by
  obtain ⟨T, h, hd, hlim⟩ := S.exists_coordinate_limits
  obtain ⟨i, z, hz, hne⟩ :=
    HolomorphicAutomorphism.Displacement.exists_ne_zero_of_locallyUniformLimits
      rigidityAtlas T.tends_one T.chart_valid T.ne_one hlim
  exact hne (T.coordinate_limits_eq_zero h hd hlim i z hz)

/-- The constructed action contains an actual neighborhood in the full
usual compact-open biholomorphism group. -/
theorem verticalHom_range_mem_nhds_one :
    (verticalHom.range : Set Aut) ∈ 𝓝 (1 : Aut) := by
  by_contra hnot
  obtain ⟨S⟩ := exists_normalizedSequence hnot
  exact normalizedSequence_false S

/-- The vertical action is an open subgroup of the actual full group. -/
theorem verticalHom_range_isOpen : IsOpen (verticalHom.range : Set Aut) :=
  verticalHom.range.isOpen_of_mem_nhds verticalHom_range_mem_nhds_one

/-- Its image is exactly the genuine identity connected component, not
a component defined using a selected family of automorphisms. -/
theorem verticalHom_range_eq_connectedComponent :
    (verticalHom.range : Set Aut) = connectedComponent (1 : Aut) :=
  HolomorphicAutomorphismComponents.range_eq_connectedComponent_of_mem_nhds
    verticalHom verticalHom_continuous verticalHom_range_mem_nhds_one

/-- Every automorphism in the genuine identity component is one of the
previously constructed vertical multiplicative time maps. -/
theorem verticalIdentityHom_surjective : Function.Surjective verticalIdentityHom := by
  intro f
  have hf : (f : Aut) ∈ verticalHom.range := by
    change (f : Aut) ∈ (verticalHom.range : Set Aut)
    rw [verticalHom_range_eq_connectedComponent]
    exact f.property
  obtain ⟨u, hu⟩ := hf
  exact ⟨u, Subtype.ext hu⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Automorphisms
