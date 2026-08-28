import Wikipedia.HopfProblem.SpecialPeriodsModularQuotient
import Wikipedia.HopfProblem.SpecialPeriodsModularTopology
import Mathlib.Topology.DiscreteSubset

/-!
# Finite fibres of the actual quotient modular map

The identity theorem on the upper half-plane makes every fibre of the
nonconstant constructed `j`-function discrete.  A compact truncated
fundamental domain therefore meets such a fibre finitely, and every
quotient-fibre point has a representative in that finite set.  This proves
finiteness, but does not assert that distinct modular orbits are separated.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped MatrixGroups Modular Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem modularJ_compact_fibre_finite {K : Set ℍ} (hK : IsCompact K) (c : ℂ) :
    (K ∩ modularJ ⁻¹' {c}).Finite := by
  have hd : IsDiscrete (K ∩ {z : ℍ | modularJ z = c}) :=
    (modularJ_fibre_isDiscrete c).mono inter_subset_right
  have h := (hK.inter_right (modularJ_fibre_isClosed c)).finite
    hd
  simpa only [Set.preimage, Set.mem_singleton_iff] using h

/-- Every fibre on the genuine modular orbit space is finite. -/
theorem modularQuotientJ_fibre_finite (c : ℂ) : (modularQuotientJ ⁻¹' {c}).Finite := by
  obtain ⟨A, hA⟩ := modularQuotientJ_bounded_representatives ‖c‖
  have hfinite := modularJ_compact_fibre_finite
    (ModularGroup.isCompact_truncatedFundamentalDomain A) c
  apply (hfinite.image modularOrbitProjection).subset
  intro x hx
  have hxc : modularQuotientJ x = c := hx
  obtain ⟨z, hz, hzx⟩ := hA x (by rw [hxc])
  refine ⟨z, ⟨hz, ?_⟩, hzx⟩
  change modularJ z = c
  rw [← modularQuotientJ_projection, hzx, hxc]

theorem modularQuotientJ_surjective : Function.Surjective modularQuotientJ := by
  intro c
  obtain ⟨z, hz⟩ := modularJ_surjective c
  exact ⟨modularOrbitProjection z, hz⟩

theorem modularQuotientJ_fibre_nonempty (c : ℂ) : (modularQuotientJ ⁻¹' {c}).Nonempty :=
  modularQuotientJ_surjective c

theorem modularQuotientJ_isOpenMap : IsOpenMap modularQuotientJ :=
  IsOpenMap.of_comp modularOrbitProjection_continuous modularOrbitProjection_surjective
    modularJ_isOpenMap

theorem modularQuotientJ_isOpenQuotientMap : IsOpenQuotientMap modularQuotientJ :=
  ⟨modularQuotientJ_surjective, modularQuotientJ_continuous, modularQuotientJ_isOpenMap⟩

/-- The already proved properness combines with genuine surjectivity and
finite fibres; none of these conclusions assumes a modular-curve model. -/
theorem modularQuotientJ_proper_finite_surjective :
    IsProperMap modularQuotientJ ∧ Function.Surjective modularQuotientJ ∧
      ∀ c : ℂ, (modularQuotientJ ⁻¹' {c}).Finite :=
  ⟨modularQuotientJ_proper, modularQuotientJ_surjective, modularQuotientJ_fibre_finite⟩

end Wikipedia.HopfProblem.SpecialPeriods
