import Wikipedia.HopfProblem.SpecialPeriodsModular
import Mathlib.NumberTheory.Modular
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properness of the actual modular function on the modular orbit space

The invariant modular function descends to the topological `SL₂(ℤ)` orbit
quotient of the upper half-plane.  Its compact preimages are obtained from
compact truncated fundamental domains: cusp growth bounds the height of
every representative in the closed fundamental domain.  No separation of
orbits by `j`, modular-curve identification, or covering property is assumed.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped MatrixGroups Modular

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual topological orbit space, including the elliptic orbits. -/
abbrev ModularOrbitSpace := Quotient (MulAction.orbitRel SL(2, ℤ) ℍ)

def modularOrbitProjection : ℍ → ModularOrbitSpace := Quotient.mk _

theorem modularOrbitProjection_continuous : Continuous modularOrbitProjection :=
  continuous_quotient_mk'

theorem modularOrbitProjection_surjective : Function.Surjective modularOrbitProjection :=
  Quotient.mk_surjective

@[simp] theorem modularOrbitProjection_smul (γ : SL(2, ℤ)) (z : ℍ) :
    modularOrbitProjection (γ • z) = modularOrbitProjection z :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The actual modular `j` function on the orbit quotient. -/
def modularQuotientJ : ModularOrbitSpace → ℂ :=
  Quotient.lift modularJ (by
    intro z w h
    change z ∈ MulAction.orbit SL(2, ℤ) w at h
    obtain ⟨γ, rfl⟩ := h
    exact modularJ_SL_invariant γ w)

@[simp] theorem modularQuotientJ_projection (z : ℍ) :
    modularQuotientJ (modularOrbitProjection z) = modularJ z := rfl

theorem modularQuotientJ_continuous : Continuous modularQuotientJ :=
  modularJ_continuous.quotient_lift _

/-- A bounded set of `j`-values cannot have representatives arbitrarily
high in the upper half-plane. -/
theorem modularJ_bounded_im (R : ℝ) :
    ∃ A : ℝ, ∀ z : ℍ, ‖modularJ z‖ ≤ R → z.im ≤ A := by
  have h := norm_modularJ_tendsto.eventually (eventually_gt_atTop R)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem {z : ℍ | R < ‖modularJ z‖}).mp h
  refine ⟨A, fun z hz => ?_⟩
  by_contra hzA
  exact (not_lt_of_ge hz) (hA z (le_of_lt (lt_of_not_ge hzA)))

/-- Every orbit with bounded `j` has a representative in one fixed compact
truncation of the standard fundamental domain. -/
theorem modularQuotientJ_bounded_representatives (R : ℝ) :
    ∃ A : ℝ, ∀ x : ModularOrbitSpace, ‖modularQuotientJ x‖ ≤ R →
      x ∈ modularOrbitProjection '' ModularGroup.truncatedFundamentalDomain A := by
  obtain ⟨A, hA⟩ := modularJ_bounded_im R
  refine ⟨A, ?_⟩
  intro x hx
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd z
  refine ⟨γ • z, ⟨hγ, hA (γ • z) ?_⟩, modularOrbitProjection_smul γ z⟩
  simpa only [modularJ_SL_invariant, modularQuotientJ_projection] using hx

theorem modularQuotientJ_isCompact_preimage {K : Set ℂ} (hK : IsCompact K) :
    IsCompact (modularQuotientJ ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨A, hA⟩ := modularQuotientJ_bounded_representatives R
  have hcompact : IsCompact
      (modularOrbitProjection '' ModularGroup.truncatedFundamentalDomain A) :=
    (ModularGroup.isCompact_truncatedFundamentalDomain A).image modularOrbitProjection_continuous
  exact hcompact.of_isClosed_subset (hK.isClosed.preimage modularQuotientJ_continuous)
    (fun x hx => hA x (hR _ hx))

/-- Properness is proved on the genuine orbit quotient, without assuming
that `j` is injective there. -/
theorem modularQuotientJ_proper : IsProperMap modularQuotientJ :=
  isProperMap_iff_isCompact_preimage.mpr
    ⟨modularQuotientJ_continuous, fun _ hK => modularQuotientJ_isCompact_preimage hK⟩

theorem modularQuotientJ_isClosedMap : IsClosedMap modularQuotientJ :=
  modularQuotientJ_proper.isClosedMap

theorem modularQuotientJ_fibre_compact (c : ℂ) :
    IsCompact (modularQuotientJ ⁻¹' {c}) :=
  modularQuotientJ_isCompact_preimage isCompact_singleton

end Wikipedia.HopfProblem.SpecialPeriods
