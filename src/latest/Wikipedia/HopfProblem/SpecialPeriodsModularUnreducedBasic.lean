import Wikipedia.HopfProblem.SpecialPeriodsModularCoverDegree
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# The actual regular upper-half-plane modular map

The source is the open subset of the upper half-plane on which `j` avoids
the two elliptic values; the target is the corresponding open subset of
the ordinary complex plane. Both complex structures are inherited from
these existing manifolds. No quotient is taken in the source.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

def modularRegularUpper : TopologicalSpace.Opens ℍ :=
  ⟨modularJ ⁻¹' modularRegularValues, modularRegularValues_isOpen.preimage modularJ_continuous⟩

def modularRegularPlane : TopologicalSpace.Opens ℂ :=
  ⟨modularRegularValues, modularRegularValues_isOpen⟩

/-- The exceptional locus is discrete and countable, so its removal from
the upper half-plane leaves a connected covering source. -/
instance modularRegularUpper_pathConnected : PathConnectedSpace modularRegularUpper := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  exact modularExceptionalSet_compl_isPathConnected

/-- The unreduced regular modular map, with its actual upper-half-plane source. -/
def modularUnreducedJ (z : modularRegularUpper) : modularRegularPlane := ⟨modularJ z, z.2⟩

@[simp] theorem modularUnreducedJ_coe (z : modularRegularUpper) :
    (modularUnreducedJ z : ℂ) = modularJ z := rfl

theorem modularUnreducedJ_continuous : Continuous modularUnreducedJ :=
  (modularJ_continuous.comp continuous_subtype_val).subtype_mk _

theorem modularUnreducedJ_surjective : Function.Surjective modularUnreducedJ := by
  intro c
  obtain ⟨z, hz⟩ := modularJ_surjective c
  refine ⟨⟨z, ?_⟩, Subtype.ext hz⟩
  change modularJ z ∈ modularRegularValues
  rw [hz]
  exact c.2

theorem modularUnreducedJ_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω modularUnreducedJ := by
  intro z
  have he : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω
      (fun w : modularRegularUpper => (modularUnreducedJ w : ℂ)) z ↔
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω modularUnreducedJ z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((modularJ_holomorphic.comp contMDiff_subtype_val) z)

theorem modularUnreducedJ_isOpenMap : IsOpenMap modularUnreducedJ := by
  have h := modularJ_isOpenMap.comp modularRegularUpper.isOpen.isOpenMap_subtype_val
  exact h.codRestrict (fun z => z.2)

theorem modularUnreducedJ_isOpenQuotientMap : IsOpenQuotientMap modularUnreducedJ :=
  ⟨modularUnreducedJ_surjective, modularUnreducedJ_continuous, modularUnreducedJ_isOpenMap⟩

end Wikipedia.HopfProblem.SpecialPeriods
