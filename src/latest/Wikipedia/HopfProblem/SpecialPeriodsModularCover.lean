import Wikipedia.HopfProblem.SpecialPeriodsModularQuotientFibres
import Wikipedia.HopfProblem.SpecialPeriodsModularQuotientTopology
import Wikipedia.HopfProblem.SpecialPeriodsModularRamification
import Mathlib.Topology.Covering.Basic

/-!
# The actual modular quotient covers the regular j-values

The inverse-function theorem for the constructed `j` gives injective local
neighbourhoods in the upper half-plane. Their open images in the orbit
quotient are injective neighbourhoods for the descended map, since every
orbit identification preserves `j`. Properness and finite fibres turn
these local homeomorphisms into a covering over `ℂ \ {0,1728}`.

This construction uses neither a stabilizer classification nor the
unproved-at-this-stage assertion that `j` separates modular orbits.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped MatrixGroups Modular

namespace Wikipedia.HopfProblem.SpecialPeriods

def modularRegularValues : Set ℂ := ({0, 1728} : Set ℂ)ᶜ

@[simp] theorem mem_modularRegularValues (c : ℂ) :
    c ∈ modularRegularValues ↔ c ≠ 0 ∧ c ≠ 1728 := by
  simp [modularRegularValues]

theorem modularRegularValues_isOpen : IsOpen modularRegularValues :=
  ((finite_singleton (1728 : ℂ)).insert 0).isClosed.isOpen_compl

/-- A genuinely injective open neighbourhood of each regular point of `j`. -/
theorem modularJ_regular_injOn_neighbourhood (z : ℍ)
    (h₀ : modularJ z ≠ 0) (h₁ : modularJ z ≠ 1728) :
    ∃ U : Set ℍ, IsOpen U ∧ z ∈ U ∧ Set.InjOn modularJ U := by
  have hleft : ∀ᶠ w in 𝓝 z, modularLocalInverse z h₀ h₁ (modularJ w) = (w : ℂ) := by
    have h := continuous_coe.continuousAt.tendsto.eventually
      (modularLocalInverse_eventually_left_inverse z h₀ h₁)
    simpa only [Function.comp_apply, ofComplex_apply] using h
  obtain ⟨U, hU, hUo, hz⟩ := mem_nhds_iff.mp hleft
  refine ⟨U, hUo, hz, ?_⟩
  intro w hw v hv heq
  apply UpperHalfPlane.ext
  rw [← hU hw, ← hU hv, heq]

/-- An injective `j` neighbourhood remains injective after passage to the
orbit quotient. The orbit projection is open, so it is a neighbourhood. -/
theorem modularQuotientJ_regular_injOn_neighbourhood (x : ModularOrbitSpace)
    (hx : modularQuotientJ x ∈ modularRegularValues) :
    ∃ V : Set ModularOrbitSpace, IsOpen V ∧ x ∈ V ∧ Set.InjOn modularQuotientJ V := by
  obtain ⟨z, rfl⟩ := modularOrbitProjection_surjective x
  obtain ⟨h₀, h₁⟩ := (mem_modularRegularValues _).mp hx
  obtain ⟨U, hUo, hz, hinj⟩ := modularJ_regular_injOn_neighbourhood z h₀ h₁
  refine ⟨modularOrbitProjection '' U, modularOrbitProjection_isOpenMap U hUo,
    ⟨z, hz, rfl⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩ _ ⟨v, hv, rfl⟩ h
  exact congrArg modularOrbitProjection (hinj hw hv h)

theorem modularQuotientJ_regular_isLocalHomeomorphOn :
    IsLocalHomeomorphOn modularQuotientJ (modularQuotientJ ⁻¹' modularRegularValues) := by
  intro x hx
  obtain ⟨V, hVo, hxV, hinj⟩ := modularQuotientJ_regular_injOn_neighbourhood x hx
  let e := OpenPartialHomeomorph.ofContinuousOpen
    (hinj.toPartialEquiv modularQuotientJ V) modularQuotientJ_continuous.continuousOn
    modularQuotientJ_isOpenMap hVo
  exact ⟨e, hxV, rfl⟩

/-- The descended map is an actual covering on all regular modular values. -/
theorem modularQuotientJ_regular_isCoveringMapOn :
    IsCoveringMapOn modularQuotientJ modularRegularValues :=
  modularQuotientJ_isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
    (fun c _ => modularQuotientJ_fibre_finite c) modularQuotientJ_regular_isLocalHomeomorphOn

abbrev ModularRegularBase := ↥modularRegularValues
abbrev ModularRegularOrbitSpace := ↥(modularQuotientJ ⁻¹' modularRegularValues)

def modularRegularQuotientJ : ModularRegularOrbitSpace → ModularRegularBase :=
  modularRegularValues.restrictPreimage modularQuotientJ

theorem modularRegularQuotientJ_isCoveringMap : IsCoveringMap modularRegularQuotientJ :=
  modularQuotientJ_regular_isCoveringMapOn.isCoveringMap_restrictPreimage

@[simp] theorem modularRegularQuotientJ_apply (x : ModularRegularOrbitSpace) :
    (modularRegularQuotientJ x : ℂ) = modularQuotientJ x := rfl

theorem modularRegularQuotientJ_surjective : Function.Surjective modularRegularQuotientJ := by
  intro c
  obtain ⟨x, hx⟩ := modularQuotientJ_surjective c
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  change modularQuotientJ x ∈ modularRegularValues
  rw [hx]
  exact c.2

end Wikipedia.HopfProblem.SpecialPeriods
