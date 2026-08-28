import Wikipedia.HopfProblem.SpecialPeriodsModularCover
import Wikipedia.HopfProblem.SpecialPeriodsModularQuotientCusp
import Wikipedia.HopfProblem.SpecialPeriodsModularCoverTools

/-!
# The modular function separates actual modular orbits

The regular quotient covering has a singleton fibre near infinity. Path
lifting transports this property across the twice-punctured complex plane.
Since the quotient is Hausdorff and the descended function is open, density
of the regular values extends injectivity across the two elliptic values.

Thus the normalized Eisenstein-series function induces a homeomorphism
from the actual `SL₂(ℤ)` orbit quotient to `ℂ`. No modular-curve
classification or assumed orbit-separation statement enters the proof.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped MatrixGroups Modular

namespace Wikipedia.HopfProblem.SpecialPeriods

instance modularRegularBase_pathConnected : PathConnectedSpace ModularRegularBase :=
  ModularCoverTools.complex_compl_pair_pathConnected 0 1728

theorem modularRegularValues_dense : Dense modularRegularValues :=
  ModularCoverTools.complex_compl_pair_dense 0 1728

theorem modularRegularQuotientJ_exists_subsingleton_fibre :
    ∃ c : ModularRegularBase, Subsingleton (modularRegularQuotientJ ⁻¹' {c}) := by
  obtain ⟨R, hR, hlarge⟩ := modularQuotientJ_unique_fibre_at_large_values
  let r : ℝ := max R 1728 + 1
  have hrpos : 0 < r := by dsimp [r]; linarith [le_max_right R (1728 : ℝ)]
  have hrbig : 1728 < r := by dsimp [r]; linarith [le_max_right R (1728 : ℝ)]
  have hrR : R < r := by dsimp [r]; linarith [le_max_left R (1728 : ℝ)]
  let c : ModularRegularBase := ⟨(r : ℂ), (mem_modularRegularValues _).mpr ⟨by
      exact_mod_cast hrpos.ne', by exact_mod_cast hrbig.ne'⟩⟩
  have hRc : R < ‖(c : ℂ)‖ := by
    change R < ‖(r : ℂ)‖
    simpa only [Complex.norm_real, Real.norm_of_nonneg hrpos.le] using hrR
  obtain ⟨x, hx, hunique⟩ := hlarge c hRc
  refine ⟨c, ⟨?_⟩⟩
  intro u v
  apply Subtype.ext
  apply Subtype.ext
  have hu : modularQuotientJ (u.1 : ModularOrbitSpace) = (c : ℂ) :=
    congrArg Subtype.val (show modularRegularQuotientJ u.1 = c from u.2)
  have hv : modularQuotientJ (v.1 : ModularOrbitSpace) = (c : ℂ) :=
    congrArg Subtype.val (show modularRegularQuotientJ v.1 = c from v.2)
  exact (hunique _ hu).trans (hunique _ hv).symm

/-- The actual regular covering has one sheet everywhere. -/
theorem modularRegularQuotientJ_injective : Function.Injective modularRegularQuotientJ := by
  obtain ⟨c, hc⟩ := modularRegularQuotientJ_exists_subsingleton_fibre
  exact ModularCoverTools.injective_of_covering_singleton_fibre
    modularRegularQuotientJ_isCoveringMap c hc

theorem modularQuotientJ_injOn_regular :
    Set.InjOn modularQuotientJ (modularQuotientJ ⁻¹' modularRegularValues) := by
  intro x hx y hy hxy
  have h : (⟨x, hx⟩ : ModularRegularOrbitSpace) = ⟨y, hy⟩ :=
    modularRegularQuotientJ_injective (Subtype.ext hxy)
  exact congrArg Subtype.val h

/-- Hausdorff separation and the open mapping theorem extend the regular
injectivity across the two omitted values. -/
theorem modularQuotientJ_injective : Function.Injective modularQuotientJ :=
  ModularCoverTools.injective_of_open_dense modularQuotientJ_isOpenMap
    modularRegularValues_dense modularQuotientJ_injOn_regular

/-- The actual modular orbit space is homeomorphic to the finite j-plane. -/
def modularQuotientJHomeomorph : ModularOrbitSpace ≃ₜ ℂ :=
  (Equiv.ofBijective modularQuotientJ
    ⟨modularQuotientJ_injective, modularQuotientJ_surjective⟩).toHomeomorphOfContinuousOpen
      modularQuotientJ_continuous modularQuotientJ_isOpenMap

@[simp] theorem modularQuotientJHomeomorph_apply (x : ModularOrbitSpace) :
    modularQuotientJHomeomorph x = modularQuotientJ x := rfl

/-- Equality of values is equivalent to equality of modular orbits. -/
theorem modularJ_eq_iff_mem_orbit (z w : ℍ) :
    modularJ z = modularJ w ↔ z ∈ MulAction.orbit SL(2, ℤ) w := by
  constructor
  · intro h
    exact Quotient.exact (modularQuotientJ_injective h)
  · intro h
    exact congrArg modularQuotientJ (Quotient.sound h)

theorem modularJ_eq_iff_exists_smul (z w : ℍ) :
    modularJ z = modularJ w ↔ ∃ γ : SL(2, ℤ), γ • w = z :=
  modularJ_eq_iff_mem_orbit z w

/-- The zero fibre consists of precisely the modular orbit of the cubic
elliptic point, not additional unclassified zeros. -/
theorem modularJ_eq_zero_iff_rho_orbit (z : ℍ) :
    modularJ z = 0 ↔ z ∈ MulAction.orbit SL(2, ℤ) rhoPoint := by
  rw [← modularJ_rhoPoint, modularJ_eq_iff_mem_orbit]

theorem modularJ_eq_1728_iff_I_orbit (z : ℍ) :
    modularJ z = 1728 ↔ z ∈ MulAction.orbit SL(2, ℤ) UpperHalfPlane.I := by
  rw [← modularJ_I, modularJ_eq_iff_mem_orbit]

end Wikipedia.HopfProblem.SpecialPeriods
