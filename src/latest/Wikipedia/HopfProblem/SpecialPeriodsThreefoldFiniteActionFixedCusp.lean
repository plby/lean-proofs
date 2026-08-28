import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFiniteActionFixedCuspQuotient
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedLocus

/-!
# Finite-order fixed points in the actual cusp patch

The correction and radius are those of the constructed cusp. The multiplicative
quotient action is identified pointwise with the original global vertical
action through the proved normalized-exponential formulas. Thus every
nonidentity finite-order parameter has precisely the original fixed curve
`D₀` as its fixed locus in the entire actual cusp patch.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp

/-- Literal multiplicative cusp action specialized to the constructed correction and radius. -/
def specialAction (u : ℂˣ) : CuspGeometry.LocalSpace → CuspGeometry.LocalSpace :=
  quotientAction CuspGeometry.data.correction CuspGeometry.data.radius u

theorem specialAction_exponential (s : ℂ) (x : CuspGeometry.LocalSpace) :
    specialAction (VerticalAction.Exponential.normalizedExponential s) x =
      VerticalAction.Cusp.specialFlow s x :=
  quotientAction_exponential CuspGeometry.data.correction CuspGeometry.data.radius s x

/-- No analytic or smallness hypothesis remains for the actual cusp data. -/
theorem specialAction_fixed_iff_doubleCurve (u : ℂˣ) (hu : u ≠ 1) (hfin : IsOfFinOrder u)
    (x : CuspGeometry.LocalSpace) :
    specialAction u x = x ↔ x ∈ CuspQuotient.doubleCurve CuspGeometry.data.correction
      CuspGeometry.data.radius CuspGeometry.data.radius_pos 1 :=
  quotientAction_fixed_iff_doubleCurve CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
    CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift u hu hfin x

theorem specialAction_fixed_iff_inclusion_mem_doubleCurve (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) (x : CuspGeometry.LocalSpace) :
    specialAction u x = x ↔ CuspGeometry.inclusion x ∈ CuspGeometry.doubleCurve 1 := by
  rw [specialAction_fixed_iff_doubleCurve u hu hfin x, CuspGeometry.doubleCurve]
  exact (CuspGeometry.inclusion_injective.mem_set_image).symm

/-- Identification with the original global action on every point of the cusp patch. -/
theorem actionBiholomorph_cusp (u : ℂˣ) (x : CuspGeometry.LocalSpace) :
    VerticalAction.actionBiholomorph u (CuspGeometry.inclusion x) =
      CuspGeometry.inclusion (specialAction u x) := by
  obtain ⟨s, rfl⟩ := VerticalAction.Exponential.normalizedExponential_surjective u
  rw [VerticalAction.actionBiholomorph_exponential, VerticalAction.flow_cusp,
    specialAction_exponential]

/-- A finite-order parameter fixes an actual cusp point exactly on the existing double curve. -/
theorem actionBiholomorph_inclusion_fixed_iff_doubleCurve (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) (x : CuspGeometry.LocalSpace) :
    VerticalAction.actionBiholomorph u (CuspGeometry.inclusion x) = CuspGeometry.inclusion x ↔
      CuspGeometry.inclusion x ∈ CuspGeometry.doubleCurve 1 := by
  rw [actionBiholomorph_cusp, CuspGeometry.inclusion_injective.eq_iff]
  exact specialAction_fixed_iff_inclusion_mem_doubleCurve u hu hfin x

/-- The finite-order fixed locus in the original cusp patch is precisely the named `D₀`. -/
theorem actionBiholomorph_inclusion_fixed_iff_D₀ (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) (x : CuspGeometry.LocalSpace) :
    VerticalAction.actionBiholomorph u (CuspGeometry.inclusion x) = CuspGeometry.inclusion x ↔
      CuspGeometry.inclusion x ∈ VerticalAction.D₀ :=
  actionBiholomorph_inclusion_fixed_iff_doubleCurve u hu hfin x

/-- The criterion also has the literal group-action form for the existing action instance. -/
theorem action_inclusion_fixed_iff_D₀ (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) (x : CuspGeometry.LocalSpace) :
    letI := VerticalAction.action
    u • CuspGeometry.inclusion x = CuspGeometry.inclusion x ↔
      CuspGeometry.inclusion x ∈ VerticalAction.D₀ :=
  actionBiholomorph_inclusion_fixed_iff_D₀ u hu hfin x

/-- One nontrivial finite-order parameter has the same cusp fixed points as the full action. -/
theorem actionBiholomorph_inclusion_fixed_iff_all (u : ℂˣ) (hu : u ≠ 1)
    (hfin : IsOfFinOrder u) (x : CuspGeometry.LocalSpace) :
    VerticalAction.actionBiholomorph u (CuspGeometry.inclusion x) = CuspGeometry.inclusion x ↔
      ∀ v : ℂˣ, VerticalAction.actionBiholomorph v (CuspGeometry.inclusion x) =
        CuspGeometry.inclusion x := by
  let := VerticalAction.action
  exact (actionBiholomorph_inclusion_fixed_iff_D₀ u hu hfin x).trans
    (VerticalAction.action_fixed_iff (CuspGeometry.inclusion x)).symm

/-- The same actual criterion with an explicit positive order witness. -/
theorem actionBiholomorph_inclusion_fixed_iff_of_pow_eq_one (u : ℂˣ) (hu : u ≠ 1)
    (n : ℕ) (hn : 0 < n) (hpow : u ^ n = 1) (x : CuspGeometry.LocalSpace) :
    VerticalAction.actionBiholomorph u (CuspGeometry.inclusion x) = CuspGeometry.inclusion x ↔
      CuspGeometry.inclusion x ∈ VerticalAction.D₀ :=
  actionBiholomorph_inclusion_fixed_iff_D₀ u hu
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hpow⟩) x

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FiniteActionFixed.Cusp
