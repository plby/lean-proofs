import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedCuspDescent
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedToric
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionCuspSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometryStrata

/-!
# The fixed double curve in the actual cusp quotient

The continuous orbit of a fixed quotient point is constant in its actual
covering fibre. The upstairs vertical fixed locus is exactly the toric
edge-direction-one locus, which descends to the existing double curve of
direction `e₂`. Specialization uses the already constructed cusp correction
and radius and leaves no analytic or smallness hypotheses outstanding.
-/

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCusp

section Generic

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
  (hε : 0 < ε) (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : ToricSpace.SmallDrift C ε)

include hε hε1 hC hR

/-- The common fixed points of the actual cusp flow are precisely the
existing double curve of vertical lattice direction. -/
theorem flow_fixed_iff_doubleCurve (x : CuspQuotient.QuotientSpace C ε) :
    (∀ s : ℂ, Cusp.flow C ε s x = x) ↔
      x ∈ CuspQuotient.doubleCurve C ε hε 1 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  exact (flow_quotientMap_toric_fixed_iff C ε hε hε1 hC hR a).trans
    ((FixedToric.toricFlow_fixed_iff (a : ToricSpace.Space)).trans
      (CuspQuotient.mem_doubleCurve_quotientMap C ε hε a 1).symm)

/-- Equality of the literal cusp fixed set and the existing double curve. -/
theorem flow_fixed_set :
    {x : CuspQuotient.QuotientSpace C ε | ∀ s : ℂ, Cusp.flow C ε s x = x} =
      CuspQuotient.doubleCurve C ε hε 1 := by
  ext x
  exact flow_fixed_iff_doubleCurve C ε hε hε1 hC hR x

/-- A common fixed point in the cusp quotient has central parameter. -/
theorem flow_fixed_projection_eq_zero {x : CuspQuotient.QuotientSpace C ε}
    (hx : ∀ s : ℂ, Cusp.flow C ε s x = x) :
    CuspQuotient.projection C ε x = 0 :=
  CuspQuotient.doubleCurve_subset_central C ε hε 1
    ((flow_fixed_iff_doubleCurve C ε hε hε1 hC hR x).mp hx)

end Generic

/-- The full cusp piece of the constructed threefold has exactly the
actual native double curve of direction `e₂` as its common fixed locus. -/
theorem specialFlow_fixed_iff_doubleCurve (x : CuspGeometry.LocalSpace) :
    (∀ s : ℂ, Cusp.specialFlow s x = x) ↔
      x ∈ CuspQuotient.doubleCurve CuspGeometry.data.correction
        CuspGeometry.data.radius CuspGeometry.data.radius_pos 1 :=
  flow_fixed_iff_doubleCurve CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
    CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift x

/-- The unconditional literal fixed-set equality for the actual cusp data. -/
theorem specialFlow_fixed_set :
    {x : CuspGeometry.LocalSpace | ∀ s : ℂ, Cusp.specialFlow s x = x} =
      CuspQuotient.doubleCurve CuspGeometry.data.correction
        CuspGeometry.data.radius CuspGeometry.data.radius_pos 1 := by
  ext x
  exact specialFlow_fixed_iff_doubleCurve x

/-- The same fixed-point criterion in the existing global double-curve
subset, using the genuine open inclusion of the full cusp patch. -/
theorem specialFlow_fixed_iff_inclusion_mem_doubleCurve (x : CuspGeometry.LocalSpace) :
    (∀ s : ℂ, Cusp.specialFlow s x = x) ↔
      CuspGeometry.inclusion x ∈ CuspGeometry.doubleCurve 1 := by
  rw [specialFlow_fixed_iff_doubleCurve, CuspGeometry.doubleCurve]
  exact (CuspGeometry.inclusion_injective.mem_set_image).symm

/-- No point of the actual noncentral cusp fibres is a common fixed point. -/
theorem specialFlow_fixed_parameter_eq_zero {x : CuspGeometry.LocalSpace}
    (hx : ∀ s : ℂ, Cusp.specialFlow s x = x) : CuspGeometry.parameter x = 0 :=
  flow_fixed_projection_eq_zero CuspGeometry.data.correction CuspGeometry.data.radius
    CuspGeometry.data.radius_pos CuspGeometry.data.radius_lt_one
    CuspGeometry.data.holomorphic CuspGeometry.data.smallDrift hx

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCusp
