import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusCoordinates

/-!
# The actual base-torus projection of the central cusp fibre

The inverse quarter-turn coordinate modulo the integral lattice is
constant on the exact fibres of the geometric honeycomb collapse.  It
therefore descends to the literal central fibre of the original cusp
quotient.  In particular, the map forgets the compact fibre phase, not a
chosen homology summand.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb PeriodTorusHigherHomology
open CuspHoneycombHexagon.CommonFibres

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

private theorem baseTorusPoint_eq_of_collapse_eq (p q : PhasePlane)
    (h : honeycombCollapseMap C r hr p = honeycombCollapseMap C r hr q) :
    baseTorusPoint p.2 = baseTorusPoint q.2 := by
  obtain ⟨v, hv, _⟩ := (honeycombCollapseMap_eq_iff C r hr p q).mp h
  rw [hv, baseTorusPoint_deck]

/-- The genuine map from the central cusp fibre to its marked base torus. -/
def baseTorusProjection : QuotientCentralFibre C r → ProductTorus 2 :=
  descend (honeycombCollapseMap C r hr) (fun p => baseTorusPoint p.2)
    (honeycombCollapseMap_surjective C r hr)

/-- The projection retains exactly the marked honeycomb base coordinate. -/
@[simp] theorem baseTorusProjection_honeycombCollapseMap (p : PhasePlane) :
    baseTorusProjection C r hr (honeycombCollapseMap C r hr p) =
      baseTorusPoint p.2 :=
  descend_apply _ _ _ (baseTorusPoint_eq_of_collapse_eq C r hr) p

theorem baseTorusProjection_phase_independent
    (u v : CompactFibreTorus) (y : CuspHoneycombTiling.Plane) :
    baseTorusProjection C r hr (honeycombCollapseMap C r hr (u, y)) =
      baseTorusProjection C r hr (honeycombCollapseMap C r hr (v, y)) := by
  rw [baseTorusProjection_honeycombCollapseMap,
    baseTorusProjection_honeycombCollapseMap]

theorem baseTorusProjection_surjective :
    Function.Surjective (baseTorusProjection C r hr) := by
  intro t
  obtain ⟨y, rfl⟩ := baseTorusPoint_surjective t
  exact ⟨honeycombCollapseMap C r hr (1, y),
    baseTorusProjection_honeycombCollapseMap C r hr (1, y)⟩

variable (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hC in
theorem baseTorusProjection_continuous : Continuous (baseTorusProjection C r hr) :=
  descend_continuous _ _ _ (honeycombCollapseMap_isQuotientMap C r hr hC)
    (baseTorusPoint_continuous.comp continuous_snd)
    (baseTorusPoint_eq_of_collapse_eq C r hr)

/-- The continuous base projection in the original quotient topology. -/
def baseTorusProjectionMap : C(QuotientCentralFibre C r, ProductTorus 2) :=
  ⟨baseTorusProjection C r hr, baseTorusProjection_continuous C r hr hC⟩

@[simp] theorem baseTorusProjectionMap_apply (x : QuotientCentralFibre C r) :
    baseTorusProjectionMap C r hr hC x = baseTorusProjection C r hr x := rfl

end Wikipedia.HopfProblem.CuspCentralHomology
