import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorus
import Wikipedia.HopfProblem.CuspCentralHomologyPhaseActionBoundary

/-!
# The phase-invariant marked circle map on the actual central cusp fibre

The first coordinate of the native base-torus projection is a continuous
map to the unit-period additive circle.  It is invariant under the entire
compact fibre torus, including on the collapsed strata.  The same identity
is expressed using arbitrary norm-one complex units and the original
unbundled fibre action used by the closed-tube maps.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open ToricSpace CuspRetraction CuspCollapse CuspHoneycomb CuspCentralHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- The first marked circle coordinate on the literal central quotient. -/
def centralGamma : C(QuotientCentralFibre C r, AddCircle (1 : ℝ)) :=
  (ContinuousMap.eval (0 : Fin 2)).comp (baseTorusProjectionMap C r hr hC)

@[simp] theorem centralGamma_apply (x : QuotientCentralFibre C r) :
    centralGamma C r hr hC x = baseTorusProjection C r hr x 0 := rfl

/-- The actual compact phase action leaves the entire marked circle map unchanged. -/
@[simp] theorem centralGamma_centralPhaseAction (u : CompactFibreTorus)
    (x : QuotientCentralFibre C r) :
    centralGamma C r hr hC (centralPhaseAction C r hr u x) = centralGamma C r hr hC x := by
  obtain ⟨p, rfl⟩ := honeycombCollapseMap_surjective C r hr x
  simp only [centralGamma_apply, centralPhaseAction_honeycombCollapseMap,
    baseTorusProjection_honeycombCollapseMap]

/-- Phase invariance on the original toric central representatives. -/
theorem centralGamma_compactFibreAction (u : CompactFibreTorus) (x : CentralFibre) :
    centralGamma C r hr hC (centralProject C r hr
      ⟨compactFibreAction u (x : Space), by rw [time_compactFibreAction, x.2]⟩) =
        centralGamma C r hr hC (centralProject C r hr x) := by
  rw [← centralPhaseAction_project, centralGamma_centralPhaseAction]

/-- The same invariance in the literal norm-one-unit action used on closed tubes. -/
theorem centralGamma_unit_fibreAction (u : Fin 2 → ℂˣ)
    (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : CentralFibre) :
    centralGamma C r hr hC (centralProject C r hr
      ⟨torusAction (fibreMultiplier u) (x : Space), by rw [time_fibreMultiplier, x.2]⟩) =
        centralGamma C r hr hC (centralProject C r hr x) := by
  let v : CompactFibreTorus := fun i =>
    ⟨(u i : ℂ), mem_sphere_zero_iff_norm.mpr (hu i)⟩
  have hv : compactFibreUnits v = u := by
    funext i
    apply Units.ext
    rfl
  simpa only [compactFibreAction, hv] using centralGamma_compactFibreAction C r hr hC v x

end Wikipedia.HopfProblem.CuspCoinvariantExtension
