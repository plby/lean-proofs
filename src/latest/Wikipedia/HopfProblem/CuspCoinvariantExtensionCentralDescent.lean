import Wikipedia.HopfProblem.CuspCoinvariantExtensionCentralBasic
import Wikipedia.HopfProblem.CuspControlledRetractionCusp

/-!
# The marked circle coordinate of an actual closed-tube endpoint

Compose the literal quotient endpoint of a lattice-equivariant toric
homotopy with the marked central circle projection.  The representative
formula retains compact fibre-phase invariance whenever the original
homotopy has that invariance.  Central fixed points and prescribed
endpoints are retained exactly, without changing either quotient topology.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension

open ToricSpace CuspRetraction CuspCollapse

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r η : ℝ}
    (hr : 0 < r) (hηr : η < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (H : C(unitInterval × ClosedTube η, ClosedTube η))
    (hH : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η),
      H (s, closedTranslate C η v x) = closedTranslate C η v (H (s, x)))
    (hone : ∀ x : ClosedTube η, time (H (1, x) : Space) = 0)

/-- The native quotient retraction retains every original toric endpoint. -/
theorem centralRetraction_closedQuotientMap (x : ClosedTube η) :
    closedHomotopyDescentRetraction C hηr H hH hC hone (closedQuotientMap C hηr x) =
      centralProject C r hr ⟨(H (1, x) : Space), hone x⟩ := by
  apply Subtype.ext
  change (closedHomotopyDescent C hηr H 1 (closedQuotientMap C hηr x) :
    CuspQuotient.QuotientSpace C r) = _
  rw [closedHomotopyDescent_closedQuotientMap C hηr H hH]
  rfl

/-- The continuous marked circle map on the full actual closed cusp neighborhood. -/
def closedCoreGamma : C(ClosedQuotient C r η, AddCircle (1 : ℝ)) :=
  (centralGamma C r hr hC).comp (closedHomotopyDescentRetraction C hηr H hH hC hone)

/-- Its value is the marked coordinate of the original toric endpoint. -/
theorem closedCoreGamma_closedQuotientMap (x : ClosedTube η) :
    closedCoreGamma C hr hηr hC H hH hone (closedQuotientMap C hηr x) =
      centralGamma C r hr hC (centralProject C r hr ⟨(H (1, x) : Space), hone x⟩) := by
  rw [closedCoreGamma, ContinuousMap.comp_apply, centralRetraction_closedQuotientMap]

/-- The actual central restriction is exactly the original marked central map. -/
theorem closedCoreGamma_comp_central
    (hfix : ∀ (s : unitInterval) (x : ClosedTube η),
      time (x : Space) = 0 → H (s, x) = x) (hη : 0 ≤ η) :
    (closedCoreGamma C hr hηr hC H hH hone).comp
      (quotientCentralIntoClosed C r η hη) = centralGamma C r hr hC := by
  apply ContinuousMap.ext
  intro q
  exact congrArg (centralGamma C r hr hC)
    (ContinuousMap.congr_fun
      (closedHomotopyDescentRetraction_comp_inclusion C hηr H hH hC hfix hone hη) q)

/-- The entire norm-one fibre torus is killed on actual closed quotient representatives. -/
theorem closedCoreGamma_unit_fibreAction
    (hfibre : ∀ (s : unitInterval) (u : Fin 2 → ℂˣ),
      (∀ i, ‖(u i : ℂ)‖ = 1) → ∀ x : ClosedTube η,
        H (s, closedFibreAction η u x) = closedFibreAction η u (H (s, x)))
    (u : Fin 2 → ℂˣ) (hu : ∀ i, ‖(u i : ℂ)‖ = 1) (x : ClosedTube η) :
    closedCoreGamma C hr hηr hC H hH hone
      (closedQuotientMap C hηr (closedFibreAction η u x)) =
        closedCoreGamma C hr hηr hC H hH hone (closedQuotientMap C hηr x) := by
  rw [closedCoreGamma_closedQuotientMap, closedCoreGamma_closedQuotientMap]
  have he : (⟨(H (1, closedFibreAction η u x) : Space),
      hone (closedFibreAction η u x)⟩ : CentralFibre) =
      ⟨torusAction (fibreMultiplier u) (H (1, x) : Space), by
        rw [time_fibreMultiplier, hone]⟩ :=
    Subtype.ext (congrArg (fun z : ClosedTube η => (z : Space)) (hfibre 1 u hu x))
  rw [he]
  exact centralGamma_unit_fibreAction C r hr hC u hu ⟨(H (1, x) : Space), hone x⟩

/-- Any prescribed original endpoint gives the same marked circle value after descent. -/
theorem closedCoreGamma_endpoint (hη : 0 ≤ η) (x : ClosedTube η) (y : CentralFibre)
    (hEnd : H (1, x) = centralIntoClosedTube η hη y) :
    closedCoreGamma C hr hηr hC H hH hone (closedQuotientMap C hηr x) =
      centralGamma C r hr hC (centralProject C r hr y) := by
  rw [closedCoreGamma_closedQuotientMap]
  apply congrArg (fun z : CentralFibre => centralGamma C r hr hC (centralProject C r hr z))
  exact Subtype.ext (congrArg (fun z : ClosedTube η => (z : Space)) hEnd)

end Wikipedia.HopfProblem.CuspCoinvariantExtension
