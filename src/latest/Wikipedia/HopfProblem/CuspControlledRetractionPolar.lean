import Wikipedia.HopfProblem.CuspPositiveRetractionEquivariance
import Wikipedia.HopfProblem.CuspPositiveRetractionPolarProperties
import Wikipedia.HopfProblem.CuspPositiveRetractionStrong
import Wikipedia.HopfProblem.CuspHoneycombHomeomorph

/-!
# Spreading a prescribed positive endpoint through the actual polar quotient

This is the endpoint-transfer step for the controlled retraction. A
supplied positive deformation retains all five of its usual properties
after polar spreading, together with compact-torus equivariance. A
prescribed endpoint on any fixed positive-height shell is preserved
exactly on every genuine polar representative.

No existence of the supplied controlled positive deformation is asserted
here; its construction is separate from this transfer theorem.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspRetraction CuspPositiveRetraction

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
variable (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
variable (hfix : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
  time (q.1 : Space) = 0 → P (s, q) = q)

/-- The actual continuous polar spreading of the supplied positive homotopy. -/
def polarDeformation : C(unitInterval × ClosedTube η, ClosedTube η) :=
  ⟨fun p => polarSpread P p.1 p.2, polarSpread_continuous P hfix⟩

@[simp] theorem polarDeformation_apply (s : unitInterval) (x : ClosedTube η) :
    polarDeformation P hfix (s, x) = polarSpread P s x := rfl

/-- The formula holds for every polar representative, not only a selected one. -/
theorem polarDeformation_closedPolarMap (s : unitInterval) (φ : CompactTorus)
    (q : ClosedPositiveTube η) :
    polarDeformation P hfix (s, closedPolarMap η (φ, q)) =
      closedPolarMap η (φ, P (s, q)) :=
  polarSpread_closedPolarMap P hfix s (φ, q)

/-- All five positive-deformation conditions transfer, with the genuine
compact torus and its fibre subtorus acting equivariantly at every stage. -/
theorem polarDeformation_properties
    (hzero : ∀ q : ClosedPositiveTube η, P (0, q) = q)
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (hequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ClosedPositiveTube η),
      P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
        CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (hmono : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
      ‖time ((P (s, q)).1 : Space)‖ ≤ ‖time (q.1 : Space)‖) :
    (∀ x, polarDeformation P hfix (0, x) = x) ∧
    (∀ s (x : ClosedTube η), time (x : Space) = 0 → polarDeformation P hfix (s, x) = x) ∧
    (∀ x, time (polarDeformation P hfix (1, x) : Space) = 0) ∧
    (∀ s v x, polarDeformation P hfix (s, closedTranslate (fun _ => C₀) η v x) =
      closedTranslate (fun _ => C₀) η v (polarDeformation P hfix (s, x))) ∧
    (∀ s φ x, polarDeformation P hfix (s, closedCompactAction η φ x) =
      closedCompactAction η φ (polarDeformation P hfix (s, x))) ∧
    (∀ s (u : Fin 2 → ℂˣ), (∀ i, ‖(u i : ℂ)‖ = 1) →
      ∀ x, polarDeformation P hfix (s, closedFibreAction η u x) =
        closedFibreAction η u (polarDeformation P hfix (s, x))) ∧
    (∀ s x, ‖time (polarDeformation P hfix (s, x) : Space)‖ ≤ ‖time (x : Space)‖) :=
  ⟨polarSpread_zero P hfix hzero, polarSpread_fixed P hfix,
    polarSpread_one_central P hfix hone, polarSpread_frozen_equivariant C₀ P hfix hequiv,
    polarSpread_compactTorus_equivariant P hfix,
    polarSpread_fibre_torus_equivariant P hfix, polarSpread_norm_time_le P hfix hmono⟩

/-- Exact endpoint transfer on a prescribed height shell. No regularity
of the endpoint expression is assumed: continuity comes from the actual
supplied homotopy and the proved polar quotient. -/
theorem polarDeformation_endpoint (ρ : ℝ) (hη : 0 ≤ η)
    (E : ClosedPositiveTube η → PositiveCentralFibre)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη (E q))
    (φ : CompactTorus) (q : ClosedPositiveTube η) (hq : ‖time (q.1 : Space)‖ = ρ) :
    polarDeformation P hfix (1, closedPolarMap η (φ, q)) =
      closedPolarMap η (φ, positiveCentralInclusion η hη (E q)) := by
  rw [polarDeformation_closedPolarMap, hEnd q hq]

/-- The endpoint formula in the original toric space itself. -/
theorem polarDeformation_endpoint_coe (ρ : ℝ) (hη : 0 ≤ η)
    (E : ClosedPositiveTube η → PositiveCentralFibre)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη (E q))
    (φ : CompactTorus) (q : ClosedPositiveTube η) (hq : ‖time (q.1 : Space)‖ = ρ) :
    (polarDeformation P hfix (1, closedPolarMap η (φ, q)) : Space) =
      compactTorusAction φ ((E q).1 : Space) := by
  rw [polarDeformation_endpoint P hfix ρ hη E hEnd φ q hq]
  rfl

/-- Specialization to the actual honeycomb endpoint. The coordinate
function can in particular be the constructed normalized displacement
coordinate; no coordinate existence is assumed by this transfer lemma. -/
theorem polarDeformation_honeycomb_endpoint (ρ : ℝ) (hη : 0 ≤ η)
    (N : Space → CuspHoneycombTiling.Plane)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀ (N (q.1 : Space))))
    (φ : CompactTorus) (q : ClosedPositiveTube η) (hq : ‖time (q.1 : Space)‖ = ρ) :
    (polarDeformation P hfix (1, closedPolarMap η (φ, q)) : Space) =
      compactTorusAction φ
        ((CuspHoneycomb.honeycombHomeomorph C₀ (N (q.1 : Space))).1 : Space) :=
  polarDeformation_endpoint_coe P hfix ρ hη
    (fun q => CuspHoneycomb.honeycombHomeomorph C₀ (N (q.1 : Space))) hEnd φ q hq

/-- The existing actual central retraction has the same prescribed
endpoint, independently of how its centrality proof is presented. -/
theorem polarRetraction_endpoint_coe
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (ρ : ℝ) (hη : 0 ≤ η) (E : ClosedPositiveTube η → PositiveCentralFibre)
    (hEnd : ∀ q : ClosedPositiveTube η, ‖time (q.1 : Space)‖ = ρ →
      P (1, q) = positiveCentralInclusion η hη (E q))
    (φ : CompactTorus) (q : ClosedPositiveTube η) (hq : ‖time (q.1 : Space)‖ = ρ) :
    (CuspRetraction.polarRetraction P hfix hone (closedPolarMap η (φ, q)) : Space) =
      compactTorusAction φ ((E q).1 : Space) :=
  polarDeformation_endpoint_coe P hfix ρ hη E hEnd φ q hq

end Wikipedia.HopfProblem.CuspControlledRetraction
