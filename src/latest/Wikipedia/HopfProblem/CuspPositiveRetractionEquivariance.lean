import Wikipedia.HopfProblem.CuspPositiveRetractionPhases
import Wikipedia.HopfProblem.CuspRetractionPolarHomotopy
import Wikipedia.HopfProblem.CuspRetractionHomeomorph

/-!
# Equivariance of the polar-spread closed-tube homotopy

The actual frozen lattice action has the phase covariance of Lemma 7.7.
Consequently, spreading a positive-part homotopy that commutes with the
positive lattice action gives a homotopy commuting with the frozen action.
This is a transformation theorem for a supplied homotopy; no existence of
a positive-part deformation is assumed as a conclusion.
-/

noncomputable section

open Set Topology
open scoped Matrix ContinuousMap

namespace Wikipedia.HopfProblem

namespace CuspPositive

open ToricSpace CuspRetraction

/-- Lemma 7.7(i) restricted to the actual closed polar quotient. -/
theorem closedTranslate_closedPolarMap (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (η : ℝ) (v : Fin 2 → ℤ) (u : CompactTorus) (q : ClosedPositiveTube η) :
    closedTranslate (fun _ => C₀) η v (closedPolarMap η (u, q)) =
      closedPolarMap η (phaseTransform C₀ v u, closedPositiveTranslate C₀ η v q) :=
  Subtype.ext (twistedTranslate_constant_polar C₀ v u q.1)

end CuspPositive

namespace CuspRetraction

open ToricSpace CuspPositive

/-- Positive-lattice equivariance descends to frozen-lattice equivariance
of every stage of the genuine polar-spread homotopy. -/
theorem polarSpread_frozen_equivariant (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
    (hfix : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
      time (q.1 : Space) = 0 → P (s, q) = q)
    (hequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ClosedPositiveTube η),
      P (s, closedPositiveTranslate C₀ η v q) =
        closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η) :
    polarSpread P s (closedTranslate (fun _ => C₀) η v x) =
      closedTranslate (fun _ => C₀) η v (polarSpread P s x) := by
  obtain ⟨⟨u, q⟩, rfl⟩ := closedPolarMap_surjective η x
  rw [closedTranslate_closedPolarMap, polarSpread_closedPolarMap P hfix,
    polarSpread_closedPolarMap P hfix, closedTranslate_closedPolarMap, hequiv]

/-- The strong-deformation-retraction package has the same genuine
frozen equivariance when the supplied positive homotopy has its stated
endpoint properties. -/
theorem polarStrongDeformationRetraction_frozen_equivariant
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {η : ℝ}
    (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
    (hfix : ∀ (s : unitInterval) (q : ClosedPositiveTube η),
      time (q.1 : Space) = 0 → P (s, q) = q)
    (hzero : ∀ q : ClosedPositiveTube η, P (0, q) = q)
    (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)
    (hη : 0 ≤ η)
    (hequiv : ∀ (s : unitInterval) (v : Fin 2 → ℤ) (q : ClosedPositiveTube η),
      P (s, closedPositiveTranslate C₀ η v q) =
        closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (x : ClosedTube η) :
    polarStrongDeformationRetraction P hfix hzero hone hη
        (s, closedTranslate (fun _ => C₀) η v x) =
      closedTranslate (fun _ => C₀) η v
        (polarStrongDeformationRetraction P hfix hzero hone hη (s, x)) :=
  polarSpread_frozen_equivariant C₀ P hfix hequiv s v x

end CuspRetraction

end Wikipedia.HopfProblem
